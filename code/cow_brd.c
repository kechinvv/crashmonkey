/*
 * Ram backed block device driver.
 *
 * Copyright (C) 2007 Nick Piggin
 * Copyright (C) 2007 Novell Inc.
 *
 * Parts derived from drivers/block/rd.c, and drivers/block/loop.c, copyright
 * of their respective owners.
 */


#include <linux/init.h>
#include <linux/initrd.h>
#include <linux/module.h>
#include <linux/moduleparam.h>
#include <linux/major.h>
#include <linux/blkdev.h>
#include <linux/bio.h>
#include <linux/highmem.h>
#include <linux/mutex.h>
#include <linux/pagemap.h>
#include <linux/radix-tree.h>
#include <linux/fs.h>
#include <linux/slab.h>
#include <linux/backing-dev.h>
#include <linux/debugfs.h>

#include <linux/uaccess.h>


#include "disk_wrapper_ioctl.h"
#include "bio_alias.h"


#define SECTOR_SHIFT        9
#define PAGE_SECTORS_SHIFT  (PAGE_SHIFT - SECTOR_SHIFT)
#define PAGE_SECTORS        (1 << PAGE_SECTORS_SHIFT)
#define DEFAULT_COW_RD_SIZE 512000
#define DEVICE_NAME         "cow_brd"



/*
 * Each block ramdisk device has a radix_tree brd_pages of pages that stores
 * the pages containing the block device's contents. A brd page's ->index is
 * its offset in PAGE_SIZE units. This is similar to, but in no way connected
 * with, the kernel's pagecache or buffer cache (which sit above our block
 * device).
 */


struct brd_device {
	int			brd_number;
	struct brd_device *parent_brd;
	struct gendisk		*brd_disk;
	struct list_head	brd_list;

	  // Denotes whether or not a cow_ram is writable and snapshots are active.
	  bool  is_writable;
	  bool  is_snapshot;


	/*
	 * Backing store of pages and lock to protect it. This is the contents
	 * of the block device.
	 */
	spinlock_t		brd_lock;
	struct radix_tree_root	brd_pages;
	u64			brd_nr_pages;
};

/*
 * Look up and return a brd's page for a given sector.
 */
static struct page *brd_lookup_page(struct brd_device *brd, sector_t sector)
{
	pgoff_t idx;
	struct page *page;

	/*
	 * The page lifetime is protected by the fact that we have opened the
	 * device node -- brd pages will never be deleted under us, so we
	 * don't need any further locking or refcounting.
	 *
	 * This is strictly true for the radix-tree nodes as well (ie. we
	 * don't actually need the rcu_read_lock()), however that is not a
	 * documented feature of the radix-tree API so it is better to be
	 * safe here (we don't have total exclusion from radix tree updates
	 * here, only deletes).
	 */
	rcu_read_lock();
	idx = sector >> PAGE_SECTORS_SHIFT; /* sector to page index */
	page = radix_tree_lookup(&brd->brd_pages, idx);
	rcu_read_unlock();

	BUG_ON(page && page->index != idx);

	return page;
}

/*
 * Insert a new page for a given sector, if one does not already exist.
 */
static int brd_insert_page(struct brd_device *brd, sector_t sector)
{
	pgoff_t idx;
	struct page *page;
	gfp_t gfp_flags;

	page = brd_lookup_page(brd, sector);
	if (page)
		return 0;

	/*
	 * Must use NOIO because we don't want to recurse back into the
	 * block or filesystem layers from page reclaim.
	 */
	gfp_flags = GFP_NOIO | __GFP_ZERO | __GFP_HIGHMEM;
	page = alloc_page(gfp_flags);
	if (!page)
		return -ENOMEM;

	if (radix_tree_preload(GFP_NOIO)) {
		__free_page(page);
		return -ENOMEM;
	}

	spin_lock(&brd->brd_lock);
	idx = sector >> PAGE_SECTORS_SHIFT;
	page->index = idx;
	if (radix_tree_insert(&brd->brd_pages, idx, page)) {
		__free_page(page);
		page = radix_tree_lookup(&brd->brd_pages, idx);
		BUG_ON(!page);
		BUG_ON(page->index != idx);
	} else {
		brd->brd_nr_pages++;
	}
	spin_unlock(&brd->brd_lock);

	radix_tree_preload_end();
	return 0;
}

static void brd_free_page(struct brd_device *brd, sector_t sector)
{
  struct page *page;
  pgoff_t idx;

  spin_lock(&brd->brd_lock);
  idx = sector >> PAGE_SECTORS_SHIFT;
  page = radix_tree_delete(&brd->brd_pages, idx);
  spin_unlock(&brd->brd_lock);
  if (page)
    __free_page(page);
}

static void brd_zero_page(struct brd_device *brd, sector_t sector)
{
  struct page *page;

  page = brd_lookup_page(brd, sector);
  if (page)
    clear_highpage(page);
}

/*
 * Free all backing store pages and radix tree. This must only be called when
 * there are no other users of the device.
 */
#define FREE_BATCH 16
static void brd_free_pages(struct brd_device *brd)
{
	unsigned long pos = 0;
	struct page *pages[FREE_BATCH];
	int nr_pages;

	do {
		int i;

		nr_pages = radix_tree_gang_lookup(&brd->brd_pages,
				(void **)pages, pos, FREE_BATCH);

		for (i = 0; i < nr_pages; i++) {
			void *ret;

			BUG_ON(pages[i]->index < pos);
			pos = pages[i]->index;
			ret = radix_tree_delete(&brd->brd_pages, pos);
			BUG_ON(!ret || ret != pages[i]);
			__free_page(pages[i]);
		}

		pos++;

		/*
		 * It takes 3.4 seconds to remove 80GiB ramdisk.
		 * So, we need cond_resched to avoid stalling the CPU.
		 */
		cond_resched();

		/*
		 * This assumes radix_tree_gang_lookup always returns as
		 * many pages as possible. If the radix-tree code changes,
		 * so will this have to.
		 */
	} while (nr_pages == FREE_BATCH);
}

/*
 * copy_to_brd_setup must be called before copy_to_brd. It may sleep.
 */
static int copy_to_brd_setup(struct brd_device *brd, sector_t sector, size_t n)
{
	unsigned int offset = (sector & (PAGE_SECTORS-1)) << SECTOR_SHIFT;
	size_t copy;
	int ret;

	copy = min_t(size_t, n, PAGE_SIZE - offset);
	ret = brd_insert_page(brd, sector);
	if (ret)
		return ret;
	if (copy < n) {
		sector += copy >> SECTOR_SHIFT;
		ret = brd_insert_page(brd, sector);
	}
	return ret;
}

static void discard_from_brd(struct brd_device *brd,
      sector_t sector, size_t n)
{
  while (n >= PAGE_SIZE) {
    /*
     * Don't want to actually discard pages here because
     * re-allocating the pages can result in writeback
     * deadlocks under heavy load.
     */
    if (0)
      brd_free_page(brd, sector);
    else
      brd_zero_page(brd, sector);
    sector += PAGE_SIZE >> SECTOR_SHIFT;
    n -= PAGE_SIZE;
  }
}

/*
 * Copy n bytes from src to the brd starting at sector. Does not sleep.
 */
static void copy_to_brd(struct brd_device *brd, const void *src,
			sector_t sector, size_t n)
{
	struct page *page;
	void *dst;
	unsigned int offset = (sector & (PAGE_SECTORS-1)) << SECTOR_SHIFT;
	size_t copy;

	copy = min_t(size_t, n, PAGE_SIZE - offset);
	page = brd_lookup_page(brd, sector);
	BUG_ON(!page);

	dst = kmap_atomic(page);
	memcpy(dst + offset, src, copy);
	kunmap_atomic(dst);

	if (copy < n) {
		src += copy;
		sector += copy >> SECTOR_SHIFT;
		copy = n - copy;
		page = brd_lookup_page(brd, sector);
		BUG_ON(!page);

		dst = kmap_atomic(page);
		memcpy(dst, src, copy);
		kunmap_atomic(dst);
	}
}

/*
 * Copy n bytes to dst from the brd starting at sector. Does not sleep.
 */
static void copy_from_brd(void *dst, struct brd_device *brd,
			sector_t sector, size_t n)
{
	struct page *page;
	void *src;
	unsigned int offset = (sector & (PAGE_SECTORS-1)) << SECTOR_SHIFT;
	size_t copy;

	copy = min_t(size_t, n, PAGE_SIZE - offset);
	page = brd_lookup_page(brd, sector);
	if (page) {
		src = kmap_atomic(page);
		memcpy(dst, src + offset, copy);
		kunmap_atomic(src);
	} else
		memset(dst, 0, copy);

	if (copy < n) {
		dst += copy;
		sector += copy >> SECTOR_SHIFT;
		copy = n - copy;
		page = brd_lookup_page(brd, sector);
		if (page) {
			src = kmap_atomic(page);
			memcpy(dst, src, copy);
			kunmap_atomic(src);
		} else
			memset(dst, 0, copy);
	}
}

/*
 * Process a single bvec of a bio.
 */
static int brd_do_bvec(struct brd_device *brd, struct page *page,
      unsigned int len, unsigned int off, bool is_write,
      sector_t sector)
{
  void *mem;
  int err = 0;

  if (is_write) {
    err = copy_to_brd_setup(brd, sector, len);
    if (err)
      goto out;
  }

  mem = kmap_atomic(page);
  if (!is_write) {
    copy_from_brd(mem + off, brd, sector, len);
    flush_dcache_page(page);
  } else {
    flush_dcache_page(page);
    copy_to_brd(brd, mem + off, sector, len);
  }
  kunmap_atomic(mem);

out:
  return err;
}


static blk_qc_t brd_submit_bio(struct bio *bio)
{	
	  bool rw;
	struct brd_device *brd = bio->bi_bdev->bd_disk->private_data;
	sector_t sector = bio->bi_iter.bi_sector;
	struct bio_vec bvec;
	struct bvec_iter iter;
  int err = -EIO;

  if (bio_end_sector(bio) > get_capacity(bio->bi_bdev->bd_disk)) {
    goto io_error;
  }

  rw = BIO_IS_WRITE(bio);

  if ((rw || bio->BI_RW & BIO_DISCARD_FLAG) && !brd->is_writable) {
    goto io_error;
  }

  if (unlikely(bio_op(bio) == BIO_DISCARD_FLAG)) {
    err = 0;
    discard_from_brd(brd, sector, bio->BI_SIZE);
    goto out;
  }


	bio_for_each_segment(bvec, bio, iter) {
		unsigned int len = bvec.bv_len;

		/* Don't support un-aligned buffer */
		WARN_ON_ONCE((bvec.bv_offset & (SECTOR_SIZE - 1)) ||
				(len & (SECTOR_SIZE - 1)));

		err = brd_do_bvec(brd, bvec.bv_page, len, bvec.bv_offset,
				  bio_op(bio), sector);
		if (err)
			goto io_error;
		sector += len >> SECTOR_SHIFT;
	}

out:
	bio_endio(bio);
	return BLK_QC_T_NONE;
io_error:
	bio_io_error(bio);
	return BLK_QC_T_NONE;
}

#ifdef CONFIG_BLK_DEV_XIP
static int brd_direct_access(struct block_device *bdev, sector_t sector,
      void **kaddr, unsigned long *pfn)
{
  struct brd_device *brd = bdev->bd_disk->private_data;
  struct page *page;

  if (!brd)
    return -ENODEV;
  if (sector & (PAGE_SECTORS-1))
    return -EINVAL;
  if (sector + PAGE_SECTORS > get_capacity(bdev->bd_disk))
    return -ERANGE;
  page = brd_insert_page(brd, sector);
  if (!page)
    return -ENOMEM;
  *kaddr = page_address(page);
  *pfn = page_to_pfn(page);

  return 0;
}
#endif

static int brd_ioctl(struct block_device *bdev, fmode_t mode,
      unsigned int cmd, unsigned long arg)
{
  int error = 0;
  struct brd_device *brd = bdev->bd_disk->private_data;

  switch (cmd) {
    case COW_BRD_SNAPSHOT:
      if (brd->is_snapshot) {
        return -ENOTTY;
      }
      brd->is_writable = false;
      break;
    case COW_BRD_UNSNAPSHOT:
      if (brd->is_snapshot) {
        return -ENOTTY;
      }
      brd->is_writable = true;
      break;
    case COW_BRD_RESTORE_SNAPSHOT:
      if (!brd->is_snapshot) {
        return -ENOTTY;
      }
      brd_free_pages(brd);
      break;
    case COW_BRD_WIPE:
      if (brd->is_snapshot) {
        return -ENOTTY;
      }
      // Assumes no snapshots are being used right now.
      brd_free_pages(brd);
      break;
    default:
      error = -ENOTTY;
  }

  return error;
}

static int brd_rw_page(struct block_device *bdev, sector_t sector,
		       struct page *page, unsigned int op)
{
	struct brd_device *brd = bdev->bd_disk->private_data;
	int err;

	if (PageTransHuge(page))
		return -ENOTSUPP;
	err = brd_do_bvec(brd, page, PAGE_SIZE, 0, op, sector);
	page_endio(page, op_is_write(op), err);
	return err;
}

static const struct block_device_operations brd_fops = {
	.owner =		THIS_MODULE,
  .ioctl = brd_ioctl,
	.submit_bio =		brd_submit_bio,
	.rw_page =		brd_rw_page,
#ifdef CONFIG_BLK_DEV_XIP
  .direct_access =  brd_direct_access,
#endif
};

/*
 * And now the modules code and kernel interface.
 */

int major_num = 0;
static int num_disks = 1;
static int num_snapshots = 1;
int disk_size = DEFAULT_COW_RD_SIZE;

static int rd_nr = CONFIG_BLK_DEV_RAM_COUNT;
module_param(rd_nr, int, 0444);
MODULE_PARM_DESC(rd_nr, "Maximum number of brd devices");

unsigned long rd_size = CONFIG_BLK_DEV_RAM_SIZE;
module_param(rd_size, ulong, 0444);
MODULE_PARM_DESC(rd_size, "Size of each RAM disk in kbytes.");

static int max_part = 1;
static int part_shift;
module_param(max_part, int, 0444);
MODULE_PARM_DESC(max_part, "Num Minors to reserve between devices");

MODULE_LICENSE("GPL");
MODULE_ALIAS_BLOCKDEV_MAJOR(RAMDISK_MAJOR);
MODULE_ALIAS("rd");

module_param(num_disks, int, S_IRUGO);
MODULE_PARM_DESC(num_disks, "Maximum number of ram block devices");
module_param(num_snapshots, int, S_IRUGO);
MODULE_PARM_DESC(num_snapshots, "Number of ram block snapshot devices where "
    "each disk gets it's own snapshot");
module_param(disk_size, int, S_IRUGO);
MODULE_PARM_DESC(disk_size, "Size of each RAM disk in kbytes.");

#ifndef MODULE
/* Legacy boot options - nonmodular */
static int __init ramdisk_size(char *str)
{
	rd_size = simple_strtol(str, NULL, 0);
	return 1;
}
__setup("ramdisk_size=", ramdisk_size);
#endif


/*
#if LINUX_VERSION_CODE >= KERNEL_VERSION(5, 15, 0) && \
    LINUX_VERSION_CODE < KERNEL_VERSION(5, 16, 0)
    struct request_queue* (*blk_alloc_queue)(int) = (struct request_queue* (*)(int)) 0xffffffff87692b50;
#endif
*/

/*
 * The device scheme is derived from loop.c. Keep them in synch where possible
 * (should share code eventually).
 */
static LIST_HEAD(brd_devices);
static DEFINE_MUTEX(brd_devices_mutex);
static struct dentry *brd_debugfs_dir;

static int brd_alloc(int i)
{
	struct brd_device *brd, *parent_brd;
	struct gendisk *disk;
	char buf[DISK_NAME_LEN];
	int err = -ENOMEM;
	printk(KERN_WARNING DEVICE_NAME ": alloc start for brd number %d\n", i);


	mutex_lock(&brd_devices_mutex);

	printk(KERN_WARNING DEVICE_NAME ": mutex_lock(&brd_devices_mutex);");

	list_for_each_entry(brd, &brd_devices, brd_list) {
		printk(KERN_WARNING DEVICE_NAME ": list_for_each_entry");

		if (brd->brd_number == i) {
			printk(KERN_WARNING DEVICE_NAME ": mutex_unlock -EXEXIST brd_number == %d", i);

			mutex_unlock(&brd_devices_mutex);
			printk(KERN_WARNING DEVICE_NAME ": mutex_unlocked");

			return -EEXIST;
		}
	}
	printk(KERN_WARNING DEVICE_NAME ": before kzalloc");

	brd = kzalloc(sizeof(*brd), GFP_KERNEL);
	printk(KERN_WARNING DEVICE_NAME ": after kzalloc");

	if (!brd) {
		printk(KERN_WARNING DEVICE_NAME ": mutex_unlock !brd");
		mutex_unlock(&brd_devices_mutex);
		printk(KERN_WARNING DEVICE_NAME ": mutex_unlocked");
		return -ENOMEM;
	}
	printk(KERN_WARNING DEVICE_NAME ": assigne brd fields");

	brd->brd_number		= i;
	  // True on disks until "snapshot" ioctl is called.
    brd->is_writable  = true;
    brd->is_snapshot  = i >= num_disks;


	printk(KERN_WARNING DEVICE_NAME ": 	list_add_tail(&brd->brd_list, &brd_devices);");
	list_add_tail(&brd->brd_list, &brd_devices);
	printk(KERN_WARNING DEVICE_NAME ": 	unconditional unlock mutex");
	mutex_unlock(&brd_devices_mutex);

	printk(KERN_WARNING DEVICE_NAME ": 	spin_lock_init");
	spin_lock_init(&brd->brd_lock);
	printk(KERN_WARNING DEVICE_NAME ": 	INIT_RADIX_TREE");
	INIT_RADIX_TREE(&brd->brd_pages, GFP_ATOMIC);
	

	printk(KERN_WARNING DEVICE_NAME ": 	blk_alloc_disk %d", 1<<part_shift);
	disk = brd->brd_disk = blk_alloc_disk(1 << part_shift);
	if (!disk) {
		printk(KERN_WARNING DEVICE_NAME ": 	goto out_free_dev;");
		goto out_free_dev;
	}
	
	printk(KERN_WARNING DEVICE_NAME ": 	assign disk fields;");
	disk->major		= major_num;
	disk->first_minor	= 1 << part_shift;
//	disk->minors		= max_part;
	disk->fops		= &brd_fops;
	disk->private_data	= brd;
	// disk->flags		= GENHD_FL_EXT_DEVT;
    disk->flags |= GENHD_FL_SUPPRESS_PARTITION_INFO;

	printk(KERN_WARNING DEVICE_NAME ": 	snprintf;");
	if (brd->is_snapshot) {
		sprintf(disk->disk_name, "cow_ram_snapshot%d_%d", i / num_disks,
			i % num_disks);
	} else {
		sprintf(disk->disk_name, "cow_ram%d", i);
	}
	printk(KERN_WARNING DEVICE_NAME ": 	disk_name %s;", disk->disk_name);


	printk(KERN_WARNING DEVICE_NAME ": 	set_capacity;");
	set_capacity(disk, disk_size * 2);

	if (i >= num_disks) {
		list_for_each_entry(parent_brd, &brd_devices, brd_list) {
			if (parent_brd->brd_number == i % num_disks) {
			brd->parent_brd = parent_brd;
			break;
			}
		}
	} else {
		brd->parent_brd = NULL;
	}
	
    blk_queue_max_hw_sectors(disk->queue, 1024);
  	blk_queue_bounce_limit(disk->queue, BLK_BOUNCE_HIGH);
  	disk->queue->limits.discard_granularity = PAGE_SIZE;
  	blk_queue_max_discard_sectors(disk->queue, UINT_MAX);
	blk_queue_flag_set(QUEUE_FLAG_DISCARD, disk->queue);

	/*
	 * This is so fdisk will align partitions on 4k, because of
	 * direct_access API needing 4k alignment, returning a PFN
	 * (This is only a problem on very small devices <= 4M,
	 *  otherwise fdisk will align on 1M. Regardless this call
	 *  is harmless)
	 */
	printk(KERN_WARNING DEVICE_NAME ": 	blk_queue_physical_block_size;");
	blk_queue_physical_block_size(disk->queue, PAGE_SIZE);

	/* Tell the block layer that this is not a rotational device */
	printk(KERN_WARNING DEVICE_NAME ": 	blk_queue_flag_set; QUEUE_FLAG_NONROT");
	blk_queue_flag_set(QUEUE_FLAG_NONROT, disk->queue);
	printk(KERN_WARNING DEVICE_NAME ": 	blk_queue_flag_clear; QUEUE_FLAG_ADD_RANDOM");
	blk_queue_flag_clear(QUEUE_FLAG_ADD_RANDOM, disk->queue);
	printk(KERN_WARNING DEVICE_NAME ": 	blk_queue_flag_set QUEUE_FLAG_NOWAIT;");
	blk_queue_flag_set(QUEUE_FLAG_NOWAIT, disk->queue);
	printk(KERN_WARNING DEVICE_NAME ": 	add_disk;");
	err = add_disk(disk);
	printk(KERN_INFO DEVICE_NAME " brd alloc error %d", err);

	if (err)
		goto out_cleanup_disk;

	return 0;

out_cleanup_disk:
	printk(KERN_WARNING DEVICE_NAME ": 	inside out_cleanup_disk;");
	blk_cleanup_disk(disk);
	printk(KERN_WARNING DEVICE_NAME ": 	blk_cleanup_disk;");
out_free_dev:
	printk(KERN_WARNING DEVICE_NAME ": 	inside out_free_dev; mutex lock;");
	mutex_lock(&brd_devices_mutex);
	printk(KERN_WARNING DEVICE_NAME ": 	inside list_del;");
	list_del(&brd->brd_list);
	printk(KERN_WARNING DEVICE_NAME ": 	mutex_unlock;");
	mutex_unlock(&brd_devices_mutex);
	printk(KERN_WARNING DEVICE_NAME ": 	kfree;");
	kfree(brd);
	printk(KERN_WARNING DEVICE_NAME ": 	NULL;");
	return -ENOMEM;
}


/*
static struct brd_device *brd_init_one(int i)
{
  struct brd_device *brd, *parent_brd;

  list_for_each_entry(brd, &brd_devices, brd_list) {
    if (brd->brd_number == i) {
      goto out;
    }
  }

  brd = brd_alloc(i);
  if (brd) {
    add_disk(brd->brd_disk);
    list_add_tail(&brd->brd_list, &brd_devices);

    if (i >= num_disks) {
      // Set the parent pointer for this device.
      list_for_each_entry(parent_brd, &brd_devices, brd_list) {
        if (parent_brd->brd_number == i % num_disks) {
          brd->parent_brd = parent_brd;
          break;
        }
      }
    } else {
      brd->parent_brd = NULL;
    }
  }
out:
  return brd;
}
*/
static inline void brd_check_and_reset_par(void)
{
	if (unlikely(!max_part))
		max_part = 1;

	/*
	 * make sure 'max_part' can be divided exactly by (1U << MINORBITS),
	 * otherwise, it is possiable to get same dev_t when adding partitions.
	 */
	if ((1U << MINORBITS) % max_part != 0)
		max_part = 1UL << fls(max_part);

	if (max_part > DISK_MAX_PARTS) {
		pr_info("brd: max_part can't be larger than %d, reset max_part = %d.\n",
			DISK_MAX_PARTS, DISK_MAX_PARTS);
		max_part = DISK_MAX_PARTS;
	}
}

static void brd_probe(dev_t dev)
{
	brd_alloc(MINOR(dev) / max_part);
}

static void brd_del_one(struct brd_device *brd)
{
	del_gendisk(brd->brd_disk);
	blk_cleanup_disk(brd->brd_disk);
	brd_free_pages(brd);
	mutex_lock(&brd_devices_mutex);
	list_del(&brd->brd_list);
	mutex_unlock(&brd_devices_mutex);
	kfree(brd);
}

static int __init brd_init(void)
{
	struct brd_device *brd, *next, *parent_brd;
	int err, i;
	const int nr = num_disks * (1 + num_snapshots);
  	unsigned long range;

	printk(KERN_INFO DEVICE_NAME " init");

	major_num = register_blkdev(major_num, DEVICE_NAME);
	printk(KERN_WARNING DEVICE_NAME ": register_blkdev\n");

	if (major_num <= 0) {
		printk(KERN_WARNING DEVICE_NAME ": unable to get major number\n");
		return -EIO;
	}
	/*
	 * brd module now has a feature to instantiate underlying device
	 * structure on-demand, provided that there is an access dev node.
	 *
	 * (1) if rd_nr is specified, create that many upfront. else
	 *     it defaults to CONFIG_BLK_DEV_RAM_COUNT
	 * (2) User can further extend brd devices by create dev node themselves
	 *     and have kernel automatically instantiate actual device
	 *     on-demand. Example:
	 *		mknod /path/devnod_name b 1 X	# 1 is the rd major
	 *		fdisk -l /path/devnod_name
	 *	If (X / max_part) was not already created it will be created
	 *	dynamically.
	 */


	part_shift = 0;
	if (max_part > 0) {
		part_shift = fls(max_part);

		/*
		* Adjust max_part according to part_shift as it is exported
		* to user space so that user can decide correct minor number
		* if [s]he want to create more devices.
		*
		* Note that -1 is required because partition 0 is reserved
		* for the whole disk.
		*/
		max_part = (1UL << part_shift) - 1;
	}

	if ((1UL << part_shift) > DISK_MAX_PARTS) {
		return -EINVAL;
	}

	if (nr > 1UL << (MINORBITS - part_shift)) {
		return -EINVAL;
	}

	range = nr << part_shift;


	// The first num_disks devices are the actual disks, the rest are snapshot
	// devices.
	for (i = 0; i < nr; i++) {
		printk(KERN_WARNING DEVICE_NAME ": alloc i: %d\n", i);
		err = brd_alloc(i);
		if (err) {
			printk(KERN_WARNING DEVICE_NAME ": err alloc\n");
			goto out_free;
		}
		printk(KERN_WARNING DEVICE_NAME ": alloc done\n");
	}
  	printk(KERN_WARNING DEVICE_NAME ": parent_brd assign\n");


  /* point of no return */
	/*
    list_for_each_entry(brd, &brd_devices, brd_list)
        add_disk(brd->brd_disk);
	*/


	if (__register_blkdev(RAMDISK_MAJOR, DEVICE_NAME, brd_probe))
		return -EIO;

  	printk(KERN_WARNING DEVICE_NAME ": __register_blkdev\n");

	brd_check_and_reset_par();

  	printk(KERN_WARNING DEVICE_NAME ": brd_check_and_reset_par\n");

	brd_debugfs_dir = debugfs_create_dir(DEVICE_NAME"_pages", NULL);

	printk(KERN_WARNING DEVICE_NAME ": debugfs_create_dir\n");


	printk(KERN_INFO DEVICE_NAME ": module loaded with %d disks and %d snapshots"
		"\n", num_disks, num_disks * num_snapshots);

	return 0;

out_free:
	unregister_blkdev(RAMDISK_MAJOR, DEVICE_NAME);
	debugfs_remove_recursive(brd_debugfs_dir);

	list_for_each_entry_safe(brd, next, &brd_devices, brd_list)
		brd_del_one(brd);

	pr_info(DEVICE_NAME": module NOT loaded !!!\n");
	return err;
}

static void __exit brd_exit(void)
{
	struct brd_device *brd, *next;

	unregister_blkdev(RAMDISK_MAJOR, DEVICE_NAME);
	debugfs_remove_recursive(brd_debugfs_dir);

	list_for_each_entry_safe(brd, next, &brd_devices, brd_list)
		brd_del_one(brd);

    printk(KERN_INFO DEVICE_NAME ": module unloaded\n");
}

module_init(brd_init);
module_exit(brd_exit);
