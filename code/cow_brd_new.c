// SPDX-License-Identifier: GPL-2.0-only
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

#ifndef SECTOR_SHIFT 
#define SECTOR_SHIFT        9

#ifndef PAGE_SECTORS_SHIFT
#define PAGE_SECTORS_SHIFT  (PAGE_SHIFT - SECTOR_SHIFT)
#ifndef PAGE_SECTORS
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
	struct gendisk		*brd_disk;
	struct list_head	brd_list;

    struct brd_device *parent_brd;
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
 * Look up and return a brd's page for a given sector.
 * If one does not exist, allocate an empty page, and insert that. Then
 * return it.
 */
static struct page *brd_insert_page(struct brd_device *brd, sector_t sector)
{
	pgoff_t idx;
	struct page *page;
	gfp_t gfp_flags;

	page = brd_lookup_page(brd, sector);
	if (page)
		return page;

	/*
	 * Must use NOIO because we don't want to recurse back into the
	 * block or filesystem layers from page reclaim.
	 */
	gfp_flags = GFP_NOIO | __GFP_ZERO | __GFP_HIGHMEM;
	page = alloc_page(gfp_flags);
	if (!page)
		return NULL;

	if (radix_tree_preload(GFP_NOIO)) {
		__free_page(page);
		return NULL;
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

    if (brd->parent_brd) {
    parent_page = brd_lookup_page(brd->parent_brd, sector);
    // This page may not have originally existed in the parent.
        if (parent_page) {
        // Map both the parent and snapshot pages so that the kernel can access
        // those addresses. The snapshot page and the parent page both already
        // reside in radix trees, so even when we unmap the pages, the data and
        // the page itself will still remain.
            dst = kmap_atomic(page);
            parent_src = kmap_atomic(parent_page);
            memcpy(dst, parent_src, PAGE_SIZE);
            kunmap_atomic(parent_src);
            kunmap_atomic(dst);
        }
    }

	return page;
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

	copy = min_t(size_t, n, PAGE_SIZE - offset);
	if (!brd_insert_page(brd, sector))
		return -ENOSPC;
	if (copy < n) {
		sector += copy >> SECTOR_SHIFT;
		if (!brd_insert_page(brd, sector))
			return -ENOSPC;
	}
	return 0;
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

    if (copy < n) {
    dst += copy;
    sector += copy >> SECTOR_SHIFT;
    copy = n - copy;
    page = brd_lookup_page(brd, sector);
    if (page) {
      // Present in the new radix tree so this page has been modified.
      src = kmap_atomic(page);
      memcpy(dst, src, copy);
      kunmap_atomic(src);
    } else if (brd->parent_brd &&
        (page = brd_lookup_page(brd->parent_brd, sector))) {
      // Present in the old radix tree so this page has not been modified.
      src = kmap_atomic(page);
      memcpy(dst, src, copy);
      kunmap_atomic(src);
    } else {
      // Page doesn't exist in either radix tree so it must never have been
      // written.
      memset(dst, 0, copy);
    }
  }
}

/*
 * Process a single bvec of a bio.
 */
static int brd_do_bvec(struct brd_device *brd, struct page *page,
			unsigned int len, unsigned int off, unsigned int op,
			sector_t sector)
{
	void *mem;
	int err = 0;

	if (op_is_write(op)) {
		err = copy_to_brd_setup(brd, sector, len);
		if (err)
			goto out;
	}

	mem = kmap_atomic(page);
	if (!op_is_write(op)) {
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
	struct brd_device *brd = bio->bi_bdev->bd_disk->private_data;
	sector_t sector = bio->bi_iter.bi_sector;
	struct bio_vec bvec;
	struct bvec_iter iter;

    rw = BIO_IS_WRITE(bio);

    if ((rw || bio->BI_RW & BIO_DISCARD_FLAG) && !brd->is_writable) {
        goto out_err;
    }

    // MAY BE PROBLEM
    if (unlikely(bio_op(bio) == BIO_DISCARD_FLAG)) {
        err = 0;
        discard_from_brd(brd, sector, bio->bi_iter.bi_size);
        goto out;
    }

	bio_for_each_segment(bvec, bio, iter) {
		unsigned int len = bvec.bv_len;
		int err;

		/* Don't support un-aligned buffer */
		WARN_ON_ONCE((bvec.bv_offset & (SECTOR_SIZE - 1)) ||
				(len & (SECTOR_SIZE - 1)));

		err = brd_do_bvec(brd, bvec.bv_page, len, bvec.bv_offset,
				  bio_op(bio), sector);
		if (err)
			goto io_error;
		sector += len >> SECTOR_SHIFT;
	}

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
	.submit_bio =		brd_submit_bio,
	.rw_page =		brd_rw_page,
    .ioctl =    brd_ioctl,
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
static int part_shift;

module_param(num_disks, int, S_IRUGO);
MODULE_PARM_DESC(num_disks, "Maximum number of brd devices");
module_param(num_snapshots, int, S_IRUGO);
MODULE_PARM_DESC(num_snapshots, "Number of ram block snapshot devices where "
    "each disk gets it's own snapshot");
module_param(disk_size, int, S_IRUGO);
MODULE_PARM_DESC(rd_size, "Size of each RAM disk in kbytes.");

static int max_part;        // MAY BE PROBLEM
module_param(max_part, int, S_IRUGO);
MODULE_PARM_DESC(max_part, "Num Minors to reserve between devices");

MODULE_LICENSE("GPL");
MODULE_ALIAS_BLOCKDEV_MAJOR(RAMDISK_MAJOR);
// MODULE_ALIAS("rd");      // MAY BE PROBLEM

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
 * The device scheme is derived from loop.c. Keep them in synch where possible
 * (should share code eventually).
 */
static LIST_HEAD(brd_devices);
static DEFINE_MUTEX(brd_devices_mutex);
static struct dentry *brd_debugfs_dir;

static int brd_alloc(int i)
{
	struct brd_device *brd;
	struct gendisk *disk;
	char buf[DISK_NAME_LEN];

	mutex_lock(&brd_devices_mutex);
	list_for_each_entry(brd, &brd_devices, brd_list) {
		if (brd->brd_number == i) {
			mutex_unlock(&brd_devices_mutex);
			return -EEXIST;                         // MAY BE PROBLEM - PROBE IN ORIGINAL CRASHMONKEY RETURN BRD
		}
	}
	brd = kzalloc(sizeof(*brd), GFP_KERNEL);
	if (!brd) {
		mutex_unlock(&brd_devices_mutex);
		return -ENOMEM;
	}


	brd->brd_number		= i;
    brd->is_writable  = true;   // True on disks until "snapshot" ioctl is called.
    brd->is_snapshot  = i >= num_disks;




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
	mutex_unlock(&brd_devices_mutex);

	spin_lock_init(&brd->brd_lock);
	INIT_RADIX_TREE(&brd->brd_pages, GFP_ATOMIC);

	snprintf(buf, DISK_NAME_LEN, "ram%d", i);
	if (!IS_ERR_OR_NULL(brd_debugfs_dir))
		debugfs_create_u64(buf, 0444, brd_debugfs_dir,
				&brd->brd_nr_pages);

	disk = brd->brd_disk = blk_alloc_disk(NUMA_NO_NODE);
	if (!disk)
		goto out_free_dev;

	disk->major   = major_num;
    disk->first_minor = i << part_shift;
	disk->minors		= max_part;
	disk->fops		= &brd_fops;
	disk->private_data	= brd;
	disk->flags		|= GENHD_FL_SUPPRESS_PARTITION_INFO;        // MAY BE PROBLEM
    if (brd->is_snapshot) {
        sprintf(disk->disk_name, "cow_ram_snapshot%d_%d", i / num_disks,
            i % num_disks);
    } else {
        sprintf(disk->disk_name, "cow_ram%d", i);
    }
	set_capacity(disk, rd_size * 2);


    blk_queue_max_hw_sectors(disk->queue, 1024);
  	blk_queue_bounce_limit(disk->queue, BLK_BOUNCE_NONE);  // MAY BE PROBLEM
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
	blk_queue_physical_block_size(disk->queue, PAGE_SIZE);   //MAYBE PROBLEM

	/* Tell the block layer that this is not a rotational device */     //MAYBE PROBLEM
	// blk_queue_flag_set(QUEUE_FLAG_NONROT, disk->queue);      
	// blk_queue_flag_clear(QUEUE_FLAG_ADD_RANDOM, disk->queue);
	add_disk(disk);                                 // MAY BE PROBLEM - IN ORIGINAL ADD DISK AT THE END OF INIT

	return 0;

out_free_dev:
	mutex_lock(&brd_devices_mutex);
	list_del(&brd->brd_list);
	mutex_unlock(&brd_devices_mutex);
	kfree(brd);
	return -ENOMEM;
}


static void brd_probe(dev_t dev)
{
	brd_alloc(MINOR(dev) >> part_shift);            // MAY BE PROBLEM
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

/*
static inline void brd_check_and_reset_par(void)
{
	if (unlikely(!max_part))
		max_part = 1;


	if ((1U << MINORBITS) % max_part != 0)
		max_part = 1UL << fls(max_part);

	if (max_part > DISK_MAX_PARTS) {
		pr_info("brd: max_part can't be larger than %d, reset max_part = %d.\n",
			DISK_MAX_PARTS, DISK_MAX_PARTS);
		max_part = DISK_MAX_PARTS;
	}
}  */

static int __init brd_init(void)
{
	struct brd_device *brd, *next;
	int err, i;

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

	major_num = __register_blkdev(major_num, DEVICE_NAME, brd_probe);
	if (major_num <= 0) {
        printk(KERN_WARNING DEVICE_NAME ": unable to get major number\n");
        return -EIO;
    }


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

	brd_debugfs_dir = debugfs_create_dir("ramdisk_pages", NULL);

	for (i = 0; i < nr; i++) {
		err = brd_alloc(i);
		if (err) {
            printk(KERN_WARNING DEVICE_NAME ": err alloc\n");
            goto out_free;
        }

	}

    printk(KERN_WARNING DEVICE_NAME ": brd module loaded\n");
	return 0;

out_free:
    unregister_blkdev(major_num, DEVICE_NAME);
  	debugfs_remove_recursive(brd_debugfs_dir);

	list_for_each_entry_safe(brd, next, &brd_devices, brd_list)
		brd_del_one(brd);

	pr_info("brd: module NOT loaded !!!\n");
	return err;
}

static void __exit brd_exit(void)
{
	struct brd_device *brd, *next;

    unregister_blkdev(major_num, DEVICE_NAME);
	debugfs_remove_recursive(brd_debugfs_dir);

	list_for_each_entry_safe(brd, next, &brd_devices, brd_list)
		brd_del_one(brd);

	pr_info("brd: module unloaded\n");
}

module_init(brd_init);
module_exit(brd_exit);

