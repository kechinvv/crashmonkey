//
// Created by Fábio Domingues on 20/07/17.
//

#ifndef CRASHMONKEY_BIO_ALIAS_H
#define CRASHMONKEY_BIO_ALIAS_H

#include <linux/version.h>

#define BI_RW                   bi_opf
#define BI_DISK                 bi_bdev->bd_disk
#define BI_SIZE                 bi_iter.bi_size
#define BI_SECTOR               bi_iter.bi_sector
#define BIO_ENDIO(bio, err)     bio_endio(bio)
#define BIO_IO_ERR(bio, err)    bio_io_error(bio)
#define BIO_DISCARD_FLAG        REQ_OP_DISCARD
#define BIO_IS_WRITE(bio)       op_is_write(bio_op(bio))


#endif //CRASHMONKEY_BIO_ALIAS_H
