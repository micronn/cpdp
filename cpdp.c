/* cpdp.c
 * WARNING! BE SURE TO UNDERSTAND WHAT'S GOING ON BEFORE USING THIS CRAP!
 * This is a tool I wrote for my personal use, and one specific use case.
 * I didn't plan to share it, but here it is. Use at your own responsibility.
 * You may find the tool useful, who knows... or best, you could rewrite it :)
 * It may be improved, of course... but have fun with my crappy code :p
 * Copies files, trying to sparse and deduplicate them, and prints copy stats.
 * Deduplication information comes from a database created in previous copies.
 * The tool tries to deduplicate contiguous blocks, to avoid lots of extents.
 * There is missing functionality and it probably needs lots of checks. For
 * example, the database saves file's mtime, which may be used to see if the
 * file is changed and recalculate its blocks, or to deprioritize it when
 * considering the file for deduplication. But by now it does nothing.
 * Note there are no locks nor version control in its grotesque database!
 * @micronn Oct 2021 (oh, yeah, all-code-in-one-file, aaarrrrgghhhh)
 * 
 * To clarify: this tool is for deduplicating large amounts of data which may
 * come from a file, network... with a few files as deduplication source, and
 * not for filesystems with lots of files. Just a few. Performance degrades
 * considerably when the database contains many files. Compile with -O3, and
 * you can also adjust MIN_SIZE_MMAP or have a process that reads the database
 * every few minutes to have it in cache. As I said, this is for a specific
 * use case, but it may work for you too if you know what you're doing.
 * 
 * 20240307: This monstruosity grew a bit, and now is able to use FICLONERANGE
 * which is way faster than FIDEDUPERANGE. But be sure to understand that this
 * is not an atomic deduplication (if the file from which the block is being
 * deduplicated changes while doing the deduplication, it may get the new data
 * and produce a corrupt copy). So, this is only enabled if -c option is
 * specified. You can use -c if you're sure that the source blocks are not
 * being changed while this program is deduplicating.
 * 
 * Now it is also able to punch holes when deduplicating an existing file.
 */

#define _DEFAULT_SOURCE

#ifdef __linux__
	#include <linux/version.h>
	#if LINUX_VERSION_CODE >= KERNEL_VERSION(2, 6, 38)
		#define _GNU_SOURCE
		#define WITH_PUNCH_HOLE
	#endif
#endif

#include <sys/types.h>
#include <sys/stat.h>
#include <sys/mman.h>

#if !defined NODEDUPE
#define WITH_DEDUPE
#ifdef __linux__
	#include <linux/version.h>
	#if LINUX_VERSION_CODE < KERNEL_VERSION(4, 5, 0)
	#error Deduplication only available from kernel 4.5 (use -DNODEDUPE)
	#undef WITH_DEDUPE	/* do not make compiler spit lots of errors */
	#endif
#else
	#error Deduplication only available in linux (use -DNODEDUPE)
	#undef WITH_DEDUPE	/* do not make compiler spit lots of errors */
#endif
#endif

#ifdef WITH_DEDUPE
#include <sys/ioctl.h>
#include <linux/fs.h>
#endif

#include <assert.h>
#include <ctype.h>
#include <endian.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#define XXH_INLINE_ALL
#include "xxhash.h"

/* don't try to dedupe less than 256 KiB */
#define MIN_DEDUPE_BYTES	0x40000

/* don't queue more than 16 MiB */
#define MAX_QUEUED_BYTES	0x1000000

/* will use mmap to read blocks from db when there are > 16 MiB in blocks */
#define MIN_SIZE_MMAP		0x1000000

static int enableclone;

/* the database is just a bunch of 4K-multiple blocks
 * some blocks represent file blocks (hash and block index in file)
 * other blocks are directories which contain entries that represent
 * information about a file, or entries that represent information
 * about blocks (offset in database, block count, availability)
 * the first block in the database must be a directory
 * values in database are stored as little-endian
 */

struct ddir {
	uint64_t next;		/* offset of next ddir */
	uint16_t dt;		/* directory type */
	uint16_t et;		/* total entries */
	uint16_t ef;		/* free entries */
	uint16_t es;		/* entry size */
};

/* adds a new directory of type dt and entry size es to the fd file
 * ldpos must be the offset of one directory, preferibly the last
 * the directories are added at 4k offset boundaries and size multiple 4k
 * pos, if not NULL, will be set to the offset of the new directory
 * d, if not NULL, will be set to the directory header
 * returns -1 on error
 */
int add_ddir(int fd, off_t ldpos, uint16_t dt, uint16_t es,
		off_t *pos, struct ddir *d)
{
	assert(es != 0);
	struct stat st;
	struct ddir dl, dn;
	off_t npos;
	size_t sz, n;
	if (fstat(fd, &st) == -1) return -1;
	if (st.st_size == 0) ldpos = -1;
	else do {
		if (pread(fd, &dl, sizeof dl, ldpos) != sizeof dl) return -1;
		npos = (off_t)le64toh(dl.next);
		if (npos != 0) ldpos = npos;
	} while (npos != 0);
	npos = st.st_size;
	if ((npos & 0xFFF) != 0) npos = (npos + 0x1000) & ~((off_t)0xFFF);
	dl.next = htole64((uint64_t)npos);
	dn.next = 0;
	dn.dt = htole16(dt);
	dn.es = htole16(es);
	sz = 0x1000 - sizeof dn;
	while ((n = sz / es) == 0) sz += 0x1000;
	dn.et = dn.ef = htole16((uint16_t)n);
	sz += sizeof dn;
	if (ftruncate(fd, npos + (off_t)sz) == -1)
		return -1;
	if (pwrite(fd, &dn, sizeof dn, npos) != sizeof dn)
		return -1;
	if (ldpos != -1 && pwrite(fd, &dl, sizeof dl, ldpos) != sizeof dl)
		return -1;
	if (pos != NULL) *pos = npos;
	if (d != NULL) *d = dn;
	return 0;
}

/* directory entry callback
 * this is called for each directory entry in loop_ddir function
 * n will start at 0 and increment by one at each call (after last item, -1)
 * o is the offset of the entry in the file
 * es is the entry size, e is the entry (transient memory), p is param
 * return 0 to continue, another value to end loop and return value
 * when last entry is passed, it will be called with n=-1, o=0, es=0, e=0, p
 * for errors you may return -2 to discriminate callback error
 */
typedef off_t decallback(ssize_t n, off_t o, size_t es, void *e, void *p);

/* loops directory entries in fd and calls f for each entry that corresponds
 * to the specified dt type, while f returns 0
 * if end of entries is reached (but some processed), calls f with n=-1
 * pos is the start directory offset
 * f is the callback and p is a user parameter
 * returns 0 if no entries, the callback return value, or -1 on error
 */
off_t loop_ddir(int fd, off_t pos, uint16_t dt, decallback f, void *p)
{
	struct stat st;
	struct ddir *dp;
	char *buf = NULL;
	off_t r, npos, eo;
	size_t sz, es;
	ssize_t n;
	int ec;
	if (fstat(fd, &st) == -1) return -1;
	if (st.st_size == 0)
		return 0;
	n = 0;
	do {
		sz = 0x1000;
rdbig:
		buf = realloc(buf, sz);
		if (buf == NULL || pread(fd, buf, sz, pos) != (ssize_t)sz) {
			r = -1;
			goto end;
		}
		dp = (struct ddir *)buf;
		npos = (off_t)le64toh(dp->next);
		ec = le16toh(dp->et) - le16toh(dp->ef);
		if (le16toh(dp->dt) == dt && ec > 0) {
			es = (size_t)le16toh(dp->es);
			if (es > sz) {
				assert(ec == 1);
				sz = es + sizeof *dp;
				goto rdbig;
			}
			eo = (off_t)sizeof *dp;
			while (ec--) {
				r = f(n++, pos + eo, es, buf + eo, p);
				if (r != 0)
					goto end;
				eo += (off_t)es;
			}
		}
		pos = npos;
	} while (npos != 0);
	if (n == 0)
		return 0;
	r = f(-1, 0, 0, NULL, p);
end:
	free(buf);
	return r;
}

/* adds a directory entry of type dt to fd file
 * pos is the position of a directory, preferibly the last
 * es is the size of the directory entry and e is the entry
 * it will add a new directory if no space for entry is found
 * return -1 on error
 */
int add_dentry(int fd, off_t pos, uint16_t dt, uint16_t es, void *e)
{
	assert(es != 0);
	struct stat st;
	struct ddir d;
	off_t npos, eo;
	int ec;
	if (fstat(fd, &st) == -1) return -1;
	if (st.st_size == 0) {
		eo = 0;
		pos = 0;
	} else {
		do {
			if (pread(fd, &d, sizeof d, pos) != sizeof d)
				return -1;
			npos = (off_t)le64toh(d.next);
			if (le16toh(d.dt) == dt 
				&& le16toh(d.ef) != 0
				&& le16toh(d.es) == es) {
				npos = -1;
				break;
			}
			if (npos != 0) pos = npos;
		} while (npos != 0);
		if (npos == 0) eo = 0;
		else {
			ec = (le16toh(d.et) - le16toh(d.ef));
			eo = (ec <= 0) ? 0 : (off_t)sizeof d + es * ec;
		}
	}
	if (!eo) {
		if (add_ddir(fd, pos, dt, es, &pos, &d) == -1) return -1;
		eo = sizeof d;
	}
	if (pwrite(fd, e, es, pos + eo) != es) return -1;
	d.ef--;
	if (pwrite(fd, &d, sizeof d, pos) != sizeof d) return -1;
	return 0;
}

/* adjusts len by incrementing it to a multiple of directory free space, if
 * necessary. This may reduce the number of directories in a database.
 * returns the adjusted len
 */
size_t normalize_dentry_len(size_t len)
{
	if (len == 0) return 0;
	size_t ml = ((0x1000 - sizeof(struct ddir)) / 2);
	/* try multiples of free space in block if sufficient small */
	/* hey, we have fast CPUs now, right? */
	while (len <= ml) {
		if (ml % len == 0) return len;
		len++;
	}
	/* do not touch if more than one in a block is not possible */
	return len;
}

#define DIR_FILE	0x01

struct fentry {
	uint64_t mtime;		/* file mtime */
	uint64_t boff;		/* blocks offset */
	uint32_t bs;		/* block size */
	uint32_t bc;		/* number of blocks */
	char realpath[];	/* file realpath */
};

/* callback to find a fentry in loop_dentry
 * compares realpath to p and returns entry offset when found
 */
static off_t find_fentry_cb(ssize_t n, off_t o, size_t es, void *e, void *p)
{
	struct fentry *fe = e;
	if (n == -1) return 0;
	if (!strncmp(fe->realpath, p, es - sizeof *fe)) return o;
	return 0;
}

/* finds the entry corresponding to realpath in fd and returns its offset
 * or 0 if not found; if pfe != NULL, sets value to NULL if no entry is found
 * or allocates a fentry and sets it value to it when the entry is found
 * returns -1 on error
 */
off_t find_fentry(int fd, const char *realpath, struct fentry **pfe)
{
	assert(realpath != NULL);
	off_t off = loop_ddir(fd, 0,
			DIR_FILE,
			find_fentry_cb, (void *)realpath);
	if (pfe != NULL) {
		if (off != 0 && off != -1) {
			size_t len = sizeof **pfe + strlen(realpath) + 1;
			if ((*pfe = malloc(len)) == NULL) return -1;
			if (pread(fd, *pfe, len, off) != (ssize_t)len) {
				free(*pfe);
				*pfe = NULL;
				return -1;
			}
		} else {
			*pfe = NULL;
		}
	}
	return off;
}

#define DIR_BLOCK	0x02

struct block {
	uint32_t hash;		/* XXH32 hash */
	uint32_t idx;		/* index of block in file */
};

/* uint32_t comparsion function for a, b being 32 bit little endian values
 * returns -1, 0, or 1 depending on a < b, a == b, or a > b
 */
static inline int le32cmp(uint32_t a, uint32_t b)
{
	a = le32toh(a);
	b = le32toh(b);
	return (a > b) - (b > a);
}

/* compares two blocks for qsort */
static int block_compare(const void *a, const void *b)
{
	struct block ba = *((struct block *)a);
	struct block bb = *((struct block *)b);
	int r = le32cmp(ba.hash, bb.hash);
	return (r == 0) ? le32cmp(ba.idx, bb.idx) : r;
}

#ifdef WITH_DEDUPE

/* compares uint32_t hash k with the hash in block b
 */
static int block_search(const void *k, const void *b)
{
	uint32_t hk = *((uint32_t *)k);
	uint32_t h = le32toh(((struct block *)b)->hash);
	return (hk > h) - (h > hk);
}

#endif

struct bentry {
	uint64_t boff;		/* block information offset */
	uint32_t bc;		/* block count */
	uint32_t used;		/* 0 when blocks are not used */
};

/* callback to find a bentry in loop_dentry, unused, and with enough block count
 * p must point to an uint32_t specifying the desired block count
 * returns the offset of the bentry, or 0 if not found
 */
static off_t find_freeblocks_cb(ssize_t n, off_t o, size_t es, void *e, void *p)
{
	(void)es;
	static off_t off = 0;
	static uint32_t min;
	if (n == -1) return off;
	struct bentry *be = e;
	uint32_t want = *((uint32_t *)p);
	uint32_t curr = le32toh(be->bc);
	if (n == 0) {
		off = 0;
		min = UINT32_MAX;
	}
	if (be->used == 0 && curr >= want && curr <= min) {
		off = o;
		min = curr;
	}
	return 0;
}

/* allocates bc blocks in fd and returns their start offset
 * start offset will be multiple of 0x1000 so it could be mmaped
 * returns -1 on error
 * ERANGE if bc = 0
 */
off_t allocate_blocks(int fd, uint32_t bc)
{
	struct stat st;
	struct bentry be;
	off_t off, boff, len;
	if (bc == 0)
		return errno = ERANGE, -1;
find:
	if ((off = loop_ddir(fd, 0, DIR_BLOCK, find_freeblocks_cb, &bc)) == -1)
		return -1;
	if (off != 0) {
		if (pread(fd, &be, sizeof be, off) != sizeof be) return -1;
	} else {
		/* file may not have any directory; add at least one entry */
		be.boff = 0;
		be.bc = htole32(bc);
		be.used = 0;
		if (add_dentry(fd, 0, DIR_BLOCK, sizeof be, &be) == -1)
			return -1;
		goto find;
	}
	/* now we should have at least one dir */
	boff = (off_t)le64toh(be.boff);
	if (boff == 0) {
		/* this means we must allocate the blocks at the end */
		if (fstat(fd, &st) == -1) return -1;
		boff = st.st_size;
		if ((boff & 0xFFF) != 0)
			boff = (boff + 0x1000) & ~((off_t)0xFFF);
		be.boff = htole64((uint64_t)boff);
		len = (off_t)(bc * sizeof(struct block));
		if ((len & 0xFFF) != 0) {
			len = (len + 0x1000) & ~((off_t)0xFFF);
			bc = (uint32_t)(len / (off_t)sizeof(struct block));
			be.bc = htole32(bc);
		}
		if (ftruncate(fd, boff + len) == -1) return -1;
	}
	be.used = htole32(1);
	if (pwrite(fd, &be, sizeof be, off) != sizeof be) return -1;
	return boff;
}

/* callback to find a bentry in loop_dentry that refers to a specific boff
 * p must point to a off_t specifying the boff to find
 * returns the offset of the bentry, or 0 if not found
 */
static off_t find_bentry_cb(ssize_t n, off_t o, size_t es, void *e, void *p)
{
	(void)es;
	struct bentry *be = (struct bentry *)e;
	if (n == -1) return 0;
	off_t boff = (off_t)le64toh(be->boff);
	if (boff == *((off_t *)p)) return o;
	return 0;
}

/* marks blocks allocated at offset boff in fd as not used
 * returns -1 on error, 0 if no blocks were allocated, 1 when blocks released
 */
int release_blocks(int fd, off_t boff)
{
	struct bentry be;
	off_t off = loop_ddir(fd, 0, DIR_BLOCK, find_bentry_cb, &boff);
	if (off == -1) return -1;
	if (off == 0) return 0;
	if (pread(fd, &be, sizeof be, off) != sizeof be) return -1;
	be.used = 0;
	if (pwrite(fd, &be, sizeof be, off) != sizeof be) return -1;
	return 1;
}

struct copy_dbfiles_stat
{
	int srcdfd;
	int dstdfd;
	char buf[4096];
};

/* callback to copy non-deleted dbfiles from db in loop_dentry
 */
static off_t copy_dbfiles_cb(ssize_t n, off_t o, size_t es, void *e, void *p)
{
	(void)o;
	if (n == -1) return 0;
	struct fentry *fe = (struct fentry *)e;
	if (*fe->realpath == 0 || fe->bc == 0) return 0;
	struct copy_dbfiles_stat *s = (struct copy_dbfiles_stat *)p;
	uint32_t bc = le32toh(fe->bc);
	off_t srcboff = (off_t)le64toh(fe->boff);
	off_t dstboff = allocate_blocks(s->dstdfd, bc);
	if (dstboff == -1) {
		perror("allocating blocks");
		return -1;
	}
	struct fentry *nfe = malloc(es);
	if (nfe == NULL) {
		perror("creating new file entry");
		return -1;
	}
	memcpy(nfe, fe, es);
	nfe->boff = htole64((uint64_t)dstboff);
	ssize_t rb, wb;
	size_t tb, nb;
	tb = bc * sizeof(struct block);
	fprintf(stderr, "%s\n", nfe->realpath);
	while (tb != 0) {
		nb = (tb > sizeof s->buf) ? sizeof s->buf : tb;
		if ((rb = pread(s->srcdfd, s->buf, nb, srcboff)) == -1) {
			perror("reading blocks");
			return free(nfe), -1;
		}
		if ((wb = pwrite(s->dstdfd, s->buf,
			(size_t)rb, dstboff)) == -1) {
			perror("writing blocks");
			return free(nfe), -1;
		}
		srcboff += wb;
		dstboff += wb;
		tb -= (size_t)wb;
	}
	if (add_dentry(s->dstdfd, 0, DIR_FILE, (uint16_t)es, nfe) == -1) {
		perror("adding file entry");
		return free(nfe), -1;
	}
	return 0;
}

/* creates a new file with the name specified in dst and writes there the
 * data about non-deleted files from dfd database
 * returns -1 on error
 */
int copy_dbfiles(int dfd, const char *dst)
{
	struct copy_dbfiles_stat s;
	s.srcdfd = dfd;
	s.dstdfd = open(dst, O_CREAT | O_EXCL | O_TRUNC | O_RDWR, 0666);
	if (s.dstdfd == -1) {
		perror("opening destination database file");
		return -1;
	}
	if (loop_ddir(dfd, 0, DIR_FILE, copy_dbfiles_cb, &s) == -1)
		return -1;
	return close(s.dstdfd);
}

struct file {
	struct file *prev;	/* this is a doubly linked list */
	struct file *next;	/* and will let us rearrange it */
	off_t boff;		/* offset of blocks in database (0 if no) */
	char *realpath;		/* real path of file */
	struct block *blocks;	/* blocks array (NULL if not loaded) */
	size_t bc;		/* block count in blocks array */
	time_t mtime;		/* file mtime */
	blksize_t bs;		/* block size of blocks represented in array */
	int dfd;		/* database file descriptor */
	int fd;			/* file descriptor */
	int valid;		/* 0 by default, <0 not valid, >0 valid */
};

/* initializes a new file with the specified name
 * it will assign the realpath corresponding to the name
 * returns -1 on error
 */
int init_new_file(struct file *f, const char *name)
{
	assert(f != NULL);
	f->prev = f->next = NULL;
	f->realpath = realpath(name, NULL);
	f->boff = 0;
	f->bc = 0;
	f->blocks = NULL;
	f->dfd = f->fd = -1;
	f->valid = 0;
	/* not strictly required, but set some defaults */
	f->mtime = 0;
	f->bs = 0;
	return (f->realpath == NULL) ? -1 : 0;
}

/* loads blocks of f from its database, if necessary
 * if file has blocks assigned not from database, it remains as is
 * returns 1 when blocks available, 0 otherwise, -1 on error
 * ERANGE when too many blocks
 */
int ensure_blocks(struct file *f)
{
	assert(f != NULL);
	void *p;
	uint64_t s;
	if (f->blocks != NULL) return 1;
	if (f->boff == 0 || f->bc == 0) return 0;
	if ((s = (uint64_t)f->bc * sizeof *f->blocks) > SIZE_MAX)
		return errno = ERANGE, -1;
	if (s < MIN_SIZE_MMAP) {
		if ((p = malloc((size_t)s)) == NULL) return -1;
		if (pread(f->dfd, p, (size_t)s, f->boff) != (ssize_t)s)
			return free(p), -1;
	} else {
		p = mmap(NULL, (size_t)s,
			PROT_READ, MAP_PRIVATE, f->dfd, f->boff);
		if (p == MAP_FAILED) return -1;
		madvise(p, (size_t)s, MADV_RANDOM);
	}
	f->blocks = p;
	return 1;
}

/* frees loaded or assigned blocks of f
 * returns -1 on error
 */
int free_blocks(struct file *f)
{
	assert(f != NULL);
	if (f->blocks == NULL) return 0;
	size_t s = f->bc * sizeof *f->blocks;
	if (f->boff != 0 && f->bc != 0 && s >= MIN_SIZE_MMAP) {
		if (munmap(f->blocks, s) == -1) return -1;
	} else {
		free(f->blocks);
	}
	f->blocks = NULL;
	return 1;
}

/* assigns new blocks to the specified file
 * blocks should be allocated with malloc
 * returns -1 on error
 * ERANGE when too many blocks
 * EINVAL when file has loaded blocks from db and trying to assign the
 * same blocks with different block count
 */
int assign_blocks(struct file *f, blksize_t bs, size_t bc, struct block *blocks)
{
	assert(f != NULL);
	if ((uint64_t)bc * sizeof *blocks > SIZE_MAX)
		return errno = ERANGE, -1;
	if (f->blocks != blocks) {
		if (free_blocks(f) == -1) return -1;
	} else if (f->boff != 0 && blocks != NULL && f->bc != bc) {
		errno = EINVAL;
		return -1;
	}
	f->blocks = blocks;
	f->boff = 0;
	f->bs = bs;
	f->bc = bc;
	return 0;
}

/* adds or updates the specified file to its database
 * after updating, file->blocks may point to another place
 * returns -1 on error
 * ERANGE when real path too long, too many blocks, or bs < 0 or too large
 */
int upsert_file(int fd, struct file *f)
{
	assert(f != NULL);
	assert(f->realpath != NULL);
	struct fentry *fe;
	off_t off, boff;
	size_t blen, len;
	int ub;
	len = 0; /* gcc is not smart enough */
	if ((off = find_fentry(fd, f->realpath, &fe)) == -1)
		return -1;
	if (off == 0) {
		len = strlen(f->realpath) + 1 + sizeof *fe;
		len = normalize_dentry_len(len);
		if (len > UINT16_MAX) return errno = ERANGE, -1;
		if ((fe = malloc(len)) == NULL) return -1;
		memset(fe, 0, len);
		strcpy(fe->realpath, f->realpath);
		ub = 1;
	} else {
		ub = f->dfd != fd || f->boff == 0;
	}
	fe->mtime = htole64((uint64_t)f->mtime);
	if (ub) {
		if (f->bc > UINT32_MAX
			|| f->bs < 0 || (uint64_t)f->bs > UINT32_MAX) {
			errno = ERANGE;
			goto errfe;
		}
		if (ensure_blocks(f) == -1)
			goto errfe;
		if (off != 0) {
			if (release_blocks(fd, (off_t)le64toh(fe->boff)) == -1)
				goto errfe;
		}
		fe->bs = htole32((uint32_t)f->bs);
		fe->bc = htole32((uint32_t)f->bc);
		if (f->blocks == NULL || f->bc == 0) {
			boff = 0;
		} else {
			boff = allocate_blocks(fd, (uint32_t)f->bc);
			if (boff == -1) goto errfe;
			blen = f->bc * sizeof *f->blocks;
			if (pwrite(fd, f->blocks, blen, boff) != (ssize_t)blen)
				goto errfe;
		}
		fe->boff = htole64((uint64_t)boff);
	}
	if (off == 0) {
		if (add_dentry(fd, 0, DIR_FILE, (uint16_t)len, fe) == -1)
			goto errfe;
	} else {
		if (pwrite(fd, fe, sizeof *fe, off) != sizeof *fe)
			goto errfe;
	}
	free(fe);
	f->dfd = fd;
	if (ub) {
		if (free_blocks(f) == -1) return -1;
		f->boff = boff;
		if (ensure_blocks(f) == -1) return -1;
	}
	return 0;
errfe:
	free(fe);
	return -1;
}

/* frees the specified file, does nothing if f is NULL
 * returns -1 on error
 */
int free_file(struct file *f)
{
	if (f == NULL) return 0;
	if (f->fd >= 0 && close(f->fd) == -1) return -1;
	if (free_blocks(f) == -1) return -1;
	free(f->realpath);
	free(f);
	return 0;
}

/* callback to print files in loop_dentry
 */
static off_t print_files_cb(ssize_t n, off_t o, size_t es, void *e, void *p)
{
	(void)n;
	(void)o;
	(void)p;
	size_t bc;
	blksize_t bs;
	time_t mtime;
	struct fentry *fe = (struct fentry *)e;
	char buf[30];
	if (fe == NULL || es <= sizeof(*fe)) return 0;
	if (*fe->realpath != 0) {
		bc = (size_t)le32toh(fe->bc);
		bs = (blksize_t)le32toh(fe->bs);
		mtime = (time_t)le64toh(fe->mtime);
		if (!strftime(buf, sizeof(buf), "%Ec", localtime(&mtime))) {
			strcpy(buf, "*");
		}
		printf("%s %3dK %9zu %s\n",
			buf, (int)bs/1024, bc, fe->realpath);
	}
	return 0;
}

/* prints to stdout all file realpaths from fd database
 * returns -1 on error
 */
int print_files(int fd)
{
	return loop_ddir(fd, 0, DIR_FILE, print_files_cb, NULL) != 0 ? -1 : 0;
}

struct floadstat {
	struct file *first;
	struct file *last;
	char *ignorefile;
	int amode;
	int report;
	int dfd;
};

/* callback to load files in loop_dentry
 * p must point to a floadstat that contains load parameters
 */
static off_t load_files_cb(ssize_t n, off_t o, size_t es, void *e, void *p)
{
	(void)o;
	(void)es;
	if (n == -1) return 0;
	char *path;
	struct file *f;
	struct fentry *fe = (struct fentry *)e;
	struct floadstat *s = (struct floadstat *)p;
	if (n == 0) s->first = s->last = NULL;
	if (*fe->realpath == 0) return 0;
	if (s->ignorefile != NULL && !strcmp(s->ignorefile, fe->realpath))
		return 0;
	if ((uint64_t)le32toh(fe->bc) * sizeof(struct block) > SIZE_MAX) {
		if (s->report)
			fprintf(stderr, "%s: too many blocks\n", fe->realpath);
		return 0;
	}
	if (access(fe->realpath, s->amode) == -1) {
		if (s->report)
			perror(fe->realpath);
		return 0;
	}
	if ((path = strdup(fe->realpath)) == NULL) return -1;
	if ((f = malloc(sizeof *f)) == NULL) return free(path), -1;
	if (s->first == NULL) f->prev = NULL, s->first = s->last = f;
	else f->prev = s->last, s->last = s->last->next = f;
	f->next = NULL;
	f->realpath = path;
	f->mtime = (time_t)le64toh(fe->mtime);
	f->boff = (off_t)le64toh(fe->boff);
	f->blocks = NULL;
	f->bc = (size_t)le32toh(fe->bc);
	f->bs = (blksize_t)le32toh(fe->bs);
	f->fd = -1;
	f->dfd = s->dfd;
	f->valid = 0;
	return 0;
}

/* loads the files from fd database that pass access with the specified amode
 * if report != 0, reports access check failures
 * if ignorefile != NULL, ignores the specified file (that must exist)
 * returns the list of files, or NULL when no files
 * you should errno = 0 and check if errno != 0 when NULL returned
 */
struct file *load_files(int fd, int amode, int report, const char *ignorefile)
{
	struct floadstat s;
	s.first = NULL;
	s.amode = amode;
	s.report = report;
	s.dfd = fd;
	if (ignorefile != NULL) {
		if ((s.ignorefile = realpath(ignorefile, NULL)) == NULL)
			return NULL;
	} else s.ignorefile = NULL;
	if (loop_ddir(fd, 0, DIR_FILE, load_files_cb, &s) == -1) {
		while (s.first != NULL) {
			s.last = s.first;
			s.first = s.first->next;
			free_file(s.last);
		}
	}
	if (s.ignorefile != NULL) free(s.ignorefile);
	return s.first;
}

struct xferinfo {
	off_t total;		/* total bytes to transfer, -1 if unknown */
	off_t xfered;		/* total transferred bytes */
	off_t xferlast;		/* total bytes transferred at last update */
	off_t sparsed;		/* total bytes sparsed */
	double xfersec;		/* bytes transferred per second */
	time_t tmstart;		/* time when the transfer started */
	time_t tmlast;		/* time of the last update */
	int dstfd;		/* destination file */
	int nowrite;		/* non-zero to disable write */
#ifdef WITH_DEDUPE
	blksize_t bs;		/* block size */
	off_t deduped;		/* total deduplicated bytes */
	off_t dedup_pending;	/* total bytes pending deduplication */
	off_t dedup_found;	/* total bytes found to deduplicate */
	off_t cloneoff;		/* destination offset for clone operation */
	off_t cloned;		/* total bytes cloned */
	size_t clonemax;	/* max number of bytes for clone */
	size_t clonelen;	/* length to clone */
	char *clonedata;	/* bytes to clone */
	struct file *fdplist;	/* start of the file list for deduplication */
	struct file *fdp;	/* current file from which to deduplicate */
	struct file_clone_range crg;
	struct file_dedupe_range *rg;
	struct file_dedupe_range_info *rgi;
	_Alignas(struct file_dedupe_range)
	char rgbuf[sizeof(struct file_dedupe_range) +
		sizeof(struct file_dedupe_range_info)];
#endif
};

/* initializes a new transfer of total bytes (-1 if unknown)
 * fdp, if not NULL, must point to any element of a file list for files that
 * are available for deduplication
 */
static void init_xfer(struct xferinfo *xi,
		int dstfd, blksize_t bs, off_t total,
		struct file *fdp)
{
	xi->total = total;
	xi->xfered = xi->xferlast = 0;
	xi->sparsed = 0;
	xi->xfersec = 0.0;
	xi->tmstart = xi->tmlast = time(NULL);
	xi->dstfd = dstfd;
	xi->nowrite = 1;
#ifdef WITH_DEDUPE 
	xi->cloneoff = xi->cloned = 0;
	xi->clonemax = xi->clonelen = 0;
	if (enableclone && (xi->clonedata = malloc(MAX_QUEUED_BYTES)) != NULL)
		xi->clonemax = MAX_QUEUED_BYTES;
	else
		xi->clonedata = NULL;
	xi->bs = bs;
	xi->deduped = xi->dedup_pending = xi->dedup_found = 0;
	if (fdp != NULL) while (fdp->prev != NULL) fdp = fdp->prev;
	xi->fdplist = fdp;
	xi->fdp = NULL;
	memset(xi->rgbuf, 0, sizeof xi->rgbuf);
	xi->rg = (struct file_dedupe_range *)xi->rgbuf;
	xi->rgi = &xi->rg->info[0];
	xi->rg->dest_count = 1;
	xi->rgi->dest_fd = dstfd;
#else
	(void)bs;
	(void)fdp;
#endif
}

/* prints transfer statistics to stderr
 * tries to set cursor to the start of line after printing
 */
static inline void print_xferstats(struct xferinfo *xi)
{ 
	const float mb = (float)((off_t)1<<20);
	const float gb = (float)((off_t)1<<30);
	fprintf(stderr, " %.2f", (float)xi->xfered / gb);
	if (xi->total >= 0)
		fprintf(stderr, "/%.2f", (float)xi->total / gb);
#ifdef WITH_PUNCH_HOLE
	fprintf(stderr, " (S %.2f", (float)xi->sparsed / gb);
#else
	fprintf(stderr, " (%c %.2f", xi->nowrite ? 's' : 'S',
		(float)xi->sparsed / gb);
#endif
#ifdef WITH_DEDUPE
	fprintf(stderr, ", D %.2f", (float)xi->deduped / gb);
	fprintf(stderr, ", %c %.2f", xi->clonemax ? 'C' : 'c',
		(float)xi->cloned / gb);
	fprintf(stderr, " d %.2f", (float)xi->dedup_found / gb);
#endif
	fprintf(stderr, ") GB [%.2f MB/s]", (float)xi->xfersec / mb);
	fprintf(stderr, "         \r");
	fflush(stderr);
}

#ifdef WITH_DEDUPE

/* closes the last file in the list (searches forward only)
 * returns -1 on error, 1 if a file was closed, 0 if no file closed
 */
static int close_last_file(struct file *list)
{
	struct file *fc = NULL;
	while (list != NULL) {
		if (list->fd >= 0)
			fc = list;
		list = list->next;
	}
	if (fc != NULL) {
		if (close(fc->fd) == -1) return -1;
		fc->fd = -1;
		return 1;
	}
	return 0;
}

/* validates the specified file by opening it read only, if not already open
 * if file is marked as invalid, it does not try to open it another time
 * if too many files were open, tries to close the last file from list onwards
 * if file couldn't be opened, marks it as invalid and frees its blocks (if db)
 * if file opened fine, marks it as valid (f->valid = 1)
 * returns -1 on error, 0 if file invalid, 1 if file valid
 */
static int validate_file(struct file *f, struct file *list)
{
	assert(f != NULL);
	if (f->valid < 0)
		return 0;
	if (f->fd < 0) {
try_open:
		if ((f->fd = open(f->realpath, O_RDONLY)) == -1) {
			int olderrno = errno;
			if (errno == EMFILE && close_last_file(list) == 1)
				goto try_open;
			if (f->boff != 0) free_blocks(f);
			errno = olderrno;
			f->valid = -1;
			return -1;
		}
	}
	f->valid = 1;
	return 1;
}

/* frees the blocks of the last file from the list onwards, if it came from db
 * returns -1 on error, 1 if blocks freed, 0 if no blocks freed
 */
static int free_last_file_blocks(struct file *list)
{
	struct file *fc = NULL;
	while (list != NULL) {
		if (list->blocks != NULL && list->boff != 0)
			fc = list;
		list = list->next;
	}
	if (fc != NULL) {
		if (free_blocks(fc) == -1) return -1;
		return 1;
	}
	return 0;
}

/* searches files from list onwards, for the specified hash in its valid files
 * it validates files, if necessary
 * if pblk != NULL, sets it to the corresponding block pointer in file->blocks
 * the block *pblk may point to any element in a group of blocks with same hash
 * returns the file, or NULL if not found
 */
static struct file *find_valid_block(struct file *list,
		blksize_t bs, uint32_t hash, struct block **pblk)
{
	struct block *b = NULL;
	struct file *first = list;
	while (list != NULL) {
		if (list->bs != bs || list->valid < 0)
			goto next;
try_ensure:
		if (ensure_blocks(list) == -1) {
			if (errno == ENOMEM
				&& free_last_file_blocks(first) == 1)
				goto try_ensure;
			goto next;
		}
		if (list->blocks == NULL)
			goto next;
		b = bsearch(&hash,
			list->blocks, list->bc, sizeof *list->blocks,
			block_search);
		if (b != NULL) {
			if (!list->valid && validate_file(list, first) != 1)
				b = NULL;
			else
				break;
		}
next:
		list = list->next;
	}
	if (pblk != NULL) *pblk = b;
	return list;
}

enum { CLONED_NONE, CLONED_ALL, CLONED_SOME };

/* verifies if dedupe data matches and perfoms the clone ioctl
 * on some success, returns the corresponding CLONED_* constant
 * returns -1 if ioctl failed
 * note:
 *  if clonelen > dedup_pending it found some dedupe data but not last block
 *  dedup_pending > clonelen should not happen
 */
static inline int perform_clone(struct xferinfo *xi)
{
	struct file_clone_range *crg = &xi->crg;
	struct file_dedupe_range *rg = xi->rg;
	struct file_dedupe_range_info *rgi = xi->rgi;
	off_t os, oc, len;
	ssize_t nr;
	int srcfd = xi->fdp->fd;
	char buf[xi->bs];
	len = (off_t)xi->clonelen;
	if ((__u64)xi->cloneoff != xi->rgi->dest_offset
		|| len < xi->dedup_pending) {
		return CLONED_NONE;
	}
	if (len > xi->dedup_pending) len = xi->dedup_pending;
	oc = nr = 0;
	os = (off_t)xi->rg->src_offset;
	while (oc < len
		&& (nr = pread(srcfd, buf, (size_t)xi->bs, os + oc)) != -1
		&& nr != 0) {
		if (len - oc < nr) nr = len - oc;
		if (memcmp(buf, xi->clonedata + oc, (size_t)nr) != 0) {
			return CLONED_NONE;
		}
		oc += nr;
	}
	if (nr == -1 || oc < len) return CLONED_NONE;
	crg->src_fd = srcfd;
	crg->src_offset = xi->rg->src_offset;
	crg->src_length = (__u64)len;
	crg->dest_offset = (__u64)xi->cloneoff;
	if (ioctl(xi->dstfd, FICLONERANGE, crg) == -1) return -1;
	rg->src_offset += (__u64)len;
	rgi->dest_offset += (__u64)len;
	xi->cloneoff += len;
	xi->dedup_pending -= len;
	xi->cloned += len;
	if (xi->clonelen != (size_t)len) {
		memcpy(xi->clonedata, xi->clonedata + (size_t)len,
			xi->clonelen - (size_t)len);
		xi->clonelen -= (size_t)len;
		return CLONED_SOME;
	}
	xi->clonelen = 0;
	return CLONED_ALL;
}

/* writes pending queued clone data (if transfer nowrite is 0)
 * if at least MIN_DEDUPE_BYTES are pending deduplication, performs the
 * clone or dedupe operation
 * returns -1 if write failed
 */
static int flush_dedupe(struct xferinfo *xi)
{
	assert(xi != NULL);
	struct file_dedupe_range *rg = xi->rg;
	struct file_dedupe_range_info *rgi = xi->rgi;
	int ok = 1, cloned = CLONED_NONE;
	if (ok && xi->fdp == NULL) {
		xi->dedup_pending = 0;
		ok = 0;
	}
	if (ok && xi->dedup_pending < MIN_DEDUPE_BYTES)
		ok = 0;
	if (ok && validate_file(xi->fdp, xi->fdplist) != 1) {
		xi->fdp = NULL;
		xi->dedup_pending = 0;
		ok = 0;
	}
	if (xi->clonelen > 0) {
		if (ok && (cloned = perform_clone(xi)) == -1) {
			/* disable clone functionality if ioctl failure */
			xi->clonemax = 0;
			cloned = CLONED_NONE;
		}
		if (cloned != CLONED_ALL) {
			/* did not clone all, so we need to write rest */
			if (!xi->nowrite && pwrite(xi->dstfd,
				xi->clonedata,
				xi->clonelen,
				xi->cloneoff) != (ssize_t)xi->clonelen) {
				perror("writing data");
				return -1;
			}
			xi->clonelen = 0;
			/* don't try to dedupe */
			ok = 0;
		}
	}
	while (ok && xi->dedup_pending > 0) {
		rg->src_length = (__u64)xi->dedup_pending;
		rg->reserved1 = 0;
		rg->reserved2 = 0;
		rgi->reserved = 0;
		if (ioctl(xi->fdp->fd, FIDEDUPERANGE, rg) == -1) goto end;
		if (rgi->status < 0) goto end;
		if (rgi->status == FILE_DEDUPE_RANGE_DIFFERS) goto end;
		if (rgi->bytes_deduped == 0) goto end;
		xi->deduped += (off_t)rgi->bytes_deduped;
		xi->dedup_pending -= (off_t)rgi->bytes_deduped;
		rg->src_offset += rgi->bytes_deduped;
		rgi->dest_offset += rgi->bytes_deduped;
	}
end:
	if (xi->dedup_pending > 0) {
		rg->src_offset += (__u64)xi->dedup_pending;
		rgi->dest_offset += (__u64)xi->dedup_pending;
	}
	xi->dedup_pending = 0;
	return 0;
}

/* given a sorted blocks array with bc blocks of size bs, a bcur current
 * block, and a pos search position, look for: a block with the same hash
 * as bcur that is at the pos offset, or the first with the same hash after
 * pos, or the smallest with the same hash in blocks array, and set bpos
 * to the found block position
 */
static inline void match_offset(
		struct block *blocks, size_t bc, blksize_t bs,
		struct block *bcur, off_t pos, off_t *bpos)
{
	struct block *borg, *bnext, *bl;
	uint32_t lehash;
	lehash = bcur->hash;
	borg = bcur;
	/* search forward if start position is less or equal than searched */
	bl = blocks + bc;
	do {
		*bpos = (off_t)le32toh(bcur->idx) * bs;
		if (*bpos < pos) bcur++;
		else break;
	} while (bcur < bl && bcur->hash == lehash);
	if (*bpos == pos) return;
	/* still less than searched? look for the smallest offset */
	if (*bpos < pos) pos = 0;
	/* search backward if start position is greater than searched */
	bnext = borg;
	bcur = borg - 1;
	while (bcur >= blocks && bcur->hash == lehash) {
		*bpos = (off_t)le32toh(bcur->idx) * bs;
		if (*bpos > pos) bnext = bcur--;
		else break;
	}
	if (*bpos == pos) return;
	/* not found? try to use a position following searched */
	if (*bpos < pos) {
		*bpos = (off_t)le32toh(bnext->idx) * bs;
	}
}

/* tries to deduplicate the block at offset o, size siz, and specified hash
 * note: it may write pending queued clone data
 * returns 0 if block not found in candidate file list, 1 if found
 * returns -1 if write pending data failed
 */
static int try_dedupe(struct xferinfo *xi, off_t o, blksize_t bs, uint32_t hash)
{
	assert(xi != NULL);
	assert(bs > 0);
	struct file *f;
	struct block *bcur;
	off_t blkoff, curoff, clooff;
	size_t cbs = 0;
	int r = 1;
	char buf[(size_t)bs];
	if (xi->bs != bs)
		return 0;
	if ((f = find_valid_block(xi->fdplist, bs, hash, &bcur)) == NULL)
		return 0;
	xi->dedup_found += bs;
	if (f == xi->fdp) {
		curoff = (off_t)xi->rg->src_offset + xi->dedup_pending;
		match_offset(f->blocks, f->bc, f->bs, bcur, curoff, &blkoff);
		/* add to current dedupe if contiguous block found */
		if ((off_t)xi->rgi->dest_offset + xi->dedup_pending == o
			&& curoff == blkoff) {
			xi->dedup_pending += (off_t)bs;
			return 1;
		}
	} else {
		/* match smallest offset if different file */
		match_offset(f->blocks, f->bc, f->bs, bcur, 0, &blkoff);
	}
	if (xi->dedup_pending > 0) {
		/* don't flush the last clone block: it's this */
		if (xi->clonelen > (size_t)bs) {
			cbs = (size_t)bs;
			xi->clonelen -= cbs;
			clooff = xi->cloneoff + (off_t)xi->clonelen;
			memcpy(buf, xi->clonedata + xi->clonelen, cbs);
		}
		if(flush_dedupe(xi) == -1) r = -1;
		else if(cbs > 0) {
			memcpy(xi->clonedata, buf, cbs);
			xi->clonelen = cbs;
			xi->cloneoff = clooff;
		}
	}
	xi->rg->src_offset = (__u64)blkoff;
	xi->rgi->dest_offset = (__u64)o;
	xi->dedup_pending = (off_t)bs;
	/* set current, and put it at the front of the list */
	xi->fdp = f;
	if (f != xi->fdplist) {
		if (f->prev != NULL) f->prev->next = f->next;
		if (f->next != NULL) f->next->prev = f->prev;
		f->prev = NULL;
		   	f->next = xi->fdplist;
		xi->fdplist->prev = f;
		xi->fdplist = f;
	}
	return r;
}

#endif

/* updates transfer statistics, accumulating xfered bytes to total transferred,
 * calculates transfer rate and prints transfer stats to stderr every few calls.
 * if end != 0, calculates transfer stats and prints them to stderr, with a \n
 * and releases clone buffer
 */
static void update_xfer(struct xferinfo *xi, ssize_t xfered, int end)
{
	static int upd = 0;
	if (xfered == -1) xfered = 0;
	xi->xferlast += (off_t)xfered;
	xi->xfered += (off_t)xfered;
	if ((upd++ & 0x0F) == 0x0F || end) {
		time_t now = time(NULL);
		time_t elapsed = now - xi->tmlast;
		if (elapsed >= 1) {
			xi->xfersec = (double)xi->xferlast / (double)elapsed;
			xi->tmlast = now;
			xi->xferlast = 0;
		}
		print_xferstats(xi);
		if (end) {
#ifdef WITH_DEDUPE
			free(xi->clonedata);
			xi->clonedata = NULL;
#endif
			fprintf(stderr, "\n");
			upd = 0;
		}
	}
}

/* if no deduplication supported, writes the buf with len to xi dest file
 * at the specified offset off if xi nowrite is 0; else, appends to
 * queue clone data the speficied buf with len. Does the clone/write 
 * operation before arriving at clonemax data size, or if the offset is
 * not contiguous
 * returns -1 on error, 0 on success
 */
static int clone_append(struct xferinfo *xi, off_t off, char *buf, size_t len)
{
#ifdef WITH_DEDUPE
	if (xi->clonemax != 0 && len <= xi->clonemax) {
		if (xi->clonelen == 0) xi->cloneoff = off;
		if (xi->clonemax - len < xi->clonelen
			|| xi->cloneoff + (off_t)xi->clonelen != off) {
			if (flush_dedupe(xi) == -1) return -1;
			xi->cloneoff = off;
		}
		memcpy(&xi->clonedata[xi->clonelen], buf, len);
		xi->clonelen += len;
	} else {
		if (xi->clonelen > 0 && flush_dedupe(xi) == -1)
			return -1;
#endif
		if (!xi->nowrite
			&& pwrite(xi->dstfd, buf, len, off) != (ssize_t)len) {
			perror("writing data");
			return -1;
		}
#ifdef WITH_DEDUPE
	}
#endif
	return 0;
}

/* transfers blocks of size bs from srcfd to dstfd
 * or just reads the blocks from srcfd if dstfd == -1
 * it may also deduplicate and punch srcfd if fdp != NULL and dstfd == -1
 * prints transfer statistics to stderr every few blocks
 * total is a hint about the total bytes to transfer (-1 if unknown)
 * if fout != NULL, computed block information will be assigned to fout
 * if fdp != NULL, it must be a list of files from which data should be
 * considered for deduplication. It may point to any element of the list.
 * The list may be rearranged in the process.
 * returns -1 on error
 */
int transfer(int srcfd, int dstfd, off_t total, blksize_t bs,
		struct file *fdp, struct file *fout)
{
	assert(bs > 0);
	struct xferinfo xi;
	struct block blk;
	char buf[bs], *bmem;
	FILE *bf;
	off_t off, splen;
	size_t bfbytes, bflen, z;
	ssize_t nr;
	int r;
	uint32_t idx;
	XXH32_hash_t hash;
	bf = NULL;
	bmem = NULL;
	if (fout != NULL && (bf = open_memstream(&bmem, &bfbytes)) == NULL)
		return -1;
	splen = 0;
	off = 0;
	idx = 0;
	if (dstfd == -1 && fdp != NULL) dstfd = srcfd;
	init_xfer(&xi, dstfd, bs, total, fdp);
	xi.nowrite = dstfd == -1 || dstfd == srcfd;
	while ((nr = read(srcfd, buf, (size_t)bs)) != -1 && nr != 0) {
		for (z = 0; z < (size_t)nr && buf[z] == 0; z++);
		if (z < (size_t)nr) {
			hash = XXH32(buf, (size_t)nr, 0);
			if (dstfd == -1) goto nodedup;
			if (splen != 0) {
				if (xi.nowrite) {
#ifdef WITH_PUNCH_HOLE
					if (fallocate(dstfd,
						FALLOC_FL_KEEP_SIZE
						| FALLOC_FL_PUNCH_HOLE,
						off - splen, splen) != -1)
						xi.sparsed += splen;
#endif
				} else {
					xi.sparsed += splen;
				}
				splen = 0;
			}
			if (clone_append(&xi, off, buf, (size_t)nr) == -1)
				goto err;
#ifdef WITH_DEDUPE
			if (try_dedupe(&xi, off, (blksize_t)nr, hash) == -1)
				goto err;
			/* do not keep lots of queued dedupe data */
			if (xi.dedup_pending >= MAX_QUEUED_BYTES)
				if (flush_dedupe(&xi) == -1) goto err;
#endif
nodedup:
			if (bf != NULL && (size_t)nr == (size_t)bs) {
				blk.idx = htole32(idx);
				blk.hash = htole32((uint32_t)hash);
				if (fwrite(&blk, sizeof blk, 1, bf) != 1) {
					perror("writing block information");
					goto err;
				}
			}
		} else {
			splen += (off_t)nr;
		}
		off += (off_t)nr;
		/* if short read, it should be the last */
		idx++;
		update_xfer(&xi, nr, 0);
	}
	if (nr == -1) {
		perror("reading data");
		goto err;
	} else {
		if (dstfd != -1 ) {
			if (dstfd != srcfd) {
				if (ftruncate(dstfd, xi.xfered) == -1) {
					perror("setting file size");
					goto err;
				}
				xi.sparsed += splen;		
			} else {
#ifdef WITH_PUNCH_HOLE
				if (splen != 0 && fallocate(dstfd,
					FALLOC_FL_KEEP_SIZE
					| FALLOC_FL_PUNCH_HOLE,
					xi.xfered - splen, splen) != -1)
					xi.sparsed += splen;
#endif
			}
		}
#ifdef WITH_DEDUPE
		if (flush_dedupe(&xi) == -1) goto err;
#endif
		update_xfer(&xi, 0, 1);
		if (bf != NULL) {
			if (fclose(bf) != 0) {
				perror("adjusting block information");
				goto err;
			}
			bf = NULL;
			bflen = bfbytes / sizeof blk;
			qsort(bmem, bflen, sizeof blk, block_compare);
			if (assign_blocks(fout, bs, bflen,
				(struct block *)bmem) == -1) {
				perror("assigning blocks");
				goto err;
			}
			/* blocks assigned, so do not free them */
			bmem = NULL;
		}
	}
	r = 0;
	goto end;
err:
	r = -1;
end:
	if (bf != NULL) fclose(bf);
	if (bmem != NULL) free(bmem);
	return r;
}

/* copies src file to dst
 * if dst == NULL, just reads data from src (which must be a regular file)
 * if fdp != NULL, tries to dedupe with the files in fdp list
 * fdp may point to any element of the list, and the list may be
 * rearranged during the copy
 * if fout != NULL, fills it with file information and its blocks
 * returns -1 on error
 */
int copy_file(const char *src, const char *dst,
		struct file *fdp, struct file *fout,
		blksize_t tbs)
{
	struct stat st;
	off_t total;
	blksize_t bs;
	int srcmode, srcfd, dstfd = -1, r;
	mode_t mode;
	/* source is read only unless trying to deduplicate the existing file */
	srcmode = (dst == NULL && fdp != NULL) ? O_RDWR : O_RDONLY;
	if ((srcfd = open(src, srcmode)) == -1) {
		perror(src);
		goto err;
	}
	if (fstat(srcfd, &st) == -1) {
		perror(src);
		goto err;
	}
	if (S_ISDIR(st.st_mode)) {
		errno = EISDIR;
		perror(src);
		goto err;
	}
	if (S_ISREG(st.st_mode)) {
		mode = st.st_mode;
		total = st.st_size;
		bs = st.st_blksize;
	} else {
		/* non-regular files should not be in the database */
		if (dst == NULL) {
			errno = ENOTSUP;
			perror(src);
			goto err;
		}
		mode = 0666;
		total = -1;
	}
	if (dst != NULL) {
		dstfd = open(dst, O_CREAT | O_EXCL | O_TRUNC | O_WRONLY, mode);
		if (dstfd == -1) {
			perror(dst);
			goto err;
		}
		bs = fstat(dstfd, &st) == -1 ? 4096 : st.st_blksize;
	}
	if (fout != NULL && init_new_file(fout, dst != NULL? dst : src) == -1) {
		perror(dst);
		goto err;
	}
	if (dstfd != -1 && total != -1 && ftruncate(dstfd, total) == -1) {
		perror(dst);
		goto err;
	}
	if (tbs <= 0) tbs = bs;
	r = transfer(srcfd, dstfd, total, tbs, fdp, fout);
	if (fout != NULL) {
		fout->mtime = fstat(dst != NULL ? dstfd : srcfd, &st) == -1
			? time(NULL)
			: st.st_mtime;
	}
	goto end;
err:
	r = -1;
end:
	if (dstfd != -1) close(dstfd);
	if (srcfd != -1) close(srcfd);
	return r;
}

/* releases (deletes) the specified name and its blocks from fd database
 * name must be the real path of the file
 * reports to stderr when the file is not found
 * returns -1 on error, 0 when file not found, 1 when file released
 */
int release_file(int fd, const char *name)
{
	struct fentry *fe;
	assert(name != NULL);
	off_t off;
	int r;
	if ((off = find_fentry(fd, name, &fe)) == -1) return -1;
	if (off != 0) {
		*fe->realpath = 0;
		if (pwrite(fd, fe, sizeof *fe + 1, off) == -1)
			goto errfe;
		if (fe->boff != 0
			&& release_blocks(fd, (off_t)le64toh(fe->boff)) == -1)
			goto errfe;
		r = 1;
	} else {
		fprintf(stderr, "%s: File not found in database.\n", name);
		r = 0;
	}
	goto end;
errfe:
	r = -1;
end:
	free(fe);
	return r;
}

void usage(void)
{
	fprintf(stderr, "syntax: cpdp [-b bs] [-c] [-f db] src dst\n");
	fprintf(stderr, "        cpdp -l -f db\n");
	fprintf(stderr, "        cpdp -P -f db newdb\n");
	fprintf(stderr, "        cpdp [-b bs] (-X | -U [-c] [-d]) -f db file\n");
	fprintf(stderr, " -c  enable clonerange (warning: not atomic!)\n");
	fprintf(stderr, " -b  set block size to bs bytes (KiB if k suffix)\n");
	fprintf(stderr, " -l  list files from db\n");
	fprintf(stderr, " -P  copy files from db to newdb (compact db)\n");
	fprintf(stderr, " -X  delete file from db\n");
	fprintf(stderr, " -U  update or insert file to db\n");
	fprintf(stderr, " -d   also deduplicate file\n");
	exit(EXIT_FAILURE);
}

enum action {
	ACTION_COPY,
	ACTION_COPY_DBFILES = 'P',
	ACTION_LIST = 'l',
	ACTION_DELETE = 'X',
	ACTION_UPDATE = 'U'
};

int main(int argc, char **argv)
{
	struct file fout;
	struct file *files = NULL;
	char *dbfile = NULL, *suffix;
	blksize_t tbs = 0;
	enum action action = ACTION_COPY;
	int dfd, opt, dbmode, dedupupd = 0;
	dfd = 0; /* gcc not smart enough */
	while ((opt = getopt(argc, argv, "cb:lPXUdf:")) != -1) {
		switch (opt) {
		case 'b':
			tbs = (blksize_t)strtoll(optarg, &suffix, 10);
			switch (*suffix) {
				case '\0':
					break;
				case 'K':
				case 'k':
					tbs <<= 10;
					break;
				default:
					tbs = 0;
			}
			if (tbs <= 0) {
				fprintf(stderr,
					"warning: invalid block specification - "
					"default will be used\n");
			}
			break;
		case 'c':
			enableclone = 1;
			break;
		case 'l':
		case 'P':
		case 'X':
		case 'U':
			if (action != ACTION_COPY) usage();
			action = (enum action)opt;
			break;
		case 'd':
			dedupupd = 1;
			break;
		case 'f':
			dbfile = optarg;
			break;
		default:
			usage();
		}
	}
	argc -= optind;
	argv += optind;
	if (dedupupd && action != ACTION_UPDATE) usage();
#ifdef NODEDUPE
	if (dedupupd)
		fprintf(stderr,
			"Warning: compiled with NODEDUPE. Won't dedupe!\n");
#endif
	if (action == ACTION_COPY) {
		if (argc != 2) usage();
	} else if (action != ACTION_LIST) {
		if (argc != 1 || dbfile == NULL) usage();
	} else {
		if (argc != 0 || dbfile == NULL) usage();
	}
	if (dbfile != NULL) {
		dbmode = (action == ACTION_LIST
			|| action == ACTION_COPY_DBFILES)
			? O_RDONLY : O_RDWR | O_CREAT;
		if ((dfd = open(dbfile, dbmode, 0666)) == -1) {
			perror(dbfile);
			return EXIT_FAILURE;
		}
	}
	switch (action) {
		case ACTION_COPY:
			if (dbfile != NULL)
				files = load_files(dfd, R_OK, 1, NULL);
			if (copy_file(argv[0], argv[1], files, &fout, tbs)==-1)
				return EXIT_FAILURE;
			break;
		case ACTION_COPY_DBFILES:
			if (copy_dbfiles(dfd, argv[0]) == -1)
				return EXIT_FAILURE;
			break;
		case ACTION_LIST:
			if (print_files(dfd) == -1) return EXIT_FAILURE;
			break;
		case ACTION_UPDATE:
			if (dedupupd) files = load_files(dfd, R_OK, 1, argv[0]);
			if (copy_file(argv[0], NULL, files, &fout, tbs) == -1)
				return EXIT_FAILURE;
			break;
		case ACTION_DELETE:
			if (release_file(dfd, argv[0]) == -1) {
				perror(dbfile);
				return EXIT_FAILURE;
			}
			break;
		default:
			assert(0 && "invalid action value");
	}
	if (dbfile != NULL) {
		if ((action == ACTION_UPDATE || action == ACTION_COPY)
			&& upsert_file(dfd, &fout) == -1) {
			perror("saving file information to database");
			return EXIT_FAILURE;
		}
		close(dfd);
	}
	return EXIT_SUCCESS;
}
