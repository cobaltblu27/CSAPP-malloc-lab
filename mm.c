/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
        /* Team name */
        "ateam",
        /* First member's full name */
        "Harry Bovik",
        /* First member's email address */
        "bovik@cs.cmu.edu",
        /* Second member's full name (leave blank if none) */
        "",
        /* Second member's email address (leave blank if none) */
        ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define ISBLACK(p) (*(unsigned int *)(p) & BLACK)

#define ALC 0
#define FREE 1
#define RED 0x0
#define BLACK 0x2

/* makes header and footer from pointer, size and allocation bit */

/***********************
 * Free block structure
 *
 * 32              0
 * -----------------     <- void *p
 * |   size    |a/f| <- stores size of entire block
 * |---------------| __  <- return value; aligned to 8-byte
 * | prev offset   |   |
 * |---------------|
 * | next offset   |  old payload
 * |---------------|
 * |               | __|
 * |---------------|
 * | padding       |
 * |---------------|
 * |   size    |a/f|
 * -----------------
************************/

/*
 * TODO 1) increase util by preventing fragmentation
 * TODO 2) move on to red-black tree
 */

extern int verbose;


void mm_check();

void Exit(int st);

void blkstatus(void *ptr);

typedef struct block {
    unsigned int header;
    unsigned int left[0];
    unsigned int right[0];
} block_t;

static block_t *startblk;
static block_t *lastblk;

//fill in header and footer
static void pack(block_t *blk, size_t size, int alloc);

static inline int header_valid(void *header);

static size_t getsize(block_t *blk);

//return aligned pointer from block ptr
static void *ptr(block_t *blk);

//set left node, set to lastblk if none
static void setleft(block_t *blk, block_t *leftnode);

//set right node, set to lastblk if none
static void setright(block_t *blk, block_t *ptr);

//set parent node
static void setparent(block_t *blk, block_t *ptr);

static block_t *getleft(block_t *blk);

static block_t *getright(block_t *blk);

static block_t *getparent(block_t *blk);

//get adjacent block right after
static block_t *getafter(block_t *blk);

//get adjacent block right before
static block_t *getbefore(block_t *blk);

//check if allocated
static int allocated(block_t *blk);

//check if block is free
static int isfree(block_t *blk);

//returns root which is connected from static block startblk
static block_t *getroot();

//finds the best fit free block for given size, returns lastblk if none
static block_t *bestfit(size_t size);

//remove node
static void rm_node(block_t *target);

/*
 * mm_init - initialize the malloc package.
 */


int mm_init(void) {
    void *p = mem_sbrk(ALIGNMENT * 6 + 4);
    if (p == (void *) -1)
        return -1;

    //prologue block, consists of header, footer and root pointer
    p = p + 4;
    startblk = p;
    pack(p, ALIGNMENT * 3, ALC);

    p = getafter(p);

    //epilogue block, only consists of header and footer
    //epilogue block size is 0
    lastblk = p;
    pack(lastblk, ALIGNMENT * 6, ALC);
    setright(startblk, lastblk);
    setleft(lastblk, NULL);
    setright(lastblk, NULL);
    return 0;
}

/*
 * mm_malloc
 */

void *mm_malloc(size_t size) {
    size_t newsize = ALIGN(size + ALIGNMENT);
    size_t oldsize;
    block_t *p;
    if (newsize < 3 * ALIGNMENT)
        newsize = 3 * ALIGNMENT;
    p = bestfit(newsize);
    if (p == lastblk) {
        block_t *new = mem_sbrk((int) newsize);
        pack(new, newsize, ALC);
        return ptr(new);
    }

    oldsize = getsize(p);
    if (oldsize - newsize < ALIGNMENT * 3) {
        rm_node(p);
        pack(p, oldsize, ALC);
    } else {
        block_t *after;
        block_t *left, *right, *parent;

        left = getleft(p);
        right = getright(p);
        parent = getparent(p);

        pack(p, newsize, ALC);

        after = getafter(p);
        setleft(after, left);
        setright(after, right);
        setparent(after, parent);
    }
    mm_check();
    return ptr(p);
}

/*
 * mm_free
 */
void mm_free(void *ptr) {
    block_t *p;//points to header
    block_t *before, *after;
    block_t *next, *prev;
    size_t blksize;
    p = ptr - 4;
    if (!header_valid(p) || allocated(p) != 0x1) {
        //compare header and footer, return if invalid
        return;
    }
    blksize = getsize(p);

    before = getbefore(p);
    after = getafter(p);

    pack(p, blksize, FREE);

    if (!allocated(before)) {
        blksize += getsize(before);
        pack(before, blksize, FREE);
        p = before;
        if (isfree(after)
            && (unsigned int) after < (unsigned int) mem_heap_hi()) {
            next = getright(after);
            prev = getleft(after);
            pack(p, blksize + getsize(after), FREE);
            setright(prev, next);
            setleft(next, prev);
            setright(prev, next);
            setleft(next, prev);
        }
    } else if (isfree(after)
               && (unsigned int) after < (unsigned int) mem_heap_hi()) {
        next = getright(after);
        prev = getleft(after);
        pack(p, blksize + getsize(after), FREE);

        setright(p, next);
        setleft(next, p);
        setright(prev, p);
        setleft(p, prev);
    } else {
        block_t *first = getright(startblk);
        pack(p, blksize, FREE);
        setright(p, first);
        setleft(first, p);
        setright(startblk, p);
        setleft(p, startblk);
    }
    //mm_check();
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size) {
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = *(size_t *) ((char *) oldptr - SIZE_T_SIZE);
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

void mm_check() {
    void *p = startblk;
    void *heap_end = mem_heap_hi();
    int freeblks = 0, freelistblks = 0;

    //checking heap start to end

    if (verbose)
        printf("mm_check - block headers: ");
    while (p < heap_end) {//check if its end of heap
        if (verbose)
            printf("%p", p);
        //check if p is valid
        if (p < mem_heap_lo() || p > mem_heap_hi() || (long) (p + 4) & 0x7) {
            blkstatus(p);
            Exit(0);
        }

        //check if header is valid
        if (!header_valid(p)) {
            blkstatus(p);
            Exit(0);
        }

        if (isfree(p)) {
            freeblks++;
            if (verbose)
                printf("(f,%x) ", (unsigned int) getsize(p));
        } else if (verbose)
            printf("(a,%x) ", (unsigned int) getsize(p));

        p = getafter(p);
    }
    if (verbose)
        printf("%p(end)\n", heap_end);

    p = getright(startblk);

    //checking free blocks link by link
    while (p != lastblk) {
        freelistblks++;
        if (verbose)
            printf("mm_check: %p %p\n", getright(p), getleft(p));
        if (allocated(getright(p)) || allocated(getleft(p))) {
            if (verbose)
                printf("next: %p, prev: %p\n", getright(p), getleft(p));
            if (getleft(p) != startblk && getright(p) != lastblk) {
                if (verbose)
                    printf("linked free block is not actually free\n");
                Exit(0);
            }
        }
        p = getright(p);
    }

    if (freeblks != freelistblks) {
        if (verbose)
            printf("free blocks: %d, free blocks in list: %d\n", freeblks, freelistblks);
        Exit(0);
    }
    if (verbose)
        printf("mm_check: exiting\n");

}

//returns 1 header p is valid
static inline int header_valid(void *header) {
    return !(*(unsigned int *) header - *(unsigned int *) (header + getsize(header) - 4));
}

void Exit(int st) {
    printf("\n--Exit summary--\nheap area: %p to %p\nheap size: %x\n", mem_heap_lo(), mem_heap_hi(),
           (unsigned int) mem_heapsize());
    mem_deinit();
    exit(st);
}

void blkstatus(void *ptr) {
    if (ptr < mem_heap_lo() || ptr > mem_heap_hi() || !(long) (ptr + 4) & 0x7) {
        printf("blkstatus: pointer invalid, %p\n", ptr);
        return;
    }
    if (!header_valid(ptr)) {
        printf("blkstatus: header invalid, %p\n", ptr);
        return;
    }
    if (allocated(ptr))
        printf("blkstatus: Allocated block %p\n", ptr);
    else
        printf("blkstatus: free block %p, prev: %p next: %p\n", ptr, getleft(ptr), getright(ptr));
    printf("size: %x, before: %p after: %p\n", (unsigned int) getsize(ptr), getbefore(ptr), getafter(ptr));
}

void pack(block_t *blk, size_t size, int alloc) {
    void *ptr = &(blk->header);
    blk->header = (unsigned int) size | alloc;
    ptr = ptr + size - sizeof(ptr);
    *(unsigned int *) ptr = (unsigned int) size | alloc;
}

size_t getsize(block_t *blk) {
    return blk->header & ~0x7;
}

block_t *getbefore(block_t *blk) {
    void *ptr = blk;
    void *footer = ptr - 4;
    ptr = ptr - (*(unsigned int *) footer & ~0x7);
    return ptr;
}

block_t *getafter(block_t *blk) {
    void *ptr = blk;
    ptr = ptr + getsize(blk);
    return ptr;
}

block_t *getleft(block_t *blk) {
    void **ptr = (void **) blk->left;
    return *ptr;
}

block_t *getright(block_t *blk) {
    void **payload = (void **) blk->left;
    payload++;
    return *payload;
}

block_t *getparent(block_t *blk) {
//TODO need to check if valid(it will be correct tho)
    void **payload = (void **) blk->left;
    payload += 2;
    return *payload;
}

void setleft(block_t *blk, block_t *leftnode) {
    block_t **leftptr = (block_t **) blk->left;
    *leftptr = leftnode;

    void **left_parent = (void **) leftnode->left;
    left_parent += 2;
    *left_parent = blk;
}

void setright(block_t *blk, block_t *ptr) {
    void **payload = (void *) blk->left;
    payload++;
    *payload = ptr;
}

void setparent(block_t *blk, block_t *ptr) {
//TODO need to check if valid(it will be correct tho)
    void *payload = blk->left;
    payload = payload + 2 * sizeof(void *);
    *(unsigned int *) payload = (unsigned int) ptr;
}


void *ptr(block_t *blk) {
    return blk->left;
}

int allocated(block_t *blk) {
    return 0 == (blk->header & 0x7);
}

int isfree(block_t *blk) {
    return blk->header & 0x7;
}

block_t *getroot() {
    return getright(startblk);
}

block_t *tree_search(block_t *node, size_t size) {
    size_t blksize = getsize(node);
    if (node == lastblk)
        return node;
    if (blksize < size) {
        return tree_search(getright(node), size);
    } else {
        struct block *left_search;
        left_search = tree_search(getleft(node), size);
        if (left_search == lastblk)
            return node;
        else return left_search;
    }
}

block_t *bestfit(size_t size) {
    block_t *blk = getroot();
    return tree_search(blk, size);
}

void rm_node(block_t *target) {

}



