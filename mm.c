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

#define ALLOCATED(p) (*(unsigned int *) (p) & 0x7)
#define ISFREE(p) (0 == (*(unsigned int *) (p) & 0x7))

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* returns size of block from block header or footer */
#define GETSIZE(p) (*(unsigned int *)(p) & ~0x7)


/* pointer to next and previous block, 4-byte offset is added to pointer p */
#define LINKEDPREV(p) ((void *) *(unsigned int *) ((p) + 4))
#define LINKEDNEXT(p) ((void *) *(unsigned int *) ((p) + 8))

#define SETPREV(p, next) (*(unsigned int *)((p) + 4) = (unsigned int) (next))
#define SETNEXT(p, next) (*(unsigned int *)((p) + 8) = (unsigned int) (next))

/* pointer to adjacent blocks, used for coalescing */
#define BEFORE(p) ((p) - GETSIZE((p) - 4))
#define AFTER(p) ((p) + GETSIZE((p)))

/* makes header and footer from pointer, size and allocation bit */
#define PACK(p, size, allocated) {*(unsigned int *)(p) = (size) | (allocated);\
                        *(unsigned int*)((p) + (size) - 4) = (size) | (allocated);}


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

/* TODO 1) get rid of all these sh*tload of bugs
 * TODO 2) increase util by preventing fragmentation
 * TODO 3) move on to red-black tree
 */
static void *startblk;
static void *lastblk;

extern int verbose;

static inline int header_valid(void *header);

void mm_check();

void Exit(int st);

void blkstatus(void *ptr);

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void) {
    void *p = mem_sbrk(ALIGNMENT * 4 + 4);
    if (p == (void *) -1)
        return -1;

    //prologue block, consists of header, footer and root pointer
    p = p + 4;
    startblk = p;
    PACK(p, 16, 1);
    p = AFTER(p);

    //epilogue block, only consists of header and footer
    //epilogue block size is 0
    lastblk = p;
    PACK(p, 16, 1);
    SETNEXT(startblk, lastblk);
    SETPREV(lastblk, startblk);
    SETNEXT(p, NULL);
    return 0;
}

/* 
 * mm_malloc
 */
void *mm_malloc(size_t size) {
//    int newsize = ALIGN(size + SIZE_T_SIZE);
//    void *p = mem_sbrk(newsize);
//    if (p == (void *)-1)
//	return NULL;
//    else {
//        *(size_t *)p = size;
//        return (void *)((char *)p + SIZE_T_SIZE);
//    }
    //TODO error on cccp-bal tracefile, runs out of memory on some other
    int newsize = (int) ALIGN(size + ALIGNMENT);
    int oldsize;
    void *p;
    void *next;
    void *prev;
    p = startblk;// points to first header block
    while (1) {
        //printf("current blksize: 0x%x mmsize: 0x%x\n", GETSIZE(p), newsize);
        p = LINKEDNEXT(p);
        if (ALLOCATED(p) == 1) {
            //epilogue block, empty allocated
            void *new = mem_sbrk(newsize);
            PACK(new, newsize, 1);
            if (verbose)
                printf("allocated %-4x sized block in %p, heap ends in: %p\n", GETSIZE(new), new, mem_heap_hi());
            return new + 4;
        } else if (GETSIZE(p) > newsize)
            break;
    }
    oldsize = GETSIZE(p);
    PACK(p, newsize, 1);
    next = LINKEDNEXT(p);
    prev = LINKEDPREV(p);
    if (GETSIZE(p) - newsize < ALIGNMENT * 2) {
        SETNEXT(LINKEDNEXT(prev), next);
        SETPREV(LINKEDPREV(next), prev);
        //extend block with padding to prevent framentation
        PACK(p, oldsize, 1);
    } else {
        int blksize = GETSIZE(p) - newsize;
        //fragmentation
        p = p + newsize;
        PACK(p, blksize, 0);
        SETNEXT(prev, p);
        SETPREV(next, p);
    }
    if (verbose)
        printf("mm succeed\n");
    mm_check();
    return p + 4;
}

/*
 * mm_free
 */
void mm_free(void *ptr) {
    void *p;//points to header
    void *before, *after;
    void *next, *prev;
    int blksize;
    p = ptr - 4;
    if (!header_valid(p) || ALLOCATED(p) != 0x1) {
        //compare header and footer, return if invalid
        return;
    }
    blksize = GETSIZE(p);
    if (verbose)
        printf("freeing block %p\n", p);

    before = BEFORE(p);
    after = AFTER(p);

    PACK(p, blksize, 0);

    if (ISFREE(before)) {
        blksize += GETSIZE(before);
        PACK(before, blksize, 0);
        p = before;
        if (ISFREE(after) && after < mem_heap_hi()) {
            next = LINKEDNEXT(after);
            prev = LINKEDPREV(after);
            PACK(p, blksize + GETSIZE(after), 0);
            SETNEXT(prev, next);
            SETPREV(next, prev);
            SETNEXT(prev, next);
            SETPREV(next, prev);
        }
    } else if (ISFREE(after) && after < mem_heap_hi()) {
        next = LINKEDNEXT(after);
        prev = LINKEDPREV(after);
        PACK(p, blksize + GETSIZE(after), 0);

        SETNEXT(p, next);
        SETPREV(next, p);
        SETNEXT(prev, p);
        SETPREV(p, prev);
    } else {
        void *first = LINKEDNEXT(startblk);
        PACK(p, blksize, 0);
        SETNEXT(p, first);
        SETPREV(first, p);
        SETNEXT(startblk, p);
        SETPREV(p, startblk);
    }
    mm_check();
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
    while (AFTER(p) < heap_end) {//check if its end of heap
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

        if (ISFREE(p))
            freeblks++;

        p = AFTER(p);
    }

    p = LINKEDNEXT(startblk);

    while (p != lastblk) {
        freelistblks++;
        if (verbose)
            printf("mm_check: %p %p\n", LINKEDNEXT(p), LINKEDPREV(p));
        if (ALLOCATED(LINKEDNEXT(p)) || ALLOCATED(LINKEDPREV(p))) {
            if (verbose)
                printf("next: %p, prev: %p\n", LINKEDNEXT(p), LINKEDPREV(p));
            if (LINKEDPREV(p) != startblk && LINKEDNEXT(p) != lastblk) {
                if (verbose)
                    printf("linked free block is not actually free\n");
                Exit(0);
            }
        }
        p = LINKEDNEXT(p);
    }

    if (freeblks != freelistblks) {
        if (verbose)
            printf("free blocks: %d, free blocks in list: %d\n", freeblks, freelistblks);
        Exit(0);
    }

}

//returns 1 header p is valid
static inline int header_valid(void *header) {
    return !(*(unsigned int *) header - *(unsigned int *) (header + GETSIZE(header) - 4));
}

void Exit(int st) {
    printf("\n--Exit summary--\nheap area: %p to %p\n"
                   "heap size: %x\n", mem_heap_lo(), mem_heap_hi(), (unsigned int) mem_heapsize());
    mem_deinit();
    exit(st);
}

void blkstatus(void *ptr) {
    if (ptr < mem_heap_lo() || ptr > mem_heap_hi() || (long) (ptr + 4) & 0x7) {
        printf("pointer invalid, %p\n", ptr);
        return;
    }
    if (!header_valid(ptr)) {
        printf("header invalid!\n");
        return;
    }
    if (ALLOCATED(ptr))
        printf("Allocated block %p\n", ptr);
    else
        printf("free block %p, prev: %p next: %p\n", ptr, LINKEDPREV(ptr), LINKEDNEXT(ptr));
    printf("size: %x, before: %p after: %p\n", GETSIZE(ptr), BEFORE(ptr), AFTER(ptr));
}