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

#define CHECK 0
#define PRINTBLK 0
/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define PTR(blk) (&((blk)->left))

#define COLOR(p) (*(unsigned int *)(p) & 0x6)

#define SETCOLOR(p, color) {*(unsigned int*)(p) = (*(unsigned int*)(p) & ~0x2) | (color);\
                *(unsigned int *) ((void *) (p) + getsize(p) - 4) = *(unsigned int*) (p);}

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
 * |   size    |a/f| <- stores size of entire block and flags(visited, r/b, a/f)
 * |---------------| __  <- return value; aligned to 8-byte
 * | prev ptr      |   |
 * |---------------|
 * | next ptr      |  old payload
 * |---------------|
 * | parent ptr    | __| <- parent node in tree or previous node in seg-list
 * |---------------|
 * | next ptr      | <- used to point to block with same size(like seg-list)
 * |---------------|
 * | payload       |
 * |---------------|
 * | padding       |
 * |---------------|
 * |   size    |a/f|
 * -----------------
************************/

/*
 * TODO implement realloc
 */

extern int verbose;


void mm_check();

void Exit(int st);

void blkstatus(void *ptr);

typedef struct block {
    unsigned int header;
    struct block *left;
    struct block *right;
    struct block *parent;
    struct block *next;

} block_t;

static block_t *startblk;
static block_t *lastblk;

//fill in header and footer
static inline void pack(block_t *blk, size_t size, int alloc);

static inline int header_valid(void *blk);

static inline size_t getsize(block_t *blk);

//set left node, set to lastblk if none
static inline void setleft(block_t *blk, block_t *leftnode);

//set right node, set to lastblk if none
static inline void setright(block_t *blk, block_t *rightnode);

//set parent node
static inline void setparent(block_t *blk, block_t *parentnode);

static inline void setnext(block_t *blk, block_t *nextnode);

//get adjacent block right after
static inline block_t *getafter(block_t *blk);

//get adjacent block right before
static inline block_t *getbefore(block_t *blk);

//check if allocated
static inline int allocated(block_t *blk);

//check if block is free
static inline int isfree(block_t *blk);

//returns root which is connected from static block startblk
static inline block_t *getroot();

//finds the best fit free block for given size, returns lastblk if none
static block_t *bestfit(size_t size);

//remove node
static void rm_node(block_t *target);

static void insert_node(block_t *node);

static int checkfreetree(block_t *root);

static int checkblackheight(block_t *root);

static void print_tree(block_t *node);

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
    pack(lastblk, ALIGNMENT * 3, ALC | BLACK);
    setright(startblk, lastblk);
    setleft(lastblk, lastblk);
    setright(lastblk, lastblk);
    return 0;
}

/*
 * mm_malloc
 */

void *mm_malloc(size_t size) {
//    printf("malloc %x\n", (unsigned int) size);
    size_t newsize, oldsize;
    if (size < 64 * ALIGNMENT) {//round to nearest power of 2
        size--;
        size |= size >> 1;
        size |= size >> 2;
        size |= size >> 4;
        size |= size >> 8;
        size = size + 1;
    }
    newsize = ALIGN(size + ALIGNMENT);
    block_t *p;
    if (newsize < 3 * ALIGNMENT)
        newsize = 3 * ALIGNMENT;
    p = bestfit(newsize);
    if (p == lastblk) {
        block_t *new_blk = mem_sbrk((int) newsize);
        if(new_blk == (void *)-1){
            printf("sbrk failed!\n");
            Exit(0);
        }
        pack(new_blk, newsize, ALC);
        if (CHECK)
            mm_check();
        return PTR(new_blk);
    }
    oldsize = getsize(p);
    if (oldsize - newsize < ALIGNMENT * 3) {
        rm_node(p);
        pack(p, oldsize, ALC);
    } else {
        rm_node(p);
        block_t *after;
        pack(p, newsize, ALC);

        //split
        after = getafter(p);

        pack(after, oldsize - newsize, FREE);
        insert_node(after);
    }
    if (CHECK)
        mm_check();
    return PTR(p);
}

/*
 * mm_free
 * using red-black tree
 */
void mm_free(void *ptr) {
    block_t *p;//points to header
    block_t *before, *after;
    size_t blksize;
    p = ptr - sizeof(unsigned int);
//    printf("freeing %p (%p, size: %x)\n", ptr, p, (int) getsize(p));
    if (!header_valid(p) || !allocated(p)) {
        //compare header and footer, return if invalid
        return;
    }
    blksize = getsize(p);

    before = getbefore(p);
    after = getafter(p);

    if (isfree(before)) {
        rm_node(before);
        blksize += getsize(before);
        pack(before, blksize, FREE);
        p = before;
        if (isfree(after) && (unsigned int) after < (unsigned int) mem_heap_hi()) {
            rm_node(after);
            pack(p, blksize + getsize(after), FREE);
        }
        insert_node(p);
    } else if (isfree(after) && (unsigned int) after < (unsigned int) mem_heap_hi()) {
        rm_node(after);
        pack(p, blksize + getsize(after), FREE);
        insert_node(p);
    } else {
        pack(p, blksize, FREE);
        insert_node(p);
    }
    if (CHECK)
        mm_check();
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size){
    block_t *oldblk = ptr - sizeof(unsigned int);
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    copySize = getsize(oldblk);
    if (size < copySize)
        copySize = size;
    memcpy(newptr, ptr, copySize);
    mm_free(ptr);
    return newptr;
}

int treesize(block_t *root) {
    if (root == lastblk)
        return 0;
    int freecnt = 1;
    freecnt += treesize(root->left);
    freecnt += treesize(root->right);
    return freecnt;
}

void mm_check() {
    void *p = startblk;
    void *heap_end = mem_heap_hi();
    int freeblks = 0;
    int freelistblks = 0;

    //checking heap start to end

    if (PRINTBLK)
        printf("mm_check - block headers: ");
    while (p < heap_end) {//check if its end of heap
        if (PRINTBLK)
            printf("%p", p);
        //check if p is valid
        if (p < mem_heap_lo() || p > mem_heap_hi() || (long) (p + 4) & 0x7) {
            blkstatus(p);
            Exit(1);
        }

        //check if header is valid
        if (!header_valid(p)) {
            blkstatus(p);
            Exit(1);
        }

        if (isfree(p)) {
            freeblks++;
            if (PRINTBLK)
                printf("(f,%x) ", (unsigned int) getsize(p));
        } else if (PRINTBLK)
            printf("(a,%x) ", (unsigned int) getsize(p));

        p = getafter(p);
    }

    if (PRINTBLK)
        printf("%p(end)\n", heap_end);

    freelistblks = checkfreetree(getroot());
    if (freeblks != freelistblks) {
        printf("free blocks: %d, free blocks in list: %d\n", freeblks, freelistblks);
        Exit(0);
    }

    checkblackheight(getroot());

//    printf("free list size: %d, tree size: %d\n", freeblks, treesize(getroot()));

}

/************************************************************************/

//returns 1 header p is valid
static inline int header_valid(void *blk) {
    return *(unsigned int *) blk == *(unsigned int *) (blk + getsize(blk) - 4);
}

int cntlist(block_t *node) {
    if (node == lastblk)
        return 0;
    else return 1 + cntlist(node->next);
}

int checkfreetree(block_t *root) {
    block_t *left = root->left;
    block_t *right = root->right;
    if (root == lastblk)
        return 0;
    if (isfree(root) != 1) {
        printf("block in tree is not actually free\n");
        Exit(1);
    }
    if (root->header & 0x4) {
        printf("tree connection is messed up\n");
        Exit(1);
    }
    root->header = root->header | 0x4;//flag for checking visited node
    int freecnt = cntlist(root);
    if (COLOR(root) == RED) {
        if (COLOR(left) == RED || COLOR(right) == RED) {
            printf("red child of red node\n");
            Exit(0);
        }
    }
    if (left != lastblk && right != lastblk)
        if (getsize(left) >= getsize(root) || getsize(root) >= getsize(right)) {
            printf("size incorrect\n");
            Exit(1);
        }

    freecnt += checkfreetree(right);
    freecnt += checkfreetree(left);
    root->header = root->header & ~0x4;
    return freecnt;
}

int checkblackheight(block_t *root) {
    if (root == lastblk)
        return 1;
    int l = checkblackheight(root->left);
    int r = checkblackheight(root->right);
    if (l != r) {
        printf("black height incorrect!: %p, left: %d right: %d\n", root, l, r);
        Exit(0);
    }
    if (COLOR(root) == BLACK)
        l++;
    return l;
}

void Exit(int st) {
    printf("\n--Exit summary--\nheap area: %p to %p\nheap size: %x\n", mem_heap_lo(), mem_heap_hi(),
           (unsigned int) mem_heapsize());
    if (st == 0)
        print_tree(getroot());
    mem_deinit();
    exit(st);
}

void blkstatus(void *ptr) {
    printf("\n");
    if (ptr < mem_heap_lo() || ptr > mem_heap_hi() || !((long) (ptr + 4) & 0x7)) {
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
        printf("blkstatus: free block %p, prev: %p next: %p\n", ptr, ((block_t *) ptr)->left, ((block_t *) ptr)->right);
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

void setleft(block_t *blk, block_t *leftnode) {
    blk->left = leftnode;
    leftnode->parent = blk;
}

void setright(block_t *blk, block_t *rightnode) {
    blk->right = rightnode;
    rightnode->parent = blk;
}

void setparent(block_t *blk, block_t *parentnode) {
    blk->parent = parentnode;
    block_t **targetptr;
    if (getsize(blk) >= getsize(parentnode) || parentnode == startblk)
        targetptr = &(parentnode->right);
    else
        targetptr = &(parentnode->left);
    *targetptr = blk;
}

void setnext(block_t *blk, block_t *nextnode) {
    blk->next = nextnode;
    nextnode->parent = blk;
}


int allocated(block_t *blk) {
    return 0 == (blk->header & 0x7);
}

int isfree(block_t *blk) {
    return blk->header & 0x1;
}

block_t *getroot() {
    return startblk->right;
}

/***************static functions for recursive call****************/

static block_t *__tree_search__(block_t *node, size_t size);

static void __insert_node__(block_t *root, block_t *node);

static void __insert_balance__(block_t *node);

static block_t *__find_min__(block_t *node);

static void __rm_node__(block_t *node);

static void __double_black__(block_t *p, block_t *node);

static void __left_rotate__(block_t *node);

static void __right_rotate__(block_t *node);

/*****************************************************************/


block_t *bestfit(size_t size) {
    block_t *blk = getroot();
    return __tree_search__(blk, size);
}


void insert_node(block_t *node) {
    block_t *root = getroot();
    if (root == lastblk) {
        //tree empty, make node root
        setright(startblk, node);
        setright(node, lastblk);
        setleft(node, lastblk);
        setnext(node, lastblk);
        SETCOLOR(node, BLACK);
        return;
    }
    setleft(node, lastblk);
    setright(node, lastblk);
    setnext(node, lastblk);
    SETCOLOR(node, RED);
    __insert_node__(root, node);

}


void rm_node(block_t *target) {
    block_t *prev = target->parent;
    block_t *next = target->next;
    if (getsize(prev) == getsize(target) && isfree(prev)) {
        //parent could be prologue block
        setnext(prev, next);
        return;
    } else if (next != lastblk) {
        setparent(next, target->parent);
        setleft(next, target->left);
        setright(next, target->right);
        SETCOLOR(next, COLOR(target));
        return;
    }

    //no replaceable entry in seg-list
    block_t *replace = NULL;
    if (target->left != lastblk && target->right != lastblk) {
        //has two child node
        replace = __find_min__(target->right);
    } else {
        __rm_node__(target);
        return;
    }
    __rm_node__(replace);

    /* after __rm_node__, replace block is not on the tree
       tree balance will be performed with target node,
       and target node will be switched to replace block afterwards */

    setparent(replace, target->parent);
    setleft(replace, target->left);
    setright(replace, target->right);
    SETCOLOR(replace, COLOR(target));

}

//////////////////////////////////////////////////////////////////////

block_t *__tree_search__(block_t *node, size_t size) {
    size_t blksize = getsize(node);
    if (node == lastblk)
        return node;
    if (blksize < size) {
        return __tree_search__(node->right, size);
    } else {
        block_t *rtblock;
        rtblock = __tree_search__(node->left, size);

        if (rtblock == lastblk)
            rtblock = node;

        if (rtblock->next != lastblk)
            return rtblock->next;
        else
            return rtblock;
    }
}

void __insert_node__(block_t *root, block_t *node) {
    if (getsize(root) > getsize(node)) {
        //left
        if (root->left == lastblk) {
            setleft(root, node);
            __insert_balance__(node);
        } else __insert_node__(root->left, node);
    } else if (getsize(root) < getsize(node)) {
        //right
        if (root->right == lastblk) {
            setright(root, node);
            __insert_balance__(node);
        } else __insert_node__(root->right, node);
    } else {
        block_t *next = root->next;
        setnext(node, next);
        setnext(root, node);
    }
}

/*
 * balance function - only call on new leaf node or color change
 * input must be always red
 */
void __insert_balance__(block_t *node) {
    block_t *parent = node->parent;
    block_t *grandparent = parent->parent;

    if (node == getroot()) {
        SETCOLOR(node, BLACK);
        return;
    }
    block_t *s = (grandparent->left == parent) ?
                 grandparent->right : grandparent->left;
    if (COLOR(parent) == RED) {
        if (getsize(grandparent) <= getsize(parent) && COLOR(s) == BLACK) {
            if (getsize(node) < getsize(parent)) {     //  g
                __right_rotate__(node);                //     p
                SETCOLOR(node, BLACK);                 //   n
                SETCOLOR(grandparent, RED);
                __left_rotate__(node);
            } else {
                SETCOLOR(parent, BLACK);
                SETCOLOR(grandparent, RED);
                //counter-clockwise rotate
                __left_rotate__(parent);
            }
        } else if (getsize(parent) < getsize(grandparent) && COLOR(s) == BLACK) {
            if (getsize(parent) <= getsize(node)) {      //    g
                __left_rotate__(node);                   // p
                SETCOLOR(node, BLACK);                   //   n
                SETCOLOR(grandparent, RED);
                __right_rotate__(node);
            } else {
                SETCOLOR(parent, BLACK);
                SETCOLOR(grandparent, RED);
                //clockwise rotate
                __right_rotate__(parent);
            }
        } else {                            // grandparent(b) have two red child
            SETCOLOR(grandparent, RED);
            SETCOLOR(grandparent->left, BLACK);
            SETCOLOR(grandparent->right, BLACK);
            __insert_balance__(grandparent);
        }
    }
}

block_t *__find_min__(block_t *node) {
    block_t *left = node;
    while (left->left != lastblk)
        left = left->left;
    return left;
}

/*
 * function for removing node with one or no child,
 * will completely detach node from tree
 */
void __rm_node__(block_t *node) {
    block_t *parent = node->parent;
    block_t *child; //child = existing child node, lastblk(black) if none

    child = (node->left == lastblk) ? node->right : node->left;

    (getsize(node) < getsize(parent) ? setleft : setright)(parent, child);

    if (COLOR(child) == RED) {
        SETCOLOR(child, COLOR(node));
    } else if (COLOR(node) == BLACK)
        __double_black__(parent, child);
}

void __double_black__(block_t *p, block_t *node) {
    if (node == startblk)//made tree empty, no need to do anything
        return;
    if (node == getroot())
        return;
    block_t *s, *l, *r;//sibling, sibling-left, sibling-right
    if (p->left == node) {
        s = p->right;
        l = s->left;
        r = s->right;
    } else {
        s = p->left;
        l = s->right;
        r = s->left;
    }

    if (COLOR(r) == RED) {//case *-2
        int p_color = COLOR(p);
        (p->left == node ? __left_rotate__ : __right_rotate__)(s);
        SETCOLOR(p, BLACK);
        SETCOLOR(s, p_color);
        SETCOLOR(r, BLACK);
    } else if (COLOR(l) == RED) {//case *-3
        (p->left == node ? __right_rotate__ : __left_rotate__)(l);
        SETCOLOR(l, BLACK);
        SETCOLOR(s, RED);
        __double_black__(p, node);
    } else if (COLOR(p) == RED) {//case 1-1
        SETCOLOR(p, BLACK);
        SETCOLOR(s, RED);
    } else if (COLOR(s) == BLACK) {//case 2-1
        SETCOLOR(s, RED);
        __double_black__(p->parent, p);
    } else {//case 2-4
        (p->left == node ? __left_rotate__ : __right_rotate__)(s);
        SETCOLOR(s, BLACK);
        SETCOLOR(p, RED);
        __double_black__(p, node);
    }

}

void __left_rotate__(block_t *node) {//input will become root
    block_t *p1 = node->parent;
    block_t *p2 = p1->parent;
    block_t *node_l = node->left;
    setparent(node, p2);
    setright(p1, node_l);
    setleft(node, p1);
}

void __right_rotate__(block_t *node) {//input will become root
    block_t *p1 = node->parent;
    block_t *p2 = p1->parent;
    block_t *node_r = node->right;
    setparent(node, p2);
    setleft(p1, node_r);
    setright(node, p1);
}


void print_tree(block_t *node) {
    block_t *array1[500];
    block_t *array2[500];
    block_t **current = array1;
    block_t **next = array2;
    array1[0] = node;
    array1[1] = NULL;
    printf("--tree form--\n");
    while (1) {
        int i = 0, j = 0;
        while (current[i] != NULL) {
            if (current[i] == lastblk)
                printf("N");
            else {
                if (COLOR(current[i]) == RED)
                    printf("R");
                else
                    printf("B");
                next[j++] = current[i]->left;
                next[j++] = current[i]->right;
            }
            i++;
        }
        if (i == 0)
            break;
        printf("\n");
        next[j] = NULL;


        block_t **tmp = current;
        current = next;
        next = tmp;
    }
}
