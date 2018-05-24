/*
 * mm.c - malloc implemented using segregated list and red-black tree
 * 
 * this package is implemented mainly with segregated list, which consists of
 * free block following structure described below. 
 * While this package is implemented with segregated list, the heads of the linked
 * lists are managed using red-black tree. Every node in list will consist of
 * free blocks of the same size.
 * The front and back part of the block are header and footer. Both contains 
 * size and three flags, which are contained in single unsigned int using 
 * bitwise OR. Three flags are free flag, black flag, and visited flag. 
 * Free flag show that the block is currently free, and black flag show that 
 * current block is free and is a black node in red-black tree. Visited flags
 * are always 0, but is used to mark visited node when traversing tree in 
 * mm_check. It will be used to check if tree is connected appropriately when 
 * debugging.
 * In the payload area, free blocks will contain four pointer, left, right, parent
 * and next, respectively. Left and right pointer connects to left and right node
 * of the tree, and will point to epilogue block if it doesn't exist. Parent 
 * pointer will point to parent node, or previous node if the block is not the head
 * node in segregated list. Next block will point to next block in segregated list,
 * and will point to epilogue block if it doesn't exist.
 *
 ************************
 * Free block structure
 *
 * 32              0
 * -----------------     <- void *p
 * |   size    |a/f| <- stores size of entire block and flags(visited, r/b, a/f)
 * |---------------| __  <- return value; aligned to 8-byte
 * | left ptr      |   |
 * |---------------|
 * | right ptr     |  old payload
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
 ************************
 * 
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

//set to 1 to call mm_check
#define CHECK 0

//set to 1 to make mm_check heap status
#define PRINTBLK 0

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

//returns pointer to the payload
#define PTR(blk) (&(GETLEFT(blk)))

//returns the color of the block
#define COLOR(p) (*(unsigned int *)(p) & 0x6)

//set the color of the free block
#define SETCOLOR(p, color) {*(unsigned int*)(p) = (*(unsigned int*)(p) & ~0x2) | (color);\
                *(unsigned int *) ((void *) (p) + getsize(p) - 4) = *(unsigned int*) (p);}

#define GETLEFT(p) *((void **)p + 1)
#define GETRIGHT(p) *((void **)p + 2)
#define GETPARENT(p) *((void **)p + 3)
#define GETNEXT(p) *((void **)p + 4)

#define ALC 0
#define FREE 1
#define RED 0x0
#define BLACK 0x2

/* makes header and footer from pointer, size and allocation bit */

extern int verbose;


void mm_check();

void Exit(int st);

void blkstatus(void *ptr);

static void *startblk;
static void *lastblk;

//fill in header and footer
static inline void pack(void *blk, size_t size, int alloc);

//check if header is valid
static inline int header_valid(void *blk);

//get size of block(including header and footer)
static inline size_t getsize(void *blk);

//set left node, set to lastblk if none
static inline void setleft(void *blk, void *leftnode);

//set right node, set to lastblk if none
static inline void setright(void *blk, void *rightnode);

//set parent node
static inline void setparent(void *blk, void *parentnode);

//set next block in linked list
static inline void setnext(void *blk, void *nextnode);

//get adjacent block right after
static inline void *getafter(void *blk);

//get adjacent block right before
static inline void *getbefore(void *blk);

//check if allocated
static inline int allocated(void *blk);

//check if block is free
static inline int isfree(void *blk);

//returns root which is connected from static block startblk
static inline void *getroot();

//finds the best fit free block for given size, returns lastblk if none
static void *bestfit(size_t size);

//remove node
static void rm_node(void *target);

//insert node into the red-black tree
static void insert_node(void *node);

//count the number of free blocks by traversing heap area
static int countfreelist();

//count the number of free blocks by traversing tree
static int checkfreetree(void *root);

//check if leaf node has same black height
static int checkblackheight(void *root);

//when mm_check finds an error, this function will print what the tree looks like
static void print_tree(void *node);

/*
 * mm_init - initialize the malloc package.
 *
 * First and second block will be prologue and epilogue block. Prologue block will
 * be used to keep track of root node, and epilogue block will be used as NIL block
 * in red-black tree. Color of epilogue block will be marked as black. This function
 * will also create initial root of the tree.
 */


int mm_init(void) {
    void *p = mem_sbrk(4 + ALIGNMENT * 6 + ALIGNMENT * 10);
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
    pack(lastblk, ALIGNMENT * 3, ALC);
    SETCOLOR(lastblk, BLACK);
    setright(startblk, lastblk);
    p = getafter(p);
    pack(p, ALIGNMENT * 10, FREE); //initial root of tree
    SETCOLOR(p, BLACK);
    setright(startblk, p);
    setright(p, lastblk);
    setleft(p, lastblk);
    setnext(p, lastblk);
    return 0;
}

/*
 * mm_malloc
 *
 * In malloc, function will put padding in size, and allocate block from free list
 * or sbrk. If size is small, size will be rounded up to nearest power of 2 to 
 * utilize coalescing. bestfit() will find the best free block to be allocated, 
 * and will call sbrk if no free block fits the size. When calling sbrk, if 
 * last block is free, function will extend the free block instead of extending
 * the heap with the entire block size.
 */

void *mm_malloc(size_t size) {
//    printf("malloc %x\n", (unsigned int) size);
    size_t newsize, oldsize;
    size_t rsize = size;
    if (rsize < 64 * ALIGNMENT) {//round to nearest power of 2
        rsize--;
        rsize |= rsize >> 1;
        rsize |= rsize >> 2;
        rsize |= rsize >> 4;
        rsize |= rsize >> 8;
        rsize = rsize + 1;
    }
    newsize = ALIGN(rsize + ALIGNMENT);
    void *p;
    if (newsize < 3 * ALIGNMENT)
        newsize = 3 * ALIGNMENT;
    p = bestfit(newsize);
    if (p == lastblk) {
        void *new_blk;
        void *endblock = getbefore(mem_heap_hi() + 1);
        if (isfree(endblock) && getafter(lastblk) != endblock) {
            size_t extend = newsize - getsize(endblock);
            mem_sbrk((int) extend);
            rm_node(endblock);
            pack(endblock, newsize, ALC);
            if (CHECK)
                mm_check();
            return PTR(endblock);
        }
        new_blk = mem_sbrk((int) newsize);
        if (new_blk == (void *) -1) {
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
        void *after;
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
 * Free will make new free block, and store them in segregated list. insert_node
 * function will the put the node in tree. If adjacent blocks are free, 
 * new free block will be coalesced with them. Adjacent blocks will be removed from
 * tree, coalesced, and then will be put back into the tree.
 */
void mm_free(void *ptr) {
    void *p;//points to header
    void *before, *after;
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
 * mm_realloc 
 * If block is located at end of the heap, this function will extend heap without
 * moving the payload. If block next to target block is free, and if coalescing 
 * that block is enough to fit size, function will merge two blocks into one, and
 * return the same ptr without copying payload. If none of these can be applied, 
 * it will call mm_malloc and mm_free.
 */
void *mm_realloc(void *ptr, size_t size) {
    void *oldblk = ptr - sizeof(unsigned int);
    void *newptr;
    size_t oldSize = getsize(oldblk) - 2 * sizeof(unsigned int);

    if ((void *) getafter(oldblk) > mem_heap_hi() && oldSize < size) {
        int extend = ALIGN(size - oldSize);
        void *p = mem_sbrk(extend);
        if (p == (void *) -1) {
            return NULL;
        }
        pack(oldblk, extend + getsize(oldblk), ALC);
        return ptr;
    } else if (oldSize < size) {
        void *after = getafter(oldblk);
        if (isfree(after) && oldSize + getsize(after) > size) {
            rm_node(after);
            pack(oldblk, oldSize + getsize(after), ALC);
            return ptr;
        }

        //if realloc is called frequently, it might be called again
        newptr = mm_malloc(size);
        memcpy(newptr, ptr, oldSize);
        mm_free(ptr);
        return newptr;
    }
    return ptr;
}


int treesize(void *root) {
    if (root == lastblk)
        return 0;
    int freecnt = 1;
    freecnt += treesize(GETLEFT(root));
    freecnt += treesize(GETRIGHT(root));
    return freecnt;
}

void mm_check() {
    int freeblks = 0;
    int freelistblks = 0;

    //checking heap start to end

    freeblks = countfreelist();

    freelistblks = checkfreetree(getroot());
    if (freeblks != freelistblks) {
        printf("free blocks: %d, free blocks in list: %d\n", freeblks, freelistblks);
        Exit(0);
    }

    checkblackheight(getroot());

//    printf("free list size: %d, tree size: %d\n", freeblks, treesize(getroot()));

}

/**************** functions for mm_check ***************************/

//returns 1 header p is valid
static inline int header_valid(void *blk) {
    return *(unsigned int *) blk == *(unsigned int *) (blk + getsize(blk) - 4);
}

int cntlist(void *node) {
    if (node == lastblk)
        return 0;
    else return 1 + cntlist(GETNEXT(node));
}

int checkfreetree(void *root) {
    void *left = GETLEFT(root);
    void *right = GETRIGHT(root);
    if (root == lastblk)
        return 0;
    if (isfree(root) != 1) {
        printf("block in tree is not actually free\n");
        Exit(1);
    }
    if (*(unsigned int *) root & 0x4) {
        printf("tree connection is messed up\n");
        Exit(1);
    }
    *(unsigned int *) root = *(unsigned int *) root | 0x4;//flag for checking visited node
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
    *(unsigned int *) root = *(unsigned int *) root & ~0x4;
    return freecnt;
}

int checkblackheight(void *root) {
    if (root == lastblk)
        return 1;
    int l = checkblackheight(GETLEFT(root));
    int r = checkblackheight(GETRIGHT(root));
    if (l != r) {
        printf("black height incorrect!: %p, left: %d right: %d\n", root, l, r);
        Exit(0);
    }
    if (COLOR(root) == BLACK)
        l++;
    return l;
}

//Exit fuction - called when mm_check finds an error, will deinitialize heap and
//print heap status to help debugging, including heap area and tree structure.
void Exit(int st) {
    printf("\n--Exit summary--\nheap area: %p to %p\nheap size: %x\n", mem_heap_lo(), mem_heap_hi(),
           (unsigned int) mem_heapsize());
    if (st == 0)
        print_tree(getroot());
    mem_deinit();
    exit(st);
}

//blkstatus will print the reason of failure
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
        printf("blkstatus: free block %p, prev: %p next: %p\n", ptr, GETLEFT(ptr), GETRIGHT(ptr));
    printf("size: %x, before: %p after: %p\n", (unsigned int) getsize(ptr), getbefore(ptr), getafter(ptr));
}

int countfreelist() {
    void *p = startblk;
    void *heap_end = mem_heap_hi();
    int cnt = 0;
    if (PRINTBLK)
        printf("block headers: ");
    while (p < heap_end) {
        if (PRINTBLK)
            printf("%p", p);
        if (!header_valid(p) || p < mem_heap_lo()
            || p > mem_heap_hi() || (long) (p + 4) & 0x7) {
            blkstatus(p);
            Exit(1);
        }
        if (isfree(p)) {
            cnt++;
            if (PRINTBLK)
                printf("(f,%d) ", (unsigned int) getsize(p));
        } else if (PRINTBLK)
            printf("(a,%d) ", (unsigned int) getsize(p));
        p = getafter(p);
    }
    if (PRINTBLK)
        printf("%p(end)\n", heap_end);
    return cnt;
}

//print entire tree, will use two array of pointer instead of using dynamic array
void print_tree(void *node) {
    int ARRAYSIZE = 500;
    void *array1[ARRAYSIZE];
    void *array2[ARRAYSIZE];
    void **current = array1;
    void **next = array2;
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
                next[j++] = GETLEFT(current[i]);
                next[j++] = GETRIGHT(current[i]);
                if (j > ARRAYSIZE - 2) {
                    //This won't happen actually
                    printf("\ntree is too big to print it all\n");
                    return;
                }
            }
            i++;
        }
        if (i == 0)
            break;
        printf("\n");
        next[j] = NULL;


        void **tmp = current;
        current = next;
        next = tmp;
    }
}


/********** functions for getting/setting values from free block *************/

void pack(void *blk, size_t size, int alloc) {
    void *ptr = blk;
    *(unsigned int *) blk = (unsigned int) size | alloc;
    ptr = ptr + size - sizeof(ptr);
    *(unsigned int *) ptr = (unsigned int) size | alloc;
}

size_t getsize(void *blk) {
    return *(unsigned int *) blk & ~0x7;
}

void *getbefore(void *blk) {
    void *ptr = blk;
    void *footer = ptr - 4;
    ptr = ptr - (*(unsigned int *) footer & ~0x7);
    return ptr;
}

void *getafter(void *blk) {
    void *ptr = blk;
    ptr = ptr + getsize(blk);
    return ptr;
}

void setleft(void *blk, void *leftnode) {
    void *p;
    p = blk;
    GETLEFT(p) = leftnode;
    GETPARENT(leftnode) = blk;
}

void setright(void *blk, void *rightnode) {
    GETRIGHT(blk) = rightnode;
    GETPARENT(rightnode) = blk;
}

void setparent(void *blk, void *parentnode) {
    GETPARENT(blk) = (void *) parentnode;
    void **targetptr;
    if (getsize(blk) >= getsize(parentnode) || parentnode == startblk)
        targetptr = &(GETRIGHT(parentnode));
    else
        targetptr = &(GETLEFT(parentnode));
    *targetptr = blk;
}

void setnext(void *blk, void *nextnode) {
    GETNEXT(blk) = nextnode;
    GETPARENT(nextnode) = blk;
}


int allocated(void *blk) {
    return 0 == (*(unsigned int *) blk & 0x7);
}

int isfree(void *blk) {
    return *(unsigned int *) blk & 0x1;
}

void *getroot() {
    return GETRIGHT(startblk);
}

/***************static functions for recursive call****************/

static void *__tree_search__(void *node, size_t size);

static void __insert_node__(void *root, void *node);

static void __insert_balance__(void *node);

static void *__find_min__(void *node);

static void __rm_node__(void *node);

static void __double_black__(void *p, void *node);

static void __left_rotate__(void *node);

static void __right_rotate__(void *node);

/************* functions for red-black tree **********************/

/*
 * These functions are used in malloc and free, and will search for node or delete
 * a node. 
 * 
 * bestfit - a function that finds the free block which best fits the input size.
 *
 * insert_node - this will insert node into the tree. If node with same size 
 * exist in red-black tree, node will be put into list, and if it doesn't, this 
 * will be inserted as new node of the red-black tree.
 *
 * rm_node - will remove a node from linked list, and if list size is 1, the node 
 * will be removed from red-black tree.
 */
void *bestfit(size_t size) {
    void *blk = getroot();
    return __tree_search__(blk, size);
}


void insert_node(void *node) {
    void *root = getroot();
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


void rm_node(void *target) {
    void *prev = GETPARENT(target);
    void *next = GETNEXT(target);
    if (getsize(prev) == getsize(target) && isfree(prev)) {
        //parent could be prologue block
        setnext(prev, next);
        return;
    } else if (next != lastblk) {
        setparent(next, GETPARENT(target));
        setleft(next, GETLEFT(target));
        setright(next, GETRIGHT(target));
        SETCOLOR(next, COLOR(target));
        return;
    }

    //no replaceable entry in seg-list
    void *replace = NULL;
    if (GETLEFT(target) != lastblk && GETRIGHT(target) != lastblk) {
        //has two child node
        replace = __find_min__(GETRIGHT(target));
    } else {
        __rm_node__(target);
        return;
    }
    __rm_node__(replace);

    /* after __rm_node__, replace block is not on the tree
       tree balance will be performed with target node,
       and target node will be switched to replace block afterwards */

    setparent(replace, GETPARENT(target));
    setleft(replace, GETLEFT(target));
    setright(replace, GETRIGHT(target));
    SETCOLOR(replace, COLOR(target));

}

//////////////////////////////////////////////////////////////////////

void *__tree_search__(void *node, size_t size) {
    size_t blksize = getsize(node);
    if (node == lastblk)
        return node;
    if (blksize < size) {
        return __tree_search__(GETRIGHT(node), size);
    } else {
        void *rtblock;
        rtblock = __tree_search__(GETLEFT(node), size);

        if (rtblock == lastblk)
            rtblock = node;

        if (GETNEXT(rtblock) != lastblk)
            return GETNEXT(rtblock);
        else
            return rtblock;
    }
}

void __insert_node__(void *root, void *node) {
    if (getsize(root) > getsize(node)) {
        //left
        if (GETLEFT(root) == lastblk) {
            setleft(root, node);
            __insert_balance__(node);
        } else __insert_node__(GETLEFT(root), node);
    } else if (getsize(root) < getsize(node)) {
        //right
        if (GETRIGHT(root) == lastblk) {
            setright(root, node);
            __insert_balance__(node);
        } else __insert_node__(GETRIGHT(root), node);
    } else {
        void *next = GETNEXT(root);
        setnext(node, next);
        setnext(root, node);
    }
}

/*
 * balance function - only call on new leaf node or color change
 * input must be always red
 * this function will balance the tree by rules of the red-black tree
 */
void __insert_balance__(void *node) {
    void *parent = GETPARENT(node);
    void *grandparent = GETPARENT(parent);

    if (node == getroot()) {
        SETCOLOR(node, BLACK);
        return;
    }
    void *s = (GETLEFT(grandparent) == parent) ?
              GETRIGHT(grandparent) : GETLEFT(grandparent);
    if (COLOR(parent) == RED) {//red child of red node
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
            SETCOLOR(GETLEFT(grandparent), BLACK);
            SETCOLOR(GETRIGHT(grandparent), BLACK);
            __insert_balance__(grandparent);
        }
    }
}

//function that finds minimum value: used for removing node
void *__find_min__(void *node) {
    void *left = node;
    while (GETLEFT(left) != lastblk)
        left = GETLEFT(left);
    return left;
}

/*
 * function for removing node with one or no child,
 * will completely detach node from tree
 */
void __rm_node__(void *node) {
    void *parent = GETPARENT(node);
    void *child; //child = existing child node, lastblk(black) if none

    child = (GETLEFT(node) == lastblk) ? GETRIGHT(node) : GETLEFT(node);

    (getsize(node) < getsize(parent) ? setleft : setright)(parent, child);

    if (COLOR(child) == RED) {
        SETCOLOR(child, COLOR(node));
    } else if (COLOR(node) == BLACK)
        __double_black__(parent, child);
}

//for managing double-black occasion from removing node
void __double_black__(void *p, void *node) {
    if (node == startblk)//made tree empty, no need to do anything
        return;
    if (node == getroot())
        return;
    void *s, *l, *r;//sibling, sibling-left, sibling-right
    if (GETLEFT(p) == node) {
        s = GETRIGHT(p);
        l = GETLEFT(s);
        r = GETRIGHT(s);
    } else {
        s = GETLEFT(p);
        l = GETRIGHT(s);
        r = GETLEFT(s);
    }

    if (COLOR(r) == RED) {//case *-2
        int p_color = COLOR(p);
        (GETLEFT(p) == node ? __left_rotate__ : __right_rotate__)(s);
        SETCOLOR(p, BLACK);
        SETCOLOR(s, p_color);
        SETCOLOR(r, BLACK);
    } else if (COLOR(l) == RED) {//case *-3
        (GETLEFT(p) == node ? __right_rotate__ : __left_rotate__)(l);
        SETCOLOR(l, BLACK);
        SETCOLOR(s, RED);
        __double_black__(p, node);
    } else if (COLOR(p) == RED) {//case 1-1
        SETCOLOR(p, BLACK);
        SETCOLOR(s, RED);
    } else if (COLOR(s) == BLACK) {//case 2-1
        SETCOLOR(s, RED);
        __double_black__(GETPARENT(p), p);
    } else {//case 2-4
        (GETLEFT(p) == node ? __left_rotate__ : __right_rotate__)(s);
        SETCOLOR(s, BLACK);
        SETCOLOR(p, RED);
        __double_black__(p, node);
    }
}

void __left_rotate__(void *node) {//input will become root
    void *p1 = GETPARENT(node);
    void *p2 = GETPARENT(p1);
    void *node_l = GETLEFT(node);
    setparent(node, p2);
    setright(p1, node_l);
    setleft(node, p1);
}

void __right_rotate__(void *node) {//input will become root
    void *p1 = GETPARENT(node);
    void *p2 = GETPARENT(p1);
    void *node_r = GETRIGHT(node);
    setparent(node, p2);
    setleft(p1, node_r);
    setright(node, p1);
}

