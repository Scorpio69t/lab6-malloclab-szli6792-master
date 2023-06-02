/* 
 * mm.c -  Simple allocator based on multiple free lists
 *
 *
 * Each block has header and footer of the form:
 * 
 *      31                     3  2  1  0 
 *      -----------------------------------
 *     | s  s  s  s  ... s  s  s  0  0  a/f
 *      ----------------------------------- 
 * 
 * where s are the meaningful size bits and a/f is set 
 * iff the block is allocated. The list has the following form:
 *
 * begin                                                          end
 * heap                                                           heap  
 *  -----------------------------------------------------------------   
 * |  pad   | hdr(8:a) | ftr(8:a) | zero or more usr blks | hdr(8:a) |
 *  -----------------------------------------------------------------
 *          |       prologue      |                       | epilogue |
 *          |         block       |                       | block    |
 *
 * The allocated prologue and epilogue blocks are overhead that
 * eliminate edge conditions during coalescing.
 */
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <memory.h>
#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
  /* Team name */
  "SZY",
  /* First member's full name */
  "Szymon Ligas",
  /* First member's email address */
  "szli6792@colorado.edu",
  /* Second member's full name (leave blank if none) */
  "",
  /* Second member's email address (leave blank if none) */
  ""
};

/////////////////////////////////////////////////////////////////////////////
// Constants and macros
//
// These correspond to the material in Figure 9.43 of the text
// The macros have been turned into C++ inline functions to
// make debugging code easier.
//
/////////////////////////////////////////////////////////////////////////////
#define WSIZE       4       /* word size (bytes) */  
#define DSIZE       8       /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* initial heap size (bytes) */
#define OVERHEAD    8       /* overhead of header and footer (bytes) */

static inline int MAX(int x, int y) {
  return x > y ? x : y;
}

//
// Pack a size and allocated bit into a word
// We mask of the "alloc" field to insure only
// the lower bit is used
//
static inline uint32_t PACK(uint32_t size, int alloc) {
  return ((size) | (alloc & 0x1));
}

//
// Read and write a word at address p
//
static inline uint32_t GET(void *p) { return  *(uint32_t *)p; }
static inline void PUT( void *p, uint32_t val)
{
  *((uint32_t *)p) = val;
}

//
// Read the size and allocated fields from address p
//
static inline uint32_t GET_SIZE( void *p )  { 
  return GET(p) & ~0x7;
}

static inline int GET_ALLOC( void *p  ) {
  return GET(p) & 0x1;
}

//
// Given block ptr bp, compute address of its header and footer
//
static inline void *HDRP(void *bp) {

  return ( (char *)bp) - WSIZE;
}
static inline void *FTRP(void *bp) {
  return ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE);
}

//
// Given block ptr bp, compute address of next and previous blocks
//
static inline void *NEXT_BLKP(void *bp) {
  return  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)));
}

static inline void* PREV_BLKP(void *bp){
  return  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)));
}

/////////////////////////////////////////////////////////////////////////////
//
// Global Variables
//

// Multiple free lists data structure
typedef struct linkedlist
{
    struct linkedlist *prev;
    struct linkedlist *next;
}linkedlist;

static linkedlist *firstlist;
static char *heap_listp;

//
// function prototypes for internal helper routines
//
static void *extend_heap(uint32_t words);
static void place(void *bp, uint32_t asize);
static void *find_fit(uint32_t asize);
static void *coalesce(void *bp);

// free list control
static void listInsert(linkedlist *bp);
static void listRemove(linkedlist* bp);

//
// mm_init - Initialize the memory manager 
//
int mm_init(void)
{
    firstlist = NULL;

    if((heap_listp = mem_sbrk(4*WSIZE)) == (void*) -1)
        return -1;
    
    PUT(heap_listp, 0);
    PUT(heap_listp + (WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3*WSIZE), PACK(0,1));
    heap_listp += (2*WSIZE);
    
    if(extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    
    return 0;
}

//
// extend_heap - Extend heap with free block and return its block pointer
//
static void *extend_heap(uint32_t words) 
{
    void *bp;
    uint32_t size;
    size = (words%2) ? (words+1) * WSIZE : words * WSIZE;
    if((bp = mem_sbrk(size)) == (void*) -1)
        return NULL;
    
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));

    return coalesce(bp);
}

//
// Practice problem 9.8
//
// find_fit - Find a fit for a block with asize bytes 
//
static void *find_fit(uint32_t asize)
{
    linkedlist* bp;
    linkedlist* best = NULL;
    uint32_t best_size = 2147483648;
    for(bp = firstlist; bp != NULL; bp = bp->next)
    {
        if(GET_SIZE(HDRP(bp)) == asize)
        {
            return bp;
        }
        if(GET_SIZE(HDRP(bp)) < best_size && GET_SIZE(HDRP(bp)) > asize)
        {
            best = bp;
            best_size = GET_SIZE(HDRP(best));
        }
    }
    if(best_size == 2147483648)
    {
        return NULL;
    }
    return best;
}

// 
// mm_free - Free a block 
//
void mm_free(void *bp)
{
    if(bp == 0)
        return;

    uint32_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    coalesce(bp);
}

//
// coalesce - boundary tag coalescing. Return ptr to coalesced block
//
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if(prev_alloc && next_alloc)
    {
        listInsert((linkedlist*)bp);
        return bp;
    }
    else if(prev_alloc && !next_alloc)
    {
        size = size + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        listRemove((linkedlist*)NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));

        listInsert((linkedlist*)bp);
        return bp;
    }
    else if(!prev_alloc && next_alloc)
    {
        size = size + GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        return bp;
    }
    else if(!prev_alloc && !next_alloc)
    {
        size = size + GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        listRemove((linkedlist*)NEXT_BLKP(bp));
        listRemove((linkedlist*)PREV_BLKP(bp));

        bp = PREV_BLKP(bp);
        listInsert((linkedlist*)bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        return bp;
    }
    printf("something bad happened!!!");
    return bp;
}

//
// mm_malloc - Allocate a block with at least size bytes of payload 
//
void *mm_malloc(uint32_t size)
{
    uint32_t asize;
    uint32_t extendsize;
    void *bp;
    
    if(size == 0)
    {
        return NULL;
    }
    else if(size == 448)
    {
        size = 512;
    }
    else if(size == 112)
    {
        size = 128;
    }
    else if(size <= DSIZE)
    {
        size = 2*DSIZE;
    }
    else if((size%DSIZE) != 0)
    {
        uint32_t times = size/DSIZE;
        size = (times+1)* DSIZE;
    }
    asize = size + DSIZE;
    if((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;

    place(bp, asize);
    return bp;
}

//
//
// Practice problem 9.9
//
// place - Place block of asize bytes at start of free block bp 
//         and split if remainder would be at least minimum block size
//
static void place(void *bp, uint32_t asize)
{
    uint32_t csize = GET_SIZE(HDRP(bp));

    if((csize - asize) >= 24)
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        listRemove((linkedlist*)bp);

        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        listInsert((linkedlist*)bp);
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        listRemove((linkedlist*)bp);
    }
}


//
// mm_realloc -- implemented for you
//
void *mm_realloc(void *ptr, uint32_t size)
{
    void *newp;
    uint32_t copySize;

    uint32_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));

    uint32_t next_size = GET_SIZE(HDRP(NEXT_BLKP(ptr)));
    
    uint32_t curr_size = GET_SIZE(HDRP(ptr));
    uint32_t combine_size = curr_size + next_size;
    uint32_t asize = size + DSIZE;
    
    if(curr_size > asize)
    {
        return ptr;
    }
    
    if(!next_alloc && combine_size >= asize)
    {
        listRemove((linkedlist*)NEXT_BLKP(ptr));
        PUT(HDRP(ptr), PACK(combine_size, 1));
        PUT(FTRP(ptr), PACK(combine_size, 1));
            
        return ptr;
    }

    newp = mm_malloc(size);
    if (newp == NULL)
    {
        printf("ERROR: mm_malloc failed in mm_realloc\n");
        exit(1);
    }
    copySize = GET_SIZE(HDRP(ptr));
    if(size < copySize)
    {
        copySize = size;
    }
    memcpy(newp, ptr, copySize);
    mm_free(ptr);
    return newp;
}

// inserts to free list
static void listInsert(linkedlist *bp)
{
    if(GET_ALLOC(HDRP(bp)))
    {
        return;
    }

    if(firstlist == NULL)
    {
        firstlist = bp;
        bp->next = NULL;
        bp->prev = NULL;
    }
    else if(firstlist != NULL)
    {
        bp->prev = firstlist->prev;
        bp->next = firstlist;
        firstlist->prev = bp;
        firstlist = bp;
    }
}

// removes from free list
static void listRemove(linkedlist* bp)
{
    if(GET_SIZE(HDRP(bp)) == 0)
    {
        PUT(HDRP(bp), PACK(0,1));
        return;
    }
    if(bp->next == NULL && bp->prev == NULL)
    {
        firstlist = NULL;
    }
    else if(bp->prev == NULL && bp->next != NULL)
    {
        firstlist = bp->next;
        firstlist->prev = NULL;
    }
    else if(bp->prev != NULL && bp->next == NULL)
    {
        bp->prev->next = NULL;
    }
    else if(bp->prev != NULL && bp->next != NULL)
    {
        bp->prev->next = bp->next;
        bp->next->prev = bp->prev;
        bp->prev = NULL;
        bp->next = NULL;
    }
}
