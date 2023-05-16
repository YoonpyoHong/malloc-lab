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

#include "mm-explicit.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Yoonpyo Hong",
    /* First member's email address */
    "yoonpyo_@naver.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

// /* single word (4) or double word (8) alignment */
// #define ALIGNMENT 8

// /* rounds up to the nearest multiple of ALIGNMENT */
// #define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
#define WSIZE 4 //word의 크기, footer와 header의 크기
#define DSIZE 8 //double word의 크기
#define CHUNKSIZE (1<<12) // heap의 사이즈를 키우기

#define MAX(x,y) ((x)>(y)? (x) : (y))

// word만큼의 사이즈로 bit를 포장한다.
#define PACK(size, alloc) ((size) | (alloc))

// p 주소에 값을 읽거나 씀
#define GET(p) (*(unsigned int *) (p))
#define PUT(p, val) (*(unsigned int *) (p) = (int)(val))

// p 주소에 할당된 크기나 할당된 필드를 구할 수 있다.
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

//header랑 footer를 인식한다.
#define HDRP(bp) ((char*)(bp)- WSIZE)
#define FTRP(bp) ((char*)(bp)+ GET_SIZE(HDRP(bp)) - DSIZE)

//pred와 succ를 이용하여 다음 가용 노드 전 가용 노드를 찾는다
#define NEXT_FREE(bp) (*(void**)(bp))
#define PREV_FREE(bp) (*(void**)(bp + WSIZE))

//각각 다음과 이전의 블록 포인터를 리턴한다.
#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(((char*)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE(((char*)(bp) - DSIZE)))

static char *heap_listp;
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);


static void *coalesce(void *bp){
    size_t prev_alloc =GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc =GET_ALLOC(HDRP(NEXT_BLKP(bp))); 
    size_t size = GET_SIZE(HDRP(bp));

    if(prev_alloc && next_alloc){
        //next-fit
        // search_bp = bp;
        return bp;
    }
    else if(prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if(!prev_alloc && next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size ,0));
        bp = PREV_BLKP(bp);
    }
    else{
        size+= GET_SIZE(HDRP(PREV_BLKP(bp)))+GET_SIZE(FTRP(NEXT_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    // next-fit
    // search_bp = bp;
    return bp;
}
static void *extend_heap(size_t words){
    char *bp;
    size_t size;
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if((long)(bp = mem_sbrk(size)) == -1) return NULL;
    
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));

    return coalesce(bp);
}

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if((heap_listp = mem_sbrk(8*WSIZE)) == (void *) -1){
        return -1;
    }
    PUT(heap_listp, 0);
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2*WSIZE), NULL);
    PUT(heap_listp + (3*WSIZE), NULL);
    PUT(heap_listp + (4*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (5*WSIZE), PACK(0, 1));
    heap_listp += (2*WSIZE);

    if(extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

static void *find_fit(size_t asize){
    // first-fit
    void *bp;
    for (bp= heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){ 
        if (!GET_ALLOC(HDRP(bp)) && (asize<=GET_SIZE(HDRP(bp)))){ 
            return bp; 
        }
    }
    return NULL; 

    // next-fit
    // if(search_bp == NULL) search_bp = heap_listp;
    // for (; GET_SIZE(HDRP(search_bp)) > 0; search_bp = NEXT_BLKP(search_bp)){ 
    //     if (!GET_ALLOC(HDRP(search_bp)) && (asize<=GET_SIZE(HDRP(search_bp)))){ 
    //         return search_bp; 
    //     }
    // }
    // return NULL; 

    // best-fit
    // void *bp;
    // void *best_bp = NULL;
    // size_t best_size = 100000000*WSIZE;
    // for (bp= heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){ 
    //     if (!GET_ALLOC(HDRP(bp)) && (asize<=GET_SIZE(HDRP(bp))) && ( GET_SIZE(HDRP(bp))< best_size)){ 
    //         best_bp = bp;
    //         best_size = GET_SIZE(HDRP(bp));
    //     }
    // }
    // if(best_bp==NULL){
    //     return NULL; 
    // }else{
    //     return best_bp;
    // }
}

static void place(void *bp, size_t asize){
    size_t now_size = GET_SIZE(HDRP(bp));
    if((now_size-asize) >= 2*DSIZE){
        PUT(HDRP(bp), PACK(asize,1));
        PUT(FTRP(bp), PACK(asize,1));
        bp=NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(now_size-asize,0));
        PUT(FTRP(bp), PACK(now_size-asize,0));
    }else{
        PUT(HDRP(bp), PACK(now_size, 1));
        PUT(FTRP(bp), PACK(now_size, 1));
    }
}
/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;
    if(size ==0){
         return NULL;
    }
    if(size <= DSIZE) {
        asize = 2*DSIZE;
    }
    else{
        asize = DSIZE *((size + (DSIZE) + (DSIZE-1))/DSIZE);
    }
    if((bp= find_fit(asize)) != NULL){
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if((bp= extend_heap(extendsize/WSIZE)) == NULL) return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}


/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size)
{
    if(size <= 0){ 
        mm_free(bp);
        return 0;
    }
    if(bp == NULL){
        return mm_malloc(size); 
    }
    void *newp = mm_malloc(size); 
    if(newp == NULL){
        return 0;
    }
    size_t oldsize = GET_SIZE(HDRP(bp));
    if(size < oldsize){
    	oldsize = size; 
	}
    memcpy(newp, bp, oldsize); 
    mm_free(bp);
    return newp;
}
