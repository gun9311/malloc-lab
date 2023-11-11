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
#define ALIGNMENT 8 // 더블 워드 정렬

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7) // 올림하여 데이터 크기 정렬


#define SIZE_T_SIZE (ALIGN(sizeof(size_t))) // 'size_t' 데이터 타입의 크기를 정렬 // 여기서 'size_t' 는 'char'형

#define WSIZE       4 // 워드 사이즈
#define DSIZE       8 // 더블 워드 사이즈
#define CHUNKSIZE   (1<<12) // 4KB로 초기 블록 설정

#define MAX(x,y) ((x) > (y) ? (x) : (y)) // 최댓값 찾기

#define PACK(size, alloc) ((size) | (alloc)) // 사이즈와 할당여부를 패킹

#define GET(p)          (*(unsigned int *)(p)) // p가 가르키는 값을 추출
#define PUT(p, val)     (*(unsigned int *)(p) = (val)) // p가 가르키는 값을 val으로

#define GET_SIZE(p)     (GET(p) & ~0x7) // 헤더의 값과 비트 연산하여 사이즈를 파악함.
#define GET_ALLOC(p)    (GET(p) & 0x1)  // 할당 여부를 파악

#define HDRP(bp)        ((char *)(bp) - WSIZE) // 해당 블록 헤드의 주소
#define FTRP(bp)        ((char *)(bp) + GET_SIZE(HDRP(bp)) -DSIZE) // 해당 블록 풋터의 주소

#define NEXT_BLKP(bp)   ((char *)(bp)) + GET_SIZE((((char *)(bp) - WSIZE))) // 다음 블록 메모리 시작 주소
#define PREV_BLKP(bp)   ((char *)(bp)) - GET_SIZE((((char *)(bp) - DSIZE))) // 이전 블록 메모리 시작 주소
/* 
 * mm_init - initialize the malloc package.
 */

static void *coalesce(char *bp)
{
    // 만약 확장 블럭 prev 블럭이 가용이면 연결하기
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // size_t는 바이트 사이즈 // prev 블럭 할당 여부 체크 // ((bp) - DSIZE) 로 prev 블럭 풋터 체크 불가??
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // next 블럭 할당 여부 체크
    size_t size = GET_SIZE(HDRP(bp)); // 현재 블럭 사이즈

    if (prev_alloc && next_alloc) { // Case 1 : prev, next 블록 모두 할당 상태이면
        return bp; // 현재 주소 포인터 반환
    }

    else if (prev_alloc && !next_alloc) { // Case 2 : prev 블록은 할당 상태고, next 블록은 가용 상태이면
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // size = 현재 블록 사이즈 + next 블록 사이즈
        PUT(HDRP(bp), PACK(size, 0)); // 연결된 현재 블록 기준으로 헤더 세팅
        PUT(FTRP(bp), PACK(size, 0)); // 연결된 현재 블록 기준으로 풋터 세팅 // next 블록 기준으로 세팅하는 것도 상관없는지??
    }

    else if (!prev_alloc && next_alloc) { // Case 3 : prev 블록은 가용 상태고, next 블록은 할당 상태이면
        size += GET_SIZE(HDRP(PREV_BLKP(bp))); // size = 현재 블록 사이즈 + prev 블록 사이즈
        PUT(FTRP(bp), PACK(size, 0)); // 연결된 블록에 풋터 세팅
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 연결된 prev 블록 기준으로 헤더 세팅
        bp = PREV_BLKP(bp); //bp는 prev 블록 기준으로 갱신
    }

    else { // Case 4 : prev, next 블록 모두 가용 상태이면
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp))); // size = 현재 블록 사이즈 + prev 블록 사이즈 + next 블록 사이즈
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 연결된 prev 블록 기준으로 헤더 세팅
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 연결된 next 블록 기준으로 풋터 세팅 // 현재 블록 기준으로 세팅하는 것도 상관없는지??
        bp = PREV_BLKP(bp); //bp는 앞 블록 기준으로 갱신
    }
    return bp; // 변경된 주소 포인터 반환
}

static void *extend_heap(size_t words) // 워드 사이즈로 인자 받음
{   
    char * bp;
    size_t size;
    
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; // 홀짝 따져서 size = 바이트 사이즈로 저장
    if ((long)(bp = mem_sbrk(size)) == -1) // mem_sbrk 후 old_brk를 반환받지 못하면 힙 확장 실패
        return NULL;

    PUT(HDRP(bp), PACK(size, 0)); // 프리 블록 헤더 값 넣기
    PUT(FTRP(bp), PACK(size, 0)); // 프리 블록 풋터 값 넣기
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 에필로그 헤더 값 넣기

    return coalesce(bp); // 이전 블록 가용이면 새 블록과 연결하기
}

static void* heap_listp ; // 힙 포인터 정적 전역 변수 선언

int mm_init(void)    
{
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void*)-1) // 힙 생성 체크
        return -1;
    PUT(heap_listp, 0); // unused
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE,1)); // 프롤로그 블록 헤더 패킹
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE,1)); // 프롤로그 블록 풋터 패킹
    PUT(heap_listp + (3*WSIZE), PACK(0,1)); // 에필로그 블록 헤더 패킹
    heap_listp += (2*WSIZE); // 프롤로그 블록 풋터로 포인터 이동

    extend_heap(CHUNKSIZE/WSIZE); // 워드 사이즈로 인자 넘김

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) 
        return -1; // 실패하면
    return 0; // 성공하면
}

static void *find_fit(size_t asize)
{
    void *bp;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) { // 왜 프롤로그 블록부터 확인??
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) { // 확인하는 블록이 가용이고 요청 사이즈를 수용하면
            return bp; // 해당 블록 데이터 시작 주소 반환
        }
    }
    return NULL; // 맞는 사이즈가 없으면
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize-asize) >= (2*DSIZE)) { // 가용블록 사이즈 - 요청 사이즈 >= 4워드면
        PUT(HDRP(bp), PACK(asize, 1)); // 요청 사이즈 만큼만 블록 할당하고 헤더 세팅
        PUT(FTRP(bp), PACK(asize, 1)); // 풋터 세팅
        bp = NEXT_BLKP(bp); // 할당하고 남는 부분으로 주소 포인터 이동
        PUT(HDRP(bp), PACK(csize-asize, 0)); // 남는 블록 헤더 세팅
        PUT(FTRP(bp), PACK(csize-asize, 0)); // 남는 블록 풋터 세팅
    }
    else {                             // 가용블록 사이즈 - 요청 사이즈 < 4워드면
        PUT(HDRP(bp), PACK(csize, 1)); // 가용블록 전체를 할당하고 헤더세팅
        PUT(FTRP(bp), PACK(csize, 1)); // 풋터세팅
    }
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */

void *mm_malloc(size_t size)
{
    int newsize = ALIGN(size + SIZE_T_SIZE); // 더블 워드 정렬 //왜 int형으로?
    size_t extendsize; // 기존 블록에 맞는 가용이 없으면 힙 확장
    void *p = mem_sbrk(newsize); // 기존 블록의 마지막 워드 포인터??
    if (p == (void *)-1)
	return NULL;
    else {
        *(size_t *)p = size; // 기존 블록 사이즈
        return (void *)((char *)p + SIZE_T_SIZE); // 다음 블록 데이터 포인터??
    }

    if (size == 0) // 요청 사이즈가 0이면 무시
        return NULL;
    
    // 사이즈 정렬은 newsize로 대체 가능??

    if ((p = find_fit(newsize)) != NULL) { // 기존 블록에 맞는 가용 사이즈가 있으면
        place(p, newsize); //
        return p; 
    }

    //기존 블록에 맞는 가용 사이즈가 없으면
    extendsize = MAX(newsize, CHUNKSIZE); // newsize와 4KB중 큰 것을 선택해서
    if ((p = extend_heap(extendsize/WSIZE)) == NULL) // 힙 영역 확장(인자는 워드로 넘김)
        return NULL;    // 실패하면
    place(p, newsize);  // 성공하면
    return p;
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
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}