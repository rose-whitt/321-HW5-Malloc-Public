/* 
 * Simple, 32-bit and 64-bit clean allocator based on an implicit free list,
 * first fit placement, and boundary tag coalescing, as described in the
 * CS:APP3e text.  Blocks are aligned to double-word boundaries.  This
 * yields 8-byte aligned blocks on a 32-bit processor, and 16-byte aligned
 * blocks on a 64-bit processor.  However, 16-byte alignment is stricter
 * than necessary; the assignment only requires 8-byte alignment.  The
 * minimum block size is four words.
 *
 * This allocator uses the size of a pointer, e.g., sizeof(void *), to
 * define the size of a word.  This allocator also uses the standard
 * type uintptr_t to define unsigned integers that are the same size
 * as a pointer, i.e., sizeof(uintptr_t) == sizeof(void *).
 */

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <math.h>

#include "memlib.h"
#include "mm.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
	/* Team name */
	"Girl Boss",
	/* First member's full name */
	"Rose Whitt",
	/* First member's NetID */
	"rew9",
	/* Second member's full name (leave blank if none) */
	"Madison Roy",
	/* Second member's NetID (leave blank if none) */
	"mmr11"};

/* Explicit Free List - Circular Doubly Linked List */
struct seg_list
{
	struct seg_list *next; /* Pointer to next block */
	struct seg_list *prev; /* Pointer to previous block */
};

/* Basic constants and macros: */
#define WSIZE sizeof(void *) /* Word and header/footer size (bytes) */
#define DSIZE (2 * WSIZE)	 /* Doubleword size (bytes) */
#define ALIGN_SIZE 8		 /* Alignment size */
#define CHUNKSIZE (1 << 12)	 /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word. */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p. */
#define GET(p) (*(uintptr_t *)(p))
#define PUT(p, val) (*(uintptr_t *)(p) = (val))

/* Read the size and allocated fields from address p. */
#define GET_SIZE(p) (GET(p) & ~(ALIGN_SIZE - 1))
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer. */
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks. */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

/* Global variables: */
static char *heap_listp; /* Pointer to first block */

/* Function prototypes for internal helper routines: */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/* Pointer to first free block of each free list */
static struct seg_list *free_listp;

/*
 * Function prototypes for heap consistency
 * checker routines:
 */
static void checkblock(void *bp);
static void checkheap(bool verbose);
static void printblock(void *bp);

static void remove_circular(struct seg_list *block);
static void insert_circular(struct seg_list *block, struct seg_list *dummy);
static unsigned int find_list_head(unsigned int size);
static void init_head(struct seg_list *dummy);
unsigned int MAX_SIZE;

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Initialize the memory manager.  Returns 0 if the memory manager was
 *   successfully initialized and -1 otherwise.
 */
int mm_init(void)
{
	/* Initialize array size */
	MAX_SIZE = 15;

	/* Create the initial empty array */
	size_t seg_size = sizeof(struct seg_list);
	if ((free_listp = mem_sbrk(MAX_SIZE * seg_size)) == (void *)-1)
		return (-1);

	/* Create the initial empty heap: 3 bc one for each PUT */
	if ((heap_listp = mem_sbrk(3 * WSIZE)) == (void *)-1)
		return (-1);

	/* Initialize the array of free lists */
	unsigned int i;
	/* Start at 1 bc 2^0 payload is no good */
	for (i = 0; i < MAX_SIZE; i++)
	{
		init_head(&free_listp[i]);
	}

	PUT(heap_listp, PACK(DSIZE, 1));			   /* Prologue header */
	PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
	PUT(heap_listp + (2 * WSIZE), PACK(0, 1));	   /* Epilogue header */

	heap_listp += WSIZE;

	/* Extend the empty heap with a free block of CHUNKSIZE bytes. */
	void *bp;
	if ((bp = extend_heap(CHUNKSIZE / WSIZE)) == NULL)
		return (-1);
	return (0);
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Allocate a block with at least "size" bytes of payload, unless "size" is
 *   zero.  Returns the address of this block if the allocation was successful
 *   and NULL otherwise.
 */
void *
mm_malloc(size_t size)
{

	size_t asize;	   /* Adjusted block size */
	size_t extendsize; /* Amount to extend heap if no fit */
	void *bp;

	/* Ignore spurious requests. */
	if (size == 0)
		return (NULL);

	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= DSIZE)
		asize = DSIZE * 2;
	else
		asize = ALIGN_SIZE * ((size + DSIZE + (ALIGN_SIZE - 1)) / ALIGN_SIZE);

	/* Search the free list for a fit. */
	if ((bp = find_fit(asize)) != NULL)
	{
		place(bp, asize);
		return (bp);
	}

	/* No fit found.  Get more memory and place the block. */
	extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
		return (NULL);
	place(bp, asize);
	return (bp);
}

/* 
 * Requires:
 *   "bp" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Free a block.
 */
void mm_free(void *bp)
{

	size_t size;

	/* Ignore spurious requests. */
	if (bp == NULL)
		return;

	/* Free and coalesce the block. */
	size = GET_SIZE(HDRP(bp));
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));

	coalesce(bp);
}

/*
 * Requires:
 *   "ptr" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Reallocates the block "ptr" to a block with at least "size" bytes of
 *   payload, unless "size" is zero.  If "size" is zero, frees the block
 *   "ptr" and returns NULL.  If the block "ptr" is already a block with at
 *   least "size" bytes of payload, then "ptr" may optionally be returned.
 *   Otherwise, a new block is allocated and the contents of the old block
 *   "ptr" are copied to that new block.  Returns the address of this new
 *   block if the allocation was successful and NULL otherwise.
 */
void *
mm_realloc(void *ptr, size_t size)
{
	size_t oldsize;
	void *newptr;
	size_t newsize;

	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= DSIZE)
		newsize = DSIZE * 2;
	else
		newsize = ALIGN_SIZE * ((size + DSIZE +
								 (ALIGN_SIZE - 1)) /
								ALIGN_SIZE);
	oldsize = GET_SIZE(HDRP(ptr));

	/* If size == 0 then this is just free, and we return NULL. */
	if (size == 0)
	{
		mm_free(ptr);
		return (NULL);
	}

	/* If oldptr is NULL, then this is just malloc. */
	if (ptr == NULL)
		return (mm_malloc(size));

	/* Copy the old data. */
	if (newsize < oldsize)
		return (ptr);

	newptr = mm_malloc(2 * size);

	/* If realloc() fails the original block is left untouched */
	if (newptr == NULL)
		return (NULL);

	memcpy(newptr, ptr, oldsize);

	/* Free the old block. */
	mm_free(ptr);

	return (newptr);
}

/*
 * The following routines are internal helper routines.
 */

/*
 * Requires:
 *   "bp" is the address of a newly freed block.
 *
 * Effects:
 *   Perform boundary tag coalescing.  Returns the address of the coalesced
 *   block.
 */
static void *
coalesce(void *bp)
{

	size_t size = GET_SIZE(HDRP(bp));
	bool prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	bool next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));

	/* Reduces repeated code */
	struct seg_list *new_free;

	if (prev_alloc && next_alloc)
	{ /* Case 1 : Previous and Next blocks are allocated */
		/* No joining, no remove necessary */
		new_free = (struct seg_list *)bp;
	}
	else if (prev_alloc && !next_alloc)
	{ /* Case 2 : Previous block is allocated, next block is not */

		/* Join with next block */
		struct seg_list *to_delete2 = (struct seg_list *)NEXT_BLKP(bp);
		remove_circular(to_delete2);

		/* Update size with joined block */
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));

		/* Header address stays the same, footer address changes */
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));

		new_free = (struct seg_list *)bp;
	}
	else if (!prev_alloc && next_alloc)
	{ /* Case 3 : Next block is allocated, previous block is not */

		/* Join with next block */
		struct seg_list *to_delete3 = (struct seg_list *)PREV_BLKP(bp);
		remove_circular(to_delete3);

		/* Update size with joined block */
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));

		/* Footer address stays the same, header address changes */
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));

		/* Change header pointer */
		bp = PREV_BLKP(bp);

		new_free = (struct seg_list *)bp;
	}
	else
	{ /* Case 4 */
		/* Join with next and previous blocks */
		struct seg_list *prev_delete = (struct seg_list *)PREV_BLKP(bp);
		remove_circular(prev_delete);

		struct seg_list *next_delete = (struct seg_list *)NEXT_BLKP(bp);
		remove_circular(next_delete);

		size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
				GET_SIZE(FTRP(NEXT_BLKP(bp)));

		/* Footer and header address change*/
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));

		/* Change header pointer */
		bp = PREV_BLKP(bp);

		new_free = (struct seg_list *)bp;
	}

	/* Insert joined block into the correct free list */
	insert_circular(new_free, &free_listp[find_list_head(size)]);

	/* Return new block pointer */
	return (bp);
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Extend the heap with a free block and return that block's address.
 */
static void *
extend_heap(size_t words)
{

	size_t size;
	void *bp;

	/* Allocate an even number of words to maintain alignment. */
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

	if ((bp = mem_sbrk(size)) == (void *)-1)
		return (NULL);

	/* Initialize free block header/footer and the epilogue header. */
	PUT(HDRP(bp), PACK(size, 0));		  /* Free block header */
	PUT(FTRP(bp), PACK(size, 0));		  /* Free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

	/* Coalesce if the previous block was free. */
	return (coalesce(bp));
}

/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Find a fit for a block with "asize" bytes.  Returns that block's address
 *   or NULL if no suitable block was found. 
 */
static void *
find_fit(size_t asize)
{

	unsigned int head = find_list_head(asize);

	/* Optimization */
	if (head + 1 != MAX_SIZE)
	{
		head++;
	}
	unsigned int idx;

	/* Iterate through the last list to find an appropriate size */
	for (idx = head; idx < MAX_SIZE; idx++)
	{ /* iterate over free list array buckets */

		struct seg_list *bp = free_listp[idx].next;

		/* While bp is not dummy (rules of circular) */
		while (bp != &free_listp[idx])
		{
			if (asize <= GET_SIZE(HDRP((void *)bp)))
			{
				return ((void *)bp);
			}

			bp = bp->next;
		}
	}

	/* No fit was found */
	return (NULL);
}

/* 
 * Requires:
 *   "bp" is the address of a free block that is at least "asize" bytes.
 *
 * Effects:
 *   Place a block of "asize" bytes at the start of the free block "bp" and
 *   split that block if the remainder would be at least the minimum block
 *   size. 
 */
static void
place(void *bp, size_t asize)
{

	size_t csize = GET_SIZE(HDRP(bp));

	remove_circular(bp);

	/* Case 1 : Split block */
	if ((csize - asize) >= (2 * DSIZE))
	{

		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));

		bp = NEXT_BLKP(bp);

		PUT(HDRP(bp), PACK(csize - asize, 0));

		PUT(FTRP(bp), PACK(csize - asize, 0));

		unsigned int head_ptr = find_list_head(csize - asize);

		insert_circular(bp, &free_listp[head_ptr]);
	}
	/* Case 2 : Do not split */
	else
	{

		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
	}
}

/* 
 * The remaining routines are heap consistency checker routines.
 */

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Perform a minimal check on the block "bp".
 */
static void
checkblock(void *bp)
{

	if ((uintptr_t)bp % ALIGN_SIZE)
		printf("Error: %p is not doubleword aligned\n", bp);
	if (GET(HDRP(bp)) != GET(FTRP(bp)))
		printf("Error: header does not match footer\n");
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Perform a minimal check of the heap for consistency. 
 */
void checkheap(bool verbose)
{
	void *bp;

	if (verbose)
		printf("Heap (%p):\n", heap_listp);

	if (GET_SIZE(HDRP(heap_listp)) != DSIZE ||
		!GET_ALLOC(HDRP(heap_listp)))
		printf("Bad prologue header\n");
	checkblock(heap_listp);

	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
	{
		if (verbose)
			printblock(bp);
		checkblock(bp);
		/* Checks that the pointers point to valid addresses. */
		if (GET_ALLOC(bp) > GET_SIZE(heap_listp))
			printf("Pointer points to an invalid address.");
	}

	if (verbose)
		printblock(bp);

	if (GET_SIZE(HDRP(bp)) != 0 || !GET_ALLOC(HDRP(bp)))
		printf("Bad epilogue header\n");

	/* Iterate over free list to check the validity of its contents. */
	for (unsigned int i = 0; i < MAX_SIZE; i++)
	{
		for (struct seg_list *block = free_listp[i].next;
			 block != &free_listp[i]; block = block->next)
		{
			if (GET_ALLOC(bp))
			{
				printf("Error: Block %p allocated, "
					   "remove from free list.\n",
					   block);
			}
		}
	}
}

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Print the block "bp".
 */
static void
printblock(void *bp)
{
	size_t hsize, fsize;
	bool halloc, falloc;

	checkheap(true);
	hsize = GET_SIZE(HDRP(bp));
	halloc = GET_ALLOC(HDRP(bp));
	fsize = GET_SIZE(FTRP(bp));
	falloc = GET_ALLOC(FTRP(bp));

	if (hsize == 0)
	{
		printf("%p: end of heap\n", bp);
		return;
	}

	printf("%p: header: [%zu:%c] footer: [%zu:%c]\n", bp,
		   hsize, (halloc ? 'a' : 'f'),
		   fsize, (falloc ? 'a' : 'f'));
}

/**
 * Requires:
 * 	Nothing.
 * 
 * Effects:
 * 	Removes "block" from a circularly doubly linked list.
 * 	The fields "next" and "prev" of wd are set to NULL before return.
 *  
 */
static void
remove_circular(struct seg_list *block)
{

	/* 1) get block's prev, set its next to block's next */
	block->prev->next = block->next;

	/* 2) get block's next, set its prev to block's prev */
	block->next->prev = block->prev;

	/* For safety */
	block->next = NULL;
	block->prev = NULL;
}

/**
 * Requires:
 * 	Nothing.
 * 
 * Effects:
 * 	Inserts block into a circular doubly linked list after dummy.
 *  
 */
static void
insert_circular(struct seg_list *block, struct seg_list *dummy)
{

	block->prev = dummy->prev;
	block->next = dummy;
	dummy->prev->next = block;
	dummy->prev = block;
}

/**
 * Requires:
 * 	Nothing.
 * 
 * Effects:
 * 	Returns the address of the list head for a certain size.
 */
static unsigned int
find_list_head(unsigned int size)
{

	if (size < 2)
		return 0;
	if (size < 4)
		return 1;
	if (size < 8)
		return 2;
	if (size < 16)
		return 3;
	if (size < 32)
		return 4;
	if (size < 64)
		return 5;
	if (size < 128)
		return 6;
	if (size < 256)
		return 7;
	if (size < 512)
		return 8;
	if (size < 1024)
		return 9;
	if (size < 2048)
		return 10;
	if (size < 4096)
		return 11;
	if (size < 8192)
		return 12;
	if (size < 16384)
		return 13;
	return 14;
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Initialize the dummy head in a circular doubly linked list.
 */
static void
init_head(struct seg_list *dummy)
{
	dummy->next = dummy;
	dummy->prev = dummy;
}
