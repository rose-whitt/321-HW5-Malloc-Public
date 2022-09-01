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

/* Basic constants and macros: */
#define WSIZE sizeof(void *) /* Word and header/footer size (bytes) */
#define DSIZE (2 * WSIZE)	 /* Doubleword size (bytes) */
#define CHUNKSIZE (1 << 12)	 /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word. */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p. */
#define GET(p) (*(uintptr_t *)(p))
#define PUT(p, val) (*(uintptr_t *)(p) = (val))

/* Read the size and allocated fields from address p. */
#define GET_SIZE(p) (GET(p) & ~(DSIZE - 1))
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer. */
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks. */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

/* Global variables: */
static char *heap_listp; /* Pointer to first block */
void *free_listp;		 /* Pointer to first free block */

/* Function prototypes for internal helper routines: */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void remove_circular(void *bp);
static void insert_circular(void *bp, void *block);

/* Struct to contain explicit list. */
struct seg_list
{
	struct seg_list *next;	// Pointer to next list
	struct seg_list *prev;	// Pointer to previous list
};

/* Pointer to the beginning of the free list, aka pointer to the dummy head. */
static struct seg_list *dummy_ptr; 

/* Function prototypes for heap consistency checker routines: */
static void checkblock(void *bp);
static void checkheap(bool verbose);
static void printblock(void *bp);


/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Initialize the memory manager.  Returns 0 if the memory manager was
 *   successfully initialized and -1 otherwise.
 */
int 
mm_init(void)
{
	/* Create the initial empty heap. Multiply by for each PUT */
	if ((heap_listp = mem_sbrk(6 * WSIZE)) == (void *)-1)
		return (-1);

	/* Initialize the dummy pointer. */
	dummy_ptr = (struct seg_list *)(heap_listp + WSIZE); 

	PUT(heap_listp, 0); /* Alignment padding */

	/* Next and Previous are just the payload, so no allocated memory there */
	PUT(heap_listp + (1 * WSIZE), 0); /* Dummy node next */
	PUT(heap_listp + (2 * WSIZE), 0); /* Dummy node previous */

	/* Initialize circular dummy header. */
	dummy_ptr->next = dummy_ptr;
	dummy_ptr->prev = dummy_ptr;

	PUT(heap_listp + (3 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
	PUT(heap_listp + (4 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
	PUT(heap_listp + (5 * WSIZE), PACK(0, 1));	   /* Epilogue header */

	heap_listp += (4 * WSIZE);

	/*
	 * Our free_listp points to the first free block and since the free list
	 * is empty right now, free_listp must be NULL. 
	 */
	free_listp = NULL;

	/* Extend the empty heap with a free block of CHUNKSIZE bytes. */
	if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
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
	void *bp;		   /* Address of allocated block or NULL */

	/* Ignore spurious requests. */
	if (size == 0)
		return (NULL);

	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= DSIZE)
		asize = 2 * DSIZE;
	else
		asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);

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
void
mm_free(void *bp)
{
	size_t size;

	/* Ignore spurious requests. */
	if (bp == NULL)
		return;

	/* Free and coalesce the block. */
	size = GET_SIZE(HDRP(bp));

	/* Removes header and footers from block. */
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
	void *newptr;
	size_t oldsize;
	size_t newsize;

	/* Adjust block size to include overhead and alignment reqs. */
	if (size < DSIZE)
		newsize = 2 * DSIZE;
	else
		newsize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);
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

	/* Over-allocate for the size of the block to avoid having to 
	 * repeat expensive operations. 
	 */

	newptr = mm_malloc(2 * size);

	/* If realloc() fails the original block is left untouched  */
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
	/* Get the size and addresses for allocated headers and footers */
	size_t size = GET_SIZE(HDRP(bp));
	bool prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	bool next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));

	if (prev_alloc && next_alloc)
	{ /* Case 1 */
	/* Also sets bp to be the new free list pointer. */
		insert_circular(bp, (void *)dummy_ptr); 
		return (bp);
	}
	else if (prev_alloc && !next_alloc)
	{ /* Case 2 */
		remove_circular(NEXT_BLKP(bp));
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
		/* Also sets bp to be the new free list pointer. */
		insert_circular(bp, (void *)dummy_ptr); 
	}
	else if (!prev_alloc && next_alloc)
	{ /* Case 3 */
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		remove_circular(PREV_BLKP(bp));
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
		/* Also sets bp to be the new free list pointer. */
		insert_circular(bp, (void *)dummy_ptr); 
	}
	else
	{ /* Case 4 */
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
				GET_SIZE(FTRP(NEXT_BLKP(bp)));
		remove_circular(NEXT_BLKP(bp));
		remove_circular(PREV_BLKP(bp));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
		/* Also sets bp to be the new free list pointer. */
		insert_circular(bp, (void *)dummy_ptr); 
	}
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
	void *bp;

	/*Set free list pointer to null to avoid null pointer. */
	if (free_listp == NULL)
	{
		return NULL;
	}

	/* Search for the first fit. */
	for (bp = free_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
	{
		if (!GET_ALLOC(HDRP(bp)) && asize <= GET_SIZE(HDRP(bp)))
			return (bp);
	}
	
	/* No fit was found. */
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

	if ((csize - asize) >= (2 * DSIZE))
	{
		/* Places the block if it needs extra space. */
		remove_circular(bp);
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize - asize, 0));
		PUT(FTRP(bp), PACK(csize - asize, 0));
		/* Also sets bp to be the new free list pointer. */
		insert_circular(bp, (void *)dummy_ptr); 
	}
	else
	{
		/* Places the block if it does not need extra space. */
		remove_circular(bp);
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
		/* Also sets bp to be the new free list pointer. */
		insert_circular(bp, (void *)dummy_ptr); 
	}
}

 /* 
 * Requires:
 *   "bp" is the address of a free block that is at least "asize" bytes.
 *
 * Effects:
 *   Remove the given pointer to a block from the free list; Assumes list 
 *   is not empty and free list contains bp.
 */
void 
remove_circular(void *bp)
{
	/* Reduces repeated code */
	struct seg_list *bp_node = (struct seg_list *)bp;

	/* Case 1: This block is the only block in the list */
	/*  [ dummy ] */
	/*	  ↕️  ↕️	*/
	/*  [   bp  ] */
	if (bp_node->next == dummy_ptr && bp_node->prev == dummy_ptr)
	{
		/* Reset list to self pointing dummy */
		dummy_ptr->next = dummy_ptr;
		dummy_ptr->prev = dummy_ptr;

		/* For safety check */
		bp_node->next = NULL;
		bp_node->prev = NULL;

		/* Free List is now "empty", set pointer to NULL */
		free_listp = NULL;

		/* The dummy header points to itself */
	}
	/* Case 2: This block is the first node in the list */
	else if (dummy_ptr->next == bp_node && bp_node->prev == dummy_ptr)
	{
		/* bp's next is now the first free block, set pointer accordingly */
		free_listp = (void *)bp_node->next; 

		dummy_ptr->next = bp_node->next;
		(bp_node->next)->prev = dummy_ptr; 
		/* bp_node's next previous was bp_node, is now dummy_ptr */

		/* For safety check */
		bp_node->next = NULL;
		bp_node->prev = NULL;
	}
	/* Case 3: This block is the last block in the list */
	else if (bp_node->next == dummy_ptr && dummy_ptr->prev == bp_node)
	{ 
		/* Last node's next is the start of the free list */
		/* Free List head does not change, free_listp stays the same */
		/* dummy's previous is now bp's previous */
		dummy_ptr->prev = bp_node->prev;
		/* bp's previous' next is now dummy */
		(bp_node->prev)->next = dummy_ptr;

		/* For safety check */
		bp_node->next = NULL;
		bp_node->prev = NULL;
	}
	/* Case 4: This block is somewhere in the middle of the free list */
	else
	{
		/* Free List head does not change, free_listp stays the same */

		/* bp's next's previous is now bp's previous */
		(bp_node->next)->prev = bp_node->prev;

		/* bp's previous' next is now bp's next */
		(bp_node->prev)->next = bp_node->next;

		/* For safety check */
		bp_node->next = NULL;
		bp_node->prev = NULL;
	}
}


/* 
 * Requires:
 *   "bp" is the address of a free block that is at least "asize" bytes.
 *   "block" is the address of a free block already in the list.
 *
 * Effects:
 *   Insert a block into a circular doubly linked free list.
 */
void 
insert_circular(void *bp, void *block)
{
	/* Reduces repeated code. */
	struct seg_list *bp_node = (struct seg_list *)bp;
	struct seg_list *existing_node = (struct seg_list *)block;

	if (existing_node->next == existing_node && existing_node->prev == existing_node)
	{ 
		/* Dummy pointer points to itself when free list is empty */
		/* bp's next is the node to be inserted. */
		bp_node->next = existing_node;

		/* bp's prev is dummy because the list is circularly linked */
		bp_node->prev = existing_node;

		/* dummy's next is bp */
		existing_node->next = bp_node;

		/* dummy's prev is bp bc circular */
		existing_node->prev = bp_node;

	} /* Insert block at the beginning of the free list */
	else
	{
		/* bp's next is dummy's next */
		bp_node->next = existing_node->next;

		/* bp's previous is dummy */
		bp_node->prev = existing_node;

		/* dummy's next's previous (aka bp's next) is bp */
		(existing_node->next)->prev = bp_node;

		/* dummy's next is bp */
		existing_node->next = bp_node;
	}
	free_listp = bp;
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

	if ((uintptr_t)bp % DSIZE)
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
void 
checkheap(bool verbose)
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
	for (bp = free_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
	{
		if (verbose)
			printblock(bp);
		/* 
		 * Check if every block in the free list is marked as free
		 * and has not been allocated.
		 */
		if (GET_ALLOC(bp))
			printf("The block has been allocated, so it should" 
			" not appear in free list.\n");
		/* Check if there are any contiguous free blocks. */
		if (GET_SIZE(bp) > GET_SIZE(dummy_ptr))
			printf("The block escaped coalescing.");
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

	checkheap(false);
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