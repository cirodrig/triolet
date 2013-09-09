#include <gc.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

// Hash tables consist of a hash array and a collision table.
// The hash array contains keys.
// The collision table has one full/empty bit (low bit)
// and the number of keys that hash to a given table entry
// in the upper bits.

// Prime number used for hashing

#define HASH_PRIME 3474692833U

// Number of elements allocated for an empty hash table
#define INITIAL_SIZE 64

#define EMPTY (~0U)

#define COLLISION_COUNT(n) ((n) >> 1)
#define COLLISION_FULL(n) ((n) & 1)
#define COLLISION_EMPTY(n) (!((n) & 1))
#define COLLISION_SET(ref) ((ref)++)

#define NEXT(i, size) ((i+1) & (size-1))

typedef struct st_hash_element_t {
  intptr_t _key;
  intptr_t _val;
} hash_element_t;

#define hash_element_getKey(elem)           ((elem)._key)
#define hash_element_getValue(elem)         ((elem)._val)

#define hash_element_setKey(elem, val)      (hash_element_getKey(elem) = val)
#define hash_element_setValue(elem, val)    (hash_element_getValue(elem) = val)

// A hash table with linear probing.
// The table is resized if it becomes 50% full so that it stays
// between 25% and 50% full.
typedef struct st_hash_p_t {
  // A collision table.
  // Each entry has one full/empty bit (low bit) indicating whether the
  // corresponding hash table element holds a valid value.
  // The upper bits hold the number of keys that hash to a given table entry.
  uint32_t * _collisions;

  // Hash table entries
  hash_element_t * _elements;

  // Length of the _collisions and _elements arrays
  int64_t _elementCount;

  // Number of entries stored in the hash table
  int64_t _len;
} * hash_t;

#define hash_getCollisions(ha)        ((ha)->_collisions)
#define hash_getCollision(ha, ii)     (hash_getCollisions(ha)[ii])
#define hash_getElements(ha)          ((ha)->_elements)
#define hash_getElement(ha, ii)       (hash_getElements(ha)[ii])
#define hash_getArraySize(ha)      ((ha)->_elementCount)
#define hash_getLength(ha)            ((ha)->_len)

#define hash_setCollisions(ha, val)   (hash_getCollisions(ha) = val)
#define hash_setCollision(ha, ii, val) (hash_getCollision(ha, ii) = val)
#define hash_setElements(ha, val)     (hash_getElements(ha) = val)
#define hash_setElement(ha, ii, val)  (hash_getElement(ha, ii) = val)
#define hash_setArraySize(ha, val) (hash_getArraySize(ha) = val)
#define hash_setLength(ha, val)       (hash_getLength(ha) = val)

/* Allocate a pointer-free array and fill with zeros */
static inline void *
malloc_atomic_zeroed(int size)
{
  void *p = GC_MALLOC_ATOMIC(size);
  memset(p, 0, size);
  return p;
}

/* FNV hashing function */
static inline uint32_t
indexing_hash(uint32_t size, intptr_t key)
{
  return ((uint64_t)key * HASH_PRIME) & (size - 1);
}

/* Choose a hash table size large enough to hold all keys.
 * Size is chosen so that table is 1/4 to 1/2 full. */
int32_t triolet_hash_size(int32_t keys_size)
{
  if (keys_size == 0) return 1;

  int highest_bit = 8*sizeof(int32_t) - 1;
  while( (keys_size & (1 << highest_bit)) == 0) highest_bit -= 1;
  return (1 << (highest_bit + 2));
}

/* Create a new hash table of the given length */
hash_t
triolet_hash_new(void) {
  int len = INITIAL_SIZE;
  hash_t hash = (hash_t) GC_MALLOC(sizeof(struct st_hash_p_t));

  hash_setCollisions(hash, malloc_atomic_zeroed(len * sizeof(uint32_t)));
  hash_setElements(hash, GC_MALLOC(len * sizeof(hash_element_t)));
  hash_setArraySize(hash, len);
  hash_setLength(hash, 0);
  return hash;
}

/* Free a hash table */
static inline void
triolet_hash_delete(hash_t hash) {
  if (hash != NULL) {
    GC_FREE(hash_getCollisions(hash));
    GC_FREE(hash_getElements(hash));
    GC_FREE(hash);
  }
  return ;
}


static void triolet_hash_rehash(hash_t hash);


// Insert a key-value pair into the hash table
static void
triolet_hash_insert(hash_t hash,
                    intptr_t key,
                    intptr_t val)
{
  int64_t hash_size = hash_getArraySize(hash);
  uint32_t hash_val = indexing_hash(hash_size, key); // Hash value
  uint32_t occupancy = hash_getCollision(hash, hash_val) >> 1; // Number of colliding keys

  uint32_t count;               // number of colliding keys found
  uint32_t i;                   // hash table index

  // Search all keys in this hash bucket
  for (i = 0, count = 0; count < occupancy; i = NEXT(i, hash_size)) {
    // Skip empty entries
    if (COLLISION_EMPTY(hash_getCollision(hash, i))) continue;

    intptr_t key2 = hash_element_getKey(hash_getElement(hash, i));
    if (key == key2) return;    // Key is already in table
    if (indexing_hash(hash_size, key2) == hash_val) count++;
  }

  // Find next available entry
  while (COLLISION_FULL(hash_getCollision(hash, i))) i = NEXT(i, hash_size);

  // Save key
  hash_element_setKey(hash_getElement(hash, i), key);
  hash_element_setValue(hash_getElement(hash, i), val);
  COLLISION_SET(hash_getCollision(hash, i));

  // Update the count
  hash_getCollision(hash, hash_val) += 2;
  hash_getLength(hash)++;

  // If the hash table is 50% full, then resize the hash table
  if (2 * hash_getLength(hash) == hash_getArraySize(hash)) {
    triolet_hash_rehash(hash);
  }
}

void
triolet_hash_insert_intptr(hash_t hash,
                           int32_t key,
                           void * val)
{
  triolet_hash_insert(hash, (intptr_t)key, (intptr_t) val);
}

void
triolet_hash_insert_ptrint(hash_t hash,
                           void * key,
                           int32_t val)
{
  triolet_hash_insert(hash, (intptr_t)key, (intptr_t) val);
}

// Increase a hash table's size by a factor of 2.
// Copy elements from the old to the new hash table.
static void
triolet_hash_rehash(hash_t hash) {
  int64_t ii;
  int64_t newCount;
  int64_t oldCount;
  uint32_t * oldCollisionTable;
  hash_element_t * oldElements;

  // Extract old hash table data
  oldCount = hash_getArraySize(hash);
  oldCollisionTable = hash_getCollisions(hash);
  oldElements = hash_getElements(hash);

  newCount = 2 * oldCount;

  // Create new hash table data
  hash_setCollisions(hash, malloc_atomic_zeroed(newCount * sizeof(uint32_t)));
  hash_setElements(hash, GC_MALLOC(newCount * sizeof(hash_element_t)));
  hash_setArraySize(hash, newCount);
  hash_setLength(hash, 0);      // New table is initially empty

  // Move all entries from old to new hash table
  for (ii = 0; ii < oldCount; ii++) {
    if (COLLISION_FULL(oldCollisionTable[ii])) {
      hash_element_t elem = oldElements[ii];
      triolet_hash_insert(hash,
                          hash_element_getKey(elem),
                          hash_element_getValue(elem));
    }
  }

  GC_FREE(oldCollisionTable);
  GC_FREE(oldElements);
}

// Look up a hash key.  Return (~0) if not found.
intptr_t
triolet_hash_lookup(hash_t hash,
                    intptr_t key)
{

  int64_t hash_size = hash_getArraySize(hash);
  uint32_t hash_val = indexing_hash(hash_size, key); // Hash value
  uint32_t occupancy = hash_getCollision(hash, hash_val) >> 1; // Number of colliding keys

  uint32_t count;               // number of colliding keys found
  uint32_t i;                   // hash table index

  // Search all keys in this hash bucket
  for (i = 0, count = 0; count < occupancy; i = NEXT(i, hash_size)) {
    // Skip empty entries
    if (COLLISION_EMPTY(hash_getCollision(hash, i))) continue;

    intptr_t key2 = hash_element_getKey(hash_getElement(hash, i));
    if (key == key2) return hash_element_getValue(hash_getElement(hash, i));    // Key is already in table
    if (indexing_hash(hash_size, key2) == hash_val) count++;
  }

  // Not found
  return EMPTY;
}

int32_t
triolet_hash_lookup_ptr(hash_t hash, void *key)
{
  return (int32_t) triolet_hash_lookup(hash, (intptr_t) key);
}

void *
triolet_hash_lookup_int(hash_t hash, int32_t key)
{
  intptr_t ret = triolet_hash_lookup(hash, (intptr_t) key);
  // Use NULL as the token for a missing value
  if (ret == EMPTY) return NULL;
  return (void *) ret;
}


/* TESTING CODE */
#if 0

static inline int assertTrue(const char * stmt, const char * test, int val) {
  if (val == 0) {
    printf("ASSERT FAILED(%s): %s\n", test, stmt);
    return 1;
  }
  return 0;
}


#define ASSERT_TRUE(stmt)       assertTrue(#stmt, _test, stmt)
#define ASSERT_FALSE(stmt)      assertTrue(#stmt, _test, !(stmt))
#define BEGIN_TEST(msg)         static void msg () {\
                                const char * _test = #msg; \
                                printf("Running test: %s\n", #msg);
#define END_TEST(msg)           }
#define RUN_TEST(msg)           msg()

BEGIN_TEST(CanCreateHash)
    hash_t hash = triolet_hash_new();
    ASSERT_TRUE(hash != NULL);
    ASSERT_TRUE(hash_getLength(hash) == 0);
    triolet_hash_delete(hash);
END_TEST(CanCreateHash)

BEGIN_TEST(CanInsertHash)
    int key0 = 1, key1 = 2;
    hash_t hash = triolet_hash_new();

    triolet_hash_insert(hash, &key0, key0);
    ASSERT_TRUE(hash_getLength(hash) == 1);

    triolet_hash_insert(hash, &key1, key1);
    ASSERT_TRUE(hash_getLength(hash) == 2);

    triolet_hash_delete(hash);
END_TEST(CanInsertHash)

BEGIN_TEST(CanLookup)
    int key0 = 1, key1 = 2, key3 = 3;
    hash_t hash = triolet_hash_new();

    triolet_hash_insert(hash, &key0, key0);
    triolet_hash_insert(hash, &key1, key1);

    ASSERT_TRUE(triolet_hash_lookup(hash, &key0) == key0);
    ASSERT_TRUE(triolet_hash_lookup(hash, &key1) == key1);

    ASSERT_FALSE(triolet_hash_lookup(hash, &key3) == key3);
    ASSERT_TRUE(triolet_hash_lookup(hash, &key3) == EMPTY);

    triolet_hash_insert(hash, &key3, key3);
    ASSERT_TRUE(triolet_hash_lookup(hash, &key3) == key3);

    triolet_hash_delete(hash);
END_TEST(CanLookup)

BEGIN_TEST(CanReHash)
    void * key;
    size_t ii;

    hash_t hash = triolet_hash_new();
    int len = hash_getArraySize(hash);

    for (ii = 0; ii < 2*len; ii++) {
        key = (void *) ii;
        triolet_hash_insert(hash, key, ii);
        ASSERT_TRUE(triolet_hash_lookup(hash, key) == ii);
        ASSERT_TRUE(hash_getLength(hash) == ii+1);
    }

    ASSERT_TRUE(hash_getArraySize(hash) != len);

    triolet_hash_delete(hash);
END_TEST(CanReHash)

int main() {
    RUN_TEST(CanCreateHash);
    RUN_TEST(CanInsertHash);
    RUN_TEST(CanLookup);
    RUN_TEST(CanReHash);
    return ;
}

#endif  /* TESTING */
