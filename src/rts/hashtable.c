#include <stdio.h>
#include <stdint.h>
#include <string.h>

/* A cursor, which is a pair of an object pointer and an interior pointer */
typedef struct
{
  void *object;
  void *interior;
} cursor;

// Hash tables consist of a hash array and a collision table.
// The hash array contains keys.
// The collision table has one full/empty bit (low bit)
// and the number of keys that hash to a given table entry
// in the upper bits.

// Prime number used for hashing
#define HASH_PRIME 3474692833U

#define EMPTY (~0U)

#define COLLISION_COUNT(n) ((n) >> 1)
#define COLLISION_FULL(n) ((n) & 1)
#define COLLISION_EMPTY(n) (!((n) & 1))
#define COLLISION_SET(ref) ((ref)++)

#define NEXT(i, size) ((i+1) & (size-1))

static inline uint32_t
indexing_hash(uint32_t size, int32_t key)
{
  return ((uint32_t)key * HASH_PRIME) & (size - 1);
}

static inline void
triolet_hash_insert(int32_t hash_size,
                    int32_t *hash_array,
                    uint32_t *collision_table,
                    int32_t key)
{
  uint32_t hash_val = indexing_hash(hash_size, key); // Hash value
  uint32_t occupancy = collision_table[hash_val] >> 1; // Number of colliding keys

  uint32_t count;               // number of colliding keys found
  uint32_t i;                   // hash table index

  // Search all keys in this hash bucket
  for (i = 0, count = 0; count < occupancy; i = NEXT(i, hash_size)) {
    // Skip empty entries
    if (COLLISION_EMPTY(collision_table[i])) continue;

    int32_t key2 = hash_array[i];
    if (key == key2) return;    // Key is already in table
    if (indexing_hash(hash_size, key2) == hash_val) count++;
  }

  // Find next available entry
  while (COLLISION_FULL(collision_table[i])) i = NEXT(i, hash_size);

  // Save key
  hash_array[i] = key;
  COLLISION_SET(collision_table[i]);

  // Update the count
  collision_table[hash_val] += 2;
}

void triolet_hash_build(int32_t hash_size,
                        int32_t *hash_array,
                        uint32_t *collision_table,
                        int32_t num_keys,
                        cursor key_array_cursor)
{
  int32_t *key_array = key_array_cursor.interior;

  //memset(hash_array, -1, hash_size*sizeof(int32_t));
  memset(collision_table, 0, hash_size*sizeof(uint32_t));

  int i;
  //printf("Build\n");
  for(i = 0; i < num_keys; i++)
  {
    //printf("%d ", key_array[i]);
    triolet_hash_insert(hash_size, hash_array, collision_table, key_array[i]);
  }
  //printf("\n");
  //for (i = 0; i < hash_size; i++)
  //  printf("%d\n", hash_array[i]);
}

uint32_t triolet_hash_lookup(int32_t hash_size,
                             cursor hash_table_cursor,
                             cursor collision_table_cursor,
                             int32_t key)
{
  int32_t *hash_table = hash_table_cursor.interior;
  uint32_t *collision_table = collision_table_cursor.interior;

  uint32_t hash_val = indexing_hash(hash_size, key); // Hash value
  uint32_t occupancy = collision_table[hash_val] >> 1; // Number of colliding keys

  uint32_t count;               // number of colliding keys found
  uint32_t i;                   // hash table index

  // Search all keys in this hash bucket
  for (i = 0, count = 0; count < occupancy; i = NEXT(i, hash_size)) {
    // Skip empty entries
    if (COLLISION_EMPTY(collision_table[i])) continue;

    int32_t key2 = hash_table[i];
    if (key == key2) return i;    // Found key
    if (indexing_hash(hash_size, key2) == hash_val) count++;
  }

  // Not found
  return EMPTY;
}

int32_t triolet_hash_size(int32_t keys_size)
{
  if (keys_size == 0) return 1;

  int highest_bit = 8*sizeof(int32_t) - 1;
  while( (keys_size & (1 << highest_bit)) == 0) highest_bit -= 1;
  return (1 << (highest_bit + 2));
}
