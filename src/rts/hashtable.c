
#include <stdint.h>
#include <string.h>

// Prime number used for hashing
#define HASH_PRIME 2166136261U

#define EMPTY (~0U)

static inline uint32_t
triolet_hash_calc(uint32_t size, int32_t key)
{
  return ((uint32_t)key * HASH_PRIME) & (size - 1);
}

static inline void
triolet_hash_insert(int32_t hash_size,
                    int32_t *hash_array,
                    uint32_t *collision_table,
                    int32_t key)
{
  // Actual hash function evaluation
  uint32_t hash_loc = triolet_hash_calc(hash_size, key);
  uint32_t old_hash_loc = hash_loc;

  // Collision detection strategy
  int collision = (hash_array[hash_loc] != -1);

  // Iterate to end of "linked list"
  while (collision_table[hash_loc] != EMPTY)
  {
    // If any element of this list is the element
    // we were looking for, then return because
    // the element has already been inserted
    if (hash_array[hash_loc] == key) return;
    
    old_hash_loc = hash_loc;
    hash_loc = collision_table[hash_loc];
  }

  // If the element has already been inserted
  // then return
  if (hash_array[hash_loc] == key) return;

  hash_loc = old_hash_loc;
  uint32_t last_link = hash_loc;

  // Scan around location for free location
  while (hash_array[hash_loc] != -1)
    hash_loc = (hash_loc + 1) & (hash_size - 1);

  hash_array[hash_loc] = key;

  // Store to linked list on collision
  if (collision) collision_table[last_link] = hash_loc;

}

void triolet_hash_build(int32_t hash_size,
                        int32_t *hash_array,
                        uint32_t *collision_table,
                        int32_t num_keys,
                        int32_t *key_array)
{
  memset(hash_array, -1, hash_size*sizeof(int32_t));
  memset(collision_table, EMPTY, hash_size*sizeof(uint32_t));

  int i;
  for(i = 0; i < num_keys; i++)
  {
    triolet_hash_insert(hash_size, hash_array, collision_table, key_array[i]);
  }
}

int32_t triolet_hash_lookup(int32_t hash_size,
                            int32_t *hash_table,
                            uint32_t *collision_table,
                            int32_t key)
{
  uint32_t hash_loc = triolet_hash_calc(hash_size, key);
  uint32_t orig_hash_loc = hash_loc;

  // Iterate to tail of linked list
  while(hash_table[hash_loc] != key)
  {
    orig_hash_loc = hash_loc;
    hash_loc = collision_table[hash_loc];
    if (hash_loc == EMPTY) break;
  }

  // Check if key exists there
  if (hash_table[orig_hash_loc] == -1) return -1;
  else return hash_table[orig_hash_loc];
  return key;
}

int32_t triolet_hash_size(int32_t keys_size)
{
  int highest_bit = 8*sizeof(int32_t) - 1;
  while( (keys_size & (1 << highest_bit)) == 0) highest_bit -= 1;
  return (1 << (highest_bit + 2));
}
