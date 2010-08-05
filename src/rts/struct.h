/*
 * Data structure access
 */

/* Get the alignment of a data type */
#define ALIGNOF(type) __alignof__(type)

/* Get the starting offset of a structure field with the given type,
 * located at the first suitable offset not less than 'offset'. */ 
#define FIELD_START_OFF(offset, type) \
  (align((offset), ALIGNOF(type)))

/* Get the ending offset of a structure field with the given type,
 * located at the first suitable offset not less than 'offset'.
 * This offset is exactly (start + size).
 */
#define FIELD_END_OFF(offset, type) \
  (FIELD_START_OFF((offset), (type)) + sizeof(type))

/* Get the size of a data type represented by the tag */
#define TAG_SIZE(t) ((int)tag_sizealign_array[(int)(t)].size)

/* Get the alignment of a data type represented by the tag */
#define TAG_ALIGN(t) ((int)tag_sizealign_array[(int)(t)].align)

/* Add the minimum amount to 'offset' necessary to get a value divisible by
 * 'alignment'.  The offset and alignment must be positive. */
static inline int
align(int offset, int alignment)
{
  return offset + (offset - alignment) % offset;
}

/* A lookup table of the sizes and alignments of primitive types */
struct tag_sizealign_t
{
  char size;
  char align;
};

extern const struct tag_sizealign_t tag_sizealign_array[];

