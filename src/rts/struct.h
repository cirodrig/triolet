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

/* Get the size of a data type represented by the bits tag */
#define TYPE_TAG_SIZE(t) ((int)type_tag_sizealign_array[(int)(t)].size)

/* Get the alignment of a data type represented by the bits tag */
#define TYPE_TAG_ALIGN(t) ((int)type_tag_sizealign_array[(int)(t)].align)

#define BITS_TAG_SIZE(t) ((int)bits_tag_size_array[(int)(t)])

/* Add the minimum amount to 'offset' necessary to get a value divisible by
 * 'alignment'.  The offset and alignment must be positive. */
static inline int
align(int offset, int alignment)
{
  // compute offset % alignment using round-to-minus-infinity
  int adjustment = offset % alignment +
    ((offset >= 0) == (alignment >= 0) ? 0 : alignment);
  return offset + adjustment;
}

/* A lookup table of the sizes and alignments of primitive types */
struct tag_sizealign_t
{
  char size;
  char align;
};

extern const struct tag_sizealign_t type_tag_sizealign_array[];
extern const char bits_tag_size_array[];

