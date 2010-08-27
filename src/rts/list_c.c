
#include <stdlib.h>
#include <string.h>
#include "pyon_internal.h"

/*****************************************************************************/
/* defined in list.pyasm */

extern PyonList *
pyon_list_from_array(PyonWord n_elems, void *array);

extern void
pyon_list_to_array_POD(PyonWord elem_size, PyonWord elem_align,
		       PyonPtr copy, PyonPtr free,
		       PyonList *list, void *array);

extern PyonWord
pyon_list_length(PyonList *list);

extern PyonList *
pyon_list_copy_POD(PyonWord elem_size, PyonWord elem_align,
		   PyonPtr copy, PyonPtr free,
		   PyonList *list);

extern void
pyon_list_free_POD(PyonList *list);

/*****************************************************************************/

PyonList *
pyon_List_PyonInt_FromArray (int length, PyonInt *data) {
  /* Make a copy of the array */
  PyonInt *data_copy = pyon_alloc(length * SIZEOF_PYON_INT);
  memcpy(data_copy, data, length * SIZEOF_PYON_INT);

  /* Call the pyasm routine to create a list */
  return pyon_list_from_array(length, data_copy);
}

void
pyon_List_PyonInt_ToArray (PyonList *list, PyonInt *data) {
  pyon_list_to_array_POD (SIZEOF_PYON_INT, ALIGNOF_PYON_INT,
		          &pyon_copy_PyonInt, &dummy_finalizer,
			  list, data);
}

int
pyon_List_PyonInt_Length (PyonList *list) {
  return pyon_list_length(list);
}

PyonList *
pyon_List_PyonInt_Copy(PyonList *list) {
  return pyon_list_copy_POD(SIZEOF_PYON_INT, ALIGNOF_PYON_INT,
			    &pyon_copy_PyonInt, &dummy_finalizer,
			    list);
};

void
pyon_List_PyonInt_Free(PyonList *list) {
  pyon_list_free_POD(list);
};

