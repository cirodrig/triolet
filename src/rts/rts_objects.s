
/* The PAP info table */
.globl _pap_info
	.data
	.align 2
_pap_info:
	.long _free_pap		/* Free function */
	.byte 1			/* PAP tag */

/* The global closure info table */
.globl _closure_info
	.align 2
_closure_info:
	.long 0			/* Free function (never called) */
	.byte 0			/* Closure tag */

.globl _dealloc_closure
	.align 2
_dealloc_closure:
	.long 1			/* Reference count */
	.long _dealloc_info	/* Info table */

.globl _dealloc_info
	.align 2
_dealloc_info:
	.long 0			/* Free function (never called) */
	.byte 0			/* Function tag */
	.align 1
	.short 1, 0, 0		/* Arity, num captured, num recursive */
	.align 2
	.long _dealloc_exact_entry
	.long _dealloc_inexact_entry
	.byte 2			/* Int32Tag */

.globl _copy4_closure
	.align 2
_copy4_closure:
	.long 1			/* Reference count */
	.long _copy4_info	/* Info table */

.globl _copy4_info
	.align 2
_copy4_info:
	.long 0			/* Free function (never called) */
	.byte 0			/* Function tag */
	.align 1
	.short 2, 0, 0		/* Arity, num captured, num recursive */
	.align 2
	.long _copy4_exact_entry
	.long _copy4_inexact_entry
	.byte 2, 2		/* Int32Tag */
