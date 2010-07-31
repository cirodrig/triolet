
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
