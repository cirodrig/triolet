
/* The PAP info table */
.globl _pap_info
	.data
	.align 2
_pap_info:
	.long _free_pap		/* Free function */
	.byte 1			/* PAP tag */

