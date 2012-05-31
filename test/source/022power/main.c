
#include <stdio.h>
#include "mypower_interface.h"

int main()
{
	Triolet_init();

	// Compute e ^ 7
	float f = mypower(2.71828, 7);
	printf("%d", (int) f);
	return 0;
}
