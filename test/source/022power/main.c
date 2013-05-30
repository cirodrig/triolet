
#include <stdio.h>
#include "mypower_interface.h"

int main(int argc, char **argv)
{
  Triolet_init(&argc, &argv);

	// Compute e ^ 7
	float f = mypow(2.71828, 7);
	printf("%d", (int) f);
	return 0;
}
