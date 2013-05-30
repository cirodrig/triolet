
#include <stdio.h>
#include "fp_interface.h"

int main(int argc, char **argv)
{
  Triolet_init(&argc, &argv);
  float x = f(77.77);		/* Result is 0.5 * 77.77 */
  float y = g(5.0/9.0);		/* Result is 1 */

  if (x < 38.8 || x > 38.9)
    printf ("Wrong x: %f", x);
  else if (y < 0.99 || y > 1.01)
    printf("Wrong y: %f", y);
  else
    printf("ok");

  return 0;
}
