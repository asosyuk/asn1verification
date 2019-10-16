#include <stddef.h>

size_t strlen(const signed char *s)
{
  size_t i = 0;

  while(*s++)
      i++;

  return i;
}
