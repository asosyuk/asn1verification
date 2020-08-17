#include "unistd.h"

int dummy(const void *buffer, size_t size, void *application_specific_key) {
  return (size == 0) ? -1 : size;
}
