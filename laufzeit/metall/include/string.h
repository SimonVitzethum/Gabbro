/* laufzeit/metall/include/string.h -- the <string.h> of the bare-metal image
 * (Opus agent J, 2026-09-26).
 *
 * Bounded strings (lane 261) emit `#include <string.h>` and call `memcpy` and
 * `memcmp`. <string.h> is not a freestanding header; the four memory
 * functions GCC may call even under `-fno-builtin` are defined by the runtime
 * itself (`kern.c`), byte by byte. This header declares exactly those four --
 * nothing of the C library's string half exists on bare metal, and a unit
 * that reached for more would fail the freestanding stage at compile time.
 */
#ifndef GABBRO_METALL_STRING_H
#define GABBRO_METALL_STRING_H

#include <stddef.h>

void *memcpy(void *d, const void *s, size_t n);
void *memmove(void *d, const void *s, size_t n);
void *memset(void *d, int c, size_t n);
int memcmp(const void *a, const void *b, size_t n);

#endif
