/* laufzeit/kmodul/include/stddef.h -- <stddef.h> inside a kernel module:
 * `size_t`, `NULL`, `offsetof`, all the kernel's own (`linux/stddef.h`,
 * `linux/types.h`). See `stdint.h` beside it for why the compiler's copy is
 * out of reach under the kernel's `-nostdinc`. */
#ifndef GABBRO_KMOD_STDDEF_H
#define GABBRO_KMOD_STDDEF_H
#include <linux/types.h>
#include <linux/stddef.h>
#endif
