/* laufzeit/kmodul/include/stdbool.h -- <stdbool.h> inside a kernel module.
 * The kernel has `bool`, `true` and `false` already (`linux/types.h`,
 * `linux/stddef.h`); this file is the name the emitted prelude asks for.
 * See `stdint.h` beside it for why the compiler's own copy is out of reach. */
#ifndef GABBRO_KMOD_STDBOOL_H
#define GABBRO_KMOD_STDBOOL_H
#include <linux/types.h>
#include <linux/stddef.h>
#endif
