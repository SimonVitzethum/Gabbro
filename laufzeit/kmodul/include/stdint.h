/* laufzeit/kmodul/include/stdint.h -- <stdint.h> for a Gabbro unit inside a
 * Linux kernel module (server lane, TODO section 0e K4).
 *
 * WHY THIS FILE EXISTS. The kernel builds with `-nostdinc`: the C library's
 * headers are gone, on purpose, and the compiler's own freestanding <stdint.h>
 * is reached only under `-ffreestanding`, which a kernel object must not carry
 * (it turns off the builtins the kernel's own `memcpy`/`memset` lowering
 * relies on). Every emitted Gabbro unit includes <stdint.h> in its prelude.
 * So the kernel module supplies one -- over the kernel's OWN types, which is
 * the point: the widths a Gabbro program reasons about become the widths the
 * kernel already guarantees, by name, in one visible place.
 *
 * It provides exactly what the emitter lowers to. A unit that needs a name
 * this file does not have fails at compile time, loudly, rather than finding
 * it in some host header -- the same rule as `laufzeit/metall/include/math.h`.
 */
#ifndef GABBRO_KMOD_STDINT_H
#define GABBRO_KMOD_STDINT_H

#include <linux/types.h>
#include <linux/limits.h>

/* `linux/types.h` already defines int8_t … uint64_t under __KERNEL__; the
 * pins below are the promise the emitted C rests on, checked here once
 * instead of assumed everywhere. */
_Static_assert(sizeof(uint8_t) == 1, "uint8_t is one byte");
_Static_assert(sizeof(uint16_t) == 2, "uint16_t is two bytes");
_Static_assert(sizeof(uint32_t) == 4, "uint32_t is four bytes");
_Static_assert(sizeof(uint64_t) == 8, "uint64_t is eight bytes");

#ifndef UINT8_MAX
#define UINT8_MAX  0xffU
#endif
#ifndef UINT16_MAX
#define UINT16_MAX 0xffffU
#endif
#ifndef UINT32_MAX
#define UINT32_MAX 0xffffffffU
#endif
#ifndef UINT64_MAX
#define UINT64_MAX 0xffffffffffffffffULL
#endif
#ifndef INT8_MAX
#define INT8_MAX   0x7f
#define INT8_MIN   (-INT8_MAX - 1)
#endif
#ifndef INT16_MAX
#define INT16_MAX  0x7fff
#define INT16_MIN  (-INT16_MAX - 1)
#endif
#ifndef INT32_MAX
#define INT32_MAX  0x7fffffff
#define INT32_MIN  (-INT32_MAX - 1)
#endif
#ifndef INT64_MAX
#define INT64_MAX  0x7fffffffffffffffLL
#define INT64_MIN  (-INT64_MAX - 1)
#endif

#endif
