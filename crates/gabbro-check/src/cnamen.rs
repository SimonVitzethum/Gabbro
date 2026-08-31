//! **The names C has already taken -- measured, not assumed.**
//!
//! The generator writes the Gabbro name into C UNCHANGED: there is no `fn c_name` in
//! `emit.rs`, no module prefix, no escape form. What stands in Gabbro stands in C. So every
//! name C owns is a name a lowering cannot use, and the checker is the place that says so --
//! not `cc`, three tools later, in a language the writer never asked about.
//!
//! **The table is a measurement of 2026-08-31**, and `messung/C-NAMEN.md` carries the command
//! for every line of it. Three classes, and they are not the same kind of thing:
//!
//! | class | count | how it was measured |
//! |---|---:|---|
//! | `Klasse::Wort` -- a C11 keyword | 37 | C11 §6.4.1, minus the 7 that Gabbro's own vocabulary already refuses at `P002` |
//! | `Klasse::Header` -- provided by one of the four headers every generated unit includes | 366 | `cc -dM -E`, `cc -aux-info` and a `typedef` scan over `<stdint.h> <stdbool.h> <stdatomic.h> <math.h>` |
//! | `Klasse::Eingebaut` -- a built-in function of the C implementation | 155 | one file per candidate, WITHOUT any `#include`, refused with *built-in function* |
//!
//! **The third class is the one that caught `F05`, and it is the unsettling one: it works
//! without a single `#include`.** `exit` is not declared by any header the generator writes,
//! and `cc` still refuses `_Noreturn void exit(void);`.
//!
//! > **What this table deliberately does NOT carry.** C11 §7.1.3 reserves every identifier
//! > that starts with `_` and an upper-case letter, and every one that starts with `__`.
//! > *Measured: none of them breaks* -- `__builtin_x`, `_Grosz` and `_klein` all compile, and
//! > the corpus holds zero item names with a leading underscore in 743. **Rule A: no construct
//! > without a measured need.** The 883 underscore names the four headers do define
//! > (`_STDINT_H`, `__GLIBC__`, …) are one libc's spelling and not C's; a list that carries
//! > them measures glibc and calls it C.

/// Which side of C took the name -- the refusal names it, because the writer cannot see it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Klasse {
    /// A keyword of C11 §6.4.1. The generated unit cannot spell it as a name at all.
    Wort,
    /// Provided by one of the four headers every generated unit includes.
    Header(&'static str),
    /// A built-in function of the C implementation -- known without any `#include`.
    Eingebaut,
}

impl Klasse {
    /// The sentence that names the finding site. **A user who writes `fn exit()` did nothing
    /// wrong** -- they only do not know the lowering goes to C. A refusal that does not say
    /// so moves an explanation into an error list.
    pub fn fundort(self, name: &str) -> String {
        match self {
            Klasse::Wort => format!("`{name}` is a keyword of C11 §6.4.1"),
            Klasse::Header(h) => format!(
                "`{name}` comes from `<{h}>`, and EVERY generated unit includes it"
            ),
            Klasse::Eingebaut => format!(
                "`{name}` is a built-in function of the C implementation -- \
                 `cc` knows it without any `#include`"
            ),
        }
    }
}

/// **The lookup.** `None` means C has not taken the name.
///
/// The three tables are sorted, and the order is asserted by a probe -- a binary search over a
/// table that has slipped out of order answers `None` for a name that IS taken, and that is a
/// false green in the only direction that matters here.
pub fn vergeben(name: &str) -> Option<Klasse> {
    if C11_WORT.binary_search(&name).is_ok() {
        return Some(Klasse::Wort);
    }
    if let Ok(i) = HEADER.binary_search_by_key(&name, |(n, _)| n) {
        return Some(Klasse::Header(HEADER[i].1));
    }
    if EINGEBAUT.binary_search(&name).is_ok() {
        return Some(Klasse::Eingebaut);
    }
    None
}

/// How many names the table carries -- read by the probe, so the number has one home.
pub fn umfang() -> (usize, usize, usize) {
    (C11_WORT.len(), HEADER.len(), EINGEBAUT.len())
}

/// C11 §6.4.1, minus `const else extern if return sizeof static` -- those are words of
/// Gabbro's own vocabulary and never reach a name (`P002`).
static C11_WORT: [&str; 37] = [
    "_Alignas", "_Alignof", "_Atomic", "_Bool", "_Complex", "_Generic", "_Imaginary",
    "_Noreturn", "_Static_assert", "_Thread_local", "auto", "break", "case", "char",
    "continue", "default", "do", "double", "enum", "float", "for", "goto", "inline", "int",
    "long", "register", "restrict", "short", "signed", "struct", "switch", "typedef", "union",
    "unsigned", "void", "volatile", "while",
];

/// What `<stdint.h>`, `<stdbool.h>`, `<stdatomic.h>` and `<math.h>` put in scope, without the
/// underscore names. Per name the header that carries it -- the refusal names the file.
static HEADER: [(&str, &str); 366] = [
    ("ATOMIC_BOOL_LOCK_FREE", "stdatomic.h"), ("ATOMIC_CHAR16_T_LOCK_FREE", "stdatomic.h"),
    ("ATOMIC_CHAR32_T_LOCK_FREE", "stdatomic.h"), ("ATOMIC_CHAR_LOCK_FREE", "stdatomic.h"),
    ("ATOMIC_FLAG_INIT", "stdatomic.h"), ("ATOMIC_INT_LOCK_FREE", "stdatomic.h"),
    ("ATOMIC_LLONG_LOCK_FREE", "stdatomic.h"), ("ATOMIC_LONG_LOCK_FREE", "stdatomic.h"),
    ("ATOMIC_POINTER_LOCK_FREE", "stdatomic.h"), ("ATOMIC_SHORT_LOCK_FREE", "stdatomic.h"),
    ("ATOMIC_VAR_INIT", "stdatomic.h"), ("ATOMIC_WCHAR_T_LOCK_FREE", "stdatomic.h"),
    ("FP_ILOGB0", "math.h"), ("FP_ILOGBNAN", "math.h"), ("FP_INFINITE", "math.h"),
    ("FP_NAN", "math.h"), ("FP_NORMAL", "math.h"), ("FP_SUBNORMAL", "math.h"),
    ("FP_ZERO", "math.h"), ("HUGE_VAL", "math.h"), ("HUGE_VALF", "math.h"),
    ("HUGE_VALL", "math.h"), ("INFINITY", "math.h"), ("INT16_C", "stdint.h"),
    ("INT16_MAX", "stdint.h"), ("INT16_MIN", "stdint.h"), ("INT32_C", "stdint.h"),
    ("INT32_MAX", "stdint.h"), ("INT32_MIN", "stdint.h"), ("INT64_C", "stdint.h"),
    ("INT64_MAX", "stdint.h"), ("INT64_MIN", "stdint.h"), ("INT8_C", "stdint.h"),
    ("INT8_MAX", "stdint.h"), ("INT8_MIN", "stdint.h"), ("INTMAX_C", "stdint.h"),
    ("INTMAX_MAX", "stdint.h"), ("INTMAX_MIN", "stdint.h"), ("INTPTR_MAX", "stdint.h"),
    ("INTPTR_MIN", "stdint.h"), ("INT_FAST16_MAX", "stdint.h"),
    ("INT_FAST16_MIN", "stdint.h"), ("INT_FAST32_MAX", "stdint.h"),
    ("INT_FAST32_MIN", "stdint.h"), ("INT_FAST64_MAX", "stdint.h"),
    ("INT_FAST64_MIN", "stdint.h"), ("INT_FAST8_MAX", "stdint.h"),
    ("INT_FAST8_MIN", "stdint.h"), ("INT_LEAST16_MAX", "stdint.h"),
    ("INT_LEAST16_MIN", "stdint.h"), ("INT_LEAST32_MAX", "stdint.h"),
    ("INT_LEAST32_MIN", "stdint.h"), ("INT_LEAST64_MAX", "stdint.h"),
    ("INT_LEAST64_MIN", "stdint.h"), ("INT_LEAST8_MAX", "stdint.h"),
    ("INT_LEAST8_MIN", "stdint.h"), ("MATH_ERREXCEPT", "math.h"), ("MATH_ERRNO", "math.h"),
    ("NAN", "math.h"), ("PTRDIFF_MAX", "stdint.h"), ("PTRDIFF_MIN", "stdint.h"),
    ("SIG_ATOMIC_MAX", "stdint.h"), ("SIG_ATOMIC_MIN", "stdint.h"), ("SIZE_MAX", "stdint.h"),
    ("UINT16_C", "stdint.h"), ("UINT16_MAX", "stdint.h"), ("UINT32_C", "stdint.h"),
    ("UINT32_MAX", "stdint.h"), ("UINT64_C", "stdint.h"), ("UINT64_MAX", "stdint.h"),
    ("UINT8_C", "stdint.h"), ("UINT8_MAX", "stdint.h"), ("UINTMAX_C", "stdint.h"),
    ("UINTMAX_MAX", "stdint.h"), ("UINTPTR_MAX", "stdint.h"), ("UINT_FAST16_MAX", "stdint.h"),
    ("UINT_FAST32_MAX", "stdint.h"), ("UINT_FAST64_MAX", "stdint.h"),
    ("UINT_FAST8_MAX", "stdint.h"), ("UINT_LEAST16_MAX", "stdint.h"),
    ("UINT_LEAST32_MAX", "stdint.h"), ("UINT_LEAST64_MAX", "stdint.h"),
    ("UINT_LEAST8_MAX", "stdint.h"), ("WCHAR_MAX", "stdint.h"), ("WCHAR_MIN", "stdint.h"),
    ("WINT_MAX", "stdint.h"), ("WINT_MIN", "stdint.h"), ("acos", "math.h"),
    ("acosf", "math.h"), ("acosh", "math.h"), ("acoshf", "math.h"), ("acoshl", "math.h"),
    ("acosl", "math.h"), ("asin", "math.h"), ("asinf", "math.h"), ("asinh", "math.h"),
    ("asinhf", "math.h"), ("asinhl", "math.h"), ("asinl", "math.h"), ("atan", "math.h"),
    ("atan2", "math.h"), ("atan2f", "math.h"), ("atan2l", "math.h"), ("atanf", "math.h"),
    ("atanh", "math.h"), ("atanhf", "math.h"), ("atanhl", "math.h"), ("atanl", "math.h"),
    ("atomic_bool", "stdatomic.h"), ("atomic_char", "stdatomic.h"),
    ("atomic_char16_t", "stdatomic.h"), ("atomic_char32_t", "stdatomic.h"),
    ("atomic_compare_exchange_strong", "stdatomic.h"),
    ("atomic_compare_exchange_strong_explicit", "stdatomic.h"),
    ("atomic_compare_exchange_weak", "stdatomic.h"),
    ("atomic_compare_exchange_weak_explicit", "stdatomic.h"),
    ("atomic_exchange", "stdatomic.h"), ("atomic_exchange_explicit", "stdatomic.h"),
    ("atomic_fetch_add", "stdatomic.h"), ("atomic_fetch_add_explicit", "stdatomic.h"),
    ("atomic_fetch_and", "stdatomic.h"), ("atomic_fetch_and_explicit", "stdatomic.h"),
    ("atomic_fetch_or", "stdatomic.h"), ("atomic_fetch_or_explicit", "stdatomic.h"),
    ("atomic_fetch_sub", "stdatomic.h"), ("atomic_fetch_sub_explicit", "stdatomic.h"),
    ("atomic_fetch_xor", "stdatomic.h"), ("atomic_fetch_xor_explicit", "stdatomic.h"),
    ("atomic_flag_clear", "stdatomic.h"), ("atomic_flag_clear_explicit", "stdatomic.h"),
    ("atomic_flag_test_and_set", "stdatomic.h"),
    ("atomic_flag_test_and_set_explicit", "stdatomic.h"), ("atomic_init", "stdatomic.h"),
    ("atomic_int", "stdatomic.h"), ("atomic_int_fast16_t", "stdatomic.h"),
    ("atomic_int_fast32_t", "stdatomic.h"), ("atomic_int_fast64_t", "stdatomic.h"),
    ("atomic_int_fast8_t", "stdatomic.h"), ("atomic_int_least16_t", "stdatomic.h"),
    ("atomic_int_least32_t", "stdatomic.h"), ("atomic_int_least64_t", "stdatomic.h"),
    ("atomic_int_least8_t", "stdatomic.h"), ("atomic_intmax_t", "stdatomic.h"),
    ("atomic_intptr_t", "stdatomic.h"), ("atomic_is_lock_free", "stdatomic.h"),
    ("atomic_llong", "stdatomic.h"), ("atomic_load", "stdatomic.h"),
    ("atomic_load_explicit", "stdatomic.h"), ("atomic_long", "stdatomic.h"),
    ("atomic_ptrdiff_t", "stdatomic.h"), ("atomic_schar", "stdatomic.h"),
    ("atomic_short", "stdatomic.h"), ("atomic_signal_fence", "stdatomic.h"),
    ("atomic_size_t", "stdatomic.h"), ("atomic_store", "stdatomic.h"),
    ("atomic_store_explicit", "stdatomic.h"), ("atomic_thread_fence", "stdatomic.h"),
    ("atomic_uchar", "stdatomic.h"), ("atomic_uint", "stdatomic.h"),
    ("atomic_uint_fast16_t", "stdatomic.h"), ("atomic_uint_fast32_t", "stdatomic.h"),
    ("atomic_uint_fast64_t", "stdatomic.h"), ("atomic_uint_fast8_t", "stdatomic.h"),
    ("atomic_uint_least16_t", "stdatomic.h"), ("atomic_uint_least32_t", "stdatomic.h"),
    ("atomic_uint_least64_t", "stdatomic.h"), ("atomic_uint_least8_t", "stdatomic.h"),
    ("atomic_uintmax_t", "stdatomic.h"), ("atomic_uintptr_t", "stdatomic.h"),
    ("atomic_ullong", "stdatomic.h"), ("atomic_ulong", "stdatomic.h"),
    ("atomic_ushort", "stdatomic.h"), ("atomic_wchar_t", "stdatomic.h"), ("cbrt", "math.h"),
    ("cbrtf", "math.h"), ("cbrtl", "math.h"), ("ceil", "math.h"), ("ceilf", "math.h"),
    ("ceill", "math.h"), ("copysign", "math.h"), ("copysignf", "math.h"),
    ("copysignl", "math.h"), ("cos", "math.h"), ("cosf", "math.h"), ("cosh", "math.h"),
    ("coshf", "math.h"), ("coshl", "math.h"), ("cosl", "math.h"), ("double_t", "math.h"),
    ("erf", "math.h"), ("erfc", "math.h"), ("erfcf", "math.h"), ("erfcl", "math.h"),
    ("erff", "math.h"), ("erfl", "math.h"), ("exp", "math.h"), ("exp2", "math.h"),
    ("exp2f", "math.h"), ("exp2l", "math.h"), ("expf", "math.h"), ("expl", "math.h"),
    ("expm1", "math.h"), ("expm1f", "math.h"), ("expm1l", "math.h"), ("fabs", "math.h"),
    ("fabsf", "math.h"), ("fabsl", "math.h"), ("fdim", "math.h"), ("fdimf", "math.h"),
    ("fdiml", "math.h"), ("float_t", "math.h"), ("floorf", "math.h"), ("floorl", "math.h"),
    ("fma", "math.h"), ("fmaf", "math.h"), ("fmal", "math.h"), ("fmax", "math.h"),
    ("fmaxf", "math.h"), ("fmaxl", "math.h"), ("fmin", "math.h"), ("fminf", "math.h"),
    ("fminl", "math.h"), ("fmod", "math.h"), ("fmodf", "math.h"), ("fmodl", "math.h"),
    ("fpclassify", "math.h"), ("frexp", "math.h"), ("frexpf", "math.h"), ("frexpl", "math.h"),
    ("hypot", "math.h"), ("hypotf", "math.h"), ("hypotl", "math.h"), ("ilogb", "math.h"),
    ("ilogbf", "math.h"), ("ilogbl", "math.h"), ("int16_t", "stdint.h"),
    ("int32_t", "stdint.h"), ("int64_t", "stdint.h"), ("int8_t", "stdint.h"),
    ("int_fast16_t", "stdint.h"), ("int_fast32_t", "stdint.h"), ("int_fast64_t", "stdint.h"),
    ("int_fast8_t", "stdint.h"), ("int_least16_t", "stdint.h"), ("int_least32_t", "stdint.h"),
    ("int_least64_t", "stdint.h"), ("int_least8_t", "stdint.h"), ("intmax_t", "stdint.h"),
    ("intptr_t", "stdint.h"), ("isfinite", "math.h"), ("isgreater", "math.h"),
    ("isgreaterequal", "math.h"), ("isinf", "math.h"), ("isless", "math.h"),
    ("islessequal", "math.h"), ("islessgreater", "math.h"), ("isnan", "math.h"),
    ("isnormal", "math.h"), ("isunordered", "math.h"), ("kill_dependency", "stdatomic.h"),
    ("ldexp", "math.h"), ("ldexpf", "math.h"), ("ldexpl", "math.h"), ("lgamma", "math.h"),
    ("lgammaf", "math.h"), ("lgammal", "math.h"), ("llrint", "math.h"), ("llrintf", "math.h"),
    ("llrintl", "math.h"), ("llround", "math.h"), ("llroundf", "math.h"),
    ("llroundl", "math.h"), ("log", "math.h"), ("log10", "math.h"), ("log10f", "math.h"),
    ("log10l", "math.h"), ("log1p", "math.h"), ("log1pf", "math.h"), ("log1pl", "math.h"),
    ("log2", "math.h"), ("log2f", "math.h"), ("log2l", "math.h"), ("logb", "math.h"),
    ("logbf", "math.h"), ("logbl", "math.h"), ("logf", "math.h"), ("logl", "math.h"),
    ("lrint", "math.h"), ("lrintf", "math.h"), ("lrintl", "math.h"), ("lround", "math.h"),
    ("lroundf", "math.h"), ("lroundl", "math.h"), ("math_errhandling", "math.h"),
    ("modf", "math.h"), ("modff", "math.h"), ("modfl", "math.h"), ("nan", "math.h"),
    ("nanf", "math.h"), ("nanl", "math.h"), ("nearbyint", "math.h"), ("nearbyintf", "math.h"),
    ("nearbyintl", "math.h"), ("nextafter", "math.h"), ("nextafterf", "math.h"),
    ("nextafterl", "math.h"), ("nexttoward", "math.h"), ("nexttowardf", "math.h"),
    ("nexttowardl", "math.h"), ("pow", "math.h"), ("powf", "math.h"), ("powl", "math.h"),
    ("remainder", "math.h"), ("remainderf", "math.h"), ("remainderl", "math.h"),
    ("remquo", "math.h"), ("remquof", "math.h"), ("remquol", "math.h"), ("rint", "math.h"),
    ("rintf", "math.h"), ("rintl", "math.h"), ("round", "math.h"), ("roundf", "math.h"),
    ("roundl", "math.h"), ("scalbln", "math.h"), ("scalblnf", "math.h"),
    ("scalblnl", "math.h"), ("scalbn", "math.h"), ("scalbnf", "math.h"),
    ("scalbnl", "math.h"), ("signbit", "math.h"), ("sin", "math.h"), ("sinf", "math.h"),
    ("sinh", "math.h"), ("sinhf", "math.h"), ("sinhl", "math.h"), ("sinl", "math.h"),
    ("sqrt", "math.h"), ("sqrtf", "math.h"), ("sqrtl", "math.h"), ("tan", "math.h"),
    ("tanf", "math.h"), ("tanh", "math.h"), ("tanhf", "math.h"), ("tanhl", "math.h"),
    ("tanl", "math.h"), ("tgamma", "math.h"), ("tgammaf", "math.h"), ("tgammal", "math.h"),
    ("trunc", "math.h"), ("truncf", "math.h"), ("truncl", "math.h"), ("uint16_t", "stdint.h"),
    ("uint32_t", "stdint.h"), ("uint64_t", "stdint.h"), ("uint8_t", "stdint.h"),
    ("uint_fast16_t", "stdint.h"), ("uint_fast32_t", "stdint.h"),
    ("uint_fast64_t", "stdint.h"), ("uint_fast8_t", "stdint.h"),
    ("uint_least16_t", "stdint.h"), ("uint_least32_t", "stdint.h"),
    ("uint_least64_t", "stdint.h"), ("uint_least8_t", "stdint.h"), ("uintmax_t", "stdint.h"),
    ("uintptr_t", "stdint.h"),
];

/// Built-in functions of the C implementation, measured WITHOUT any `#include`.
static EINGEBAUT: [&str; 155] = [
    "abort", "abs", "aligned_alloc", "cabs", "cabsf", "cabsl", "cacos", "cacosf", "cacosh",
    "cacoshf", "cacoshl", "cacosl", "calloc", "carg", "cargf", "cargl", "casin", "casinf",
    "casinh", "casinhf", "casinhl", "casinl", "catan", "catanf", "catanh", "catanhf",
    "catanhl", "catanl", "ccos", "ccosf", "ccosh", "ccoshf", "ccoshl", "ccosl", "cexp",
    "cexpf", "cexpl", "cimag", "cimagf", "cimagl", "clog", "clogf", "clogl", "conj", "conjf",
    "conjl", "cpow", "cpowf", "cpowl", "cproj", "cprojf", "cprojl", "creal", "crealf",
    "creall", "csin", "csinf", "csinh", "csinhf", "csinhl", "csinl", "csqrt", "csqrtf",
    "csqrtl", "ctan", "ctanf", "ctanh", "ctanhf", "ctanhl", "ctanl", "exit", "feclearexcept",
    "fegetenv", "fegetexceptflag", "fegetround", "feholdexcept", "feraiseexcept", "fesetenv",
    "fesetexceptflag", "fesetround", "fetestexcept", "feupdateenv", "fprintf", "fputc",
    "fputs", "free", "fscanf", "fwrite", "imaxabs", "isalnum", "isalpha", "isblank",
    "iscntrl", "isdigit", "isgraph", "islower", "isprint", "ispunct", "isspace", "isupper",
    "iswalnum", "iswalpha", "iswblank", "iswcntrl", "iswdigit", "iswgraph", "iswlower",
    "iswprint", "iswpunct", "iswspace", "iswupper", "iswxdigit", "isxdigit", "labs", "llabs",
    "malloc", "memchr", "memcmp", "memcpy", "memmove", "memset", "printf", "putc", "putchar",
    "puts", "realloc", "scanf", "snprintf", "sprintf", "sscanf", "strcat", "strchr", "strcmp",
    "strcpy", "strcspn", "strftime", "strlen", "strncat", "strncmp", "strncpy", "strpbrk",
    "strrchr", "strspn", "strstr", "tolower", "toupper", "towlower", "towupper", "vfprintf",
    "vfscanf", "vprintf", "vscanf", "vsnprintf", "vsprintf", "vsscanf",
];
