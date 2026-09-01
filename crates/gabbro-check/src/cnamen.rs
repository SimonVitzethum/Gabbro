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
//! | `Klasse::Wort` -- a C11 keyword | 37 | C11 §6.4.1, minus the 7 that Gabbro's own vocabulary already refuses -- see `P002`, issued in `parse.rs` |
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
    /// **Declared by a POSIX header the generated unit does NOT include.** The dangerous
    /// class: nothing in the translation unit contradicts a wrong declaration, so `cc` has
    /// no conflict to report and the link succeeds against a signature nobody checked.
    Posix(&'static str),
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
            Klasse::Posix(h) => format!(
                "`{name}` is declared by `<{h}>`, which NO generated unit includes -- so `cc` \
                 sees no conflict, and the link finds the real symbol behind whatever this \
                 unit declared"
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
/// Gabbro's own vocabulary and never reach a name -- see `P002`, which lives in `parse.rs`.
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

/// **What C declares for a name -- and whether an `extern fn` can bind it at all.**
///
/// `N041` refuses a name. **At an `extern fn` that is the wrong question**: the construct
/// exists to bind a name C already has, so agreement is the GOAL. What can go wrong is the
/// SIGNATURE, and `cc` says so in as many words --
/// *conflicting types for built-in function 'exit'; expected 'void(int)'*.
///
/// So the checker needs C's signature, and this is where it stands. Three fields:
///
/// | field | what it holds |
/// |---|---|
/// | `c` | C's declaration in C's OWN words -- `int(int)`, `void *(void *, const void *, long unsigned int)` |
/// | `absenkung` | the lowering an `extern fn` must produce to match -- **empty when none can** |
/// | `form` | the Gabbro line that produces it -- **empty when none can** |
///
/// **A row with an empty `absenkung` is not a gap, it is the answer**: `printf` is
/// `int(const char *, ...)` and Gabbro has no variadic form; `memcpy` takes `void *`. *The
/// refusal shows C's declaration and the writer sees why, instead of being told a name is
/// "taken".*
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Signatur {
    /// C's declaration, in C's own words.
    pub c: &'static str,
    /// The lowering an `extern fn` must produce. Empty when no `extern fn` can bind the name.
    pub absenkung: &'static str,
    /// The Gabbro line that produces `absenkung`. Empty for the same reason.
    pub form: &'static str,
}

impl Signatur {
    /// Can an `extern fn` bind this name at all?
    pub fn bindbar(self) -> bool {
        !self.absenkung.is_empty()
    }
}

/// **The lookup.** `None` means: this measurement could read no C declaration for the name --
/// it is a keyword, a macro or a typedef, and none of the three is a function.
///
/// **Both tables, C11 first.** A name that stands in both is C11's -- see `POSIX`, which is
/// generated with the C11 names already subtracted, so the case does not arise and the order
/// is a statement about which table OWNS a name rather than a tie-break.
pub fn signatur(name: &str) -> Option<Signatur> {
    if let Ok(i) = SIGNATUR.binary_search_by_key(&name, |(n, ..)| n) {
        let (_, c, absenkung, form) = SIGNATUR[i];
        return Some(Signatur { c, absenkung, form });
    }
    let i = POSIX.binary_search_by_key(&name, |(n, ..)| n).ok()?;
    let (_, c, absenkung, form) = POSIX[i];
    Some(Signatur { c, absenkung, form })
}

/// **Does a POSIX header declare this name?** `Some(header)` -- and the header is the whole
/// answer to *how far the guard reaches*; see `POSIX`.
///
/// **Read at an `extern fn` and NOWHERE else, and that is the edge, not an oversight.** An
/// `extern fn` ASKS for the C side's symbol: it says *"the thing behind this name already
/// exists, and here is its shape"*, and a wrong shape is a wrong call. A Gabbro `fn read`
/// DEFINES its own and asks libc for nothing -- refusing it would forbid an ordinary English
/// word on the strength of a symbol the program never reaches for.
///
/// *That is why this is not folded into `vergeben`*, which `N041` reads for every named item:
/// `read`, `write`, `open`, `close`, `link`, `access`, `pause` and `sleep` are words, and a
/// rule that forbids them everywhere would cost far more than the hole it closes.
pub fn posix(name: &str) -> Option<&'static str> {
    POSIX
        .binary_search_by_key(&name, |(n, ..)| n)
        .ok()
        .map(|_| POSIX_KOPF)
}

/// **Does this function find the end of its data IN the data?** -- the rule of `N052`.
///
/// See the head of `ABSCHLUSS` for the argument. `true` means: the callee reads until it
/// meets a terminator, and **how far that is stands nowhere in the signature.**
pub fn endet_in_den_daten(name: &str) -> bool {
    ABSCHLUSS.binary_search(&name).is_ok()
}

/// How many rows each of the two new tables carries -- read by the probe, one home per number.
pub fn posixumfang() -> (usize, usize, usize) {
    (
        POSIX.len(),
        POSIX.iter().filter(|(_, _, a, _)| !a.is_empty()).count(),
        ABSCHLUSS.len(),
    )
}

/// How many rows the signature table carries, and how many of them are bindable.
/// **Read by the probe, so the number has one home** -- the same reason `umfang` exists.
pub fn signaturumfang() -> (usize, usize) {
    (
        SIGNATUR.len(),
        SIGNATUR.iter().filter(|(_, _, a, _)| !a.is_empty()).count(),
    )
}

/// **The signature C knows for each name it took -- measured, and the handle is checked in.**
///
/// `./instrumente/miss-c-signaturen.py` writes this table and
/// `./instrumente/miss-c-signaturen.py --pruefe` holds it against a fresh measurement.
/// *`W28`: a number that carries a rule belongs beside its handle -- and so does a table.*
///
/// > **The 558 names, split by what an `extern fn` can do with them** (2026-09-01):
/// >
/// > | class | count | bindable |
/// > |---|---:|---:|
/// > | C11 keyword | 37 | 0 -- no C declaration can carry it as a name |
/// > | header macro | 129 | 0 -- the preprocessor rewrites the name before the parser sees it |
/// > | header typedef | 67 | 0 -- no function in the same scope can carry it |
/// > | header function | 170 | 99 |
/// > | built-in function | 155 | 50 |
/// > | **total** | **558** | **149** |
///
/// > **138 → 149 on 2026-09-02, and the eleven come from ONE decision**: a `void *` in a
/// > PARAMETER is writable and a `void *` as a RESULT is not. `fwrite`, `memcmp`, `free`,
/// > `fputc`, `putc` and the six `<fenv.h>` calls gained a form; `memcpy`, `memmove`,
/// > `memset` and `memchr` did not, and all four for the same reason -- they RETURN one.
/// > *The split is not a taste; it is which way the precision flows.* See `ZEIGER` in
/// > `./instrumente/miss-c-signaturen.py` and `ABSCHLUSS` below.
///
/// **`long long` is deliberately not treated as `int64_t`, and that is measured**:
/// `_Static_assert(__builtin_types_compatible_p(long long, int64_t))` FAILS here -- `int64_t`
/// is `long`, and C keeps the two apart although both are 64 bits wide. *Without that check
/// `llabs`, `llrint` and `llround` would stand here with a signature `cc` rejects* -- a table
/// that replaces a rule and is itself wrong, in the expensive direction.
///
/// Every bindable row was handed to `cc -std=c11 -O0 -Wall -Wextra -Werror` as the
/// declaration `emit.rs` would write: **149 of 149 green.** *A signature table nobody has
/// compiled is an assertion.*
static SIGNATUR: [(&str, &str, &str, &str); 325] = [
    ("abort", "void(void)", "void(void)", "extern fn abort()"),
    ("abs", "int(int)", "int32_t(int32_t)", "extern fn abs(a : i32) -> i32"),
    ("acos", "double(double)", "double(double)", "extern fn acos(a : f64) -> f64"),
    ("acosf", "float(float)", "float(float)", "extern fn acosf(a : f32) -> f32"),
    ("acosh", "double(double)", "double(double)", "extern fn acosh(a : f64) -> f64"),
    ("acoshf", "float(float)", "float(float)", "extern fn acoshf(a : f32) -> f32"),
    ("acoshl", "long double(long double)", "", ""),
    ("acosl", "long double(long double)", "", ""),
    ("aligned_alloc", "void *(long unsigned int, long unsigned int)", "", ""),
    ("asin", "double(double)", "double(double)", "extern fn asin(a : f64) -> f64"),
    ("asinf", "float(float)", "float(float)", "extern fn asinf(a : f32) -> f32"),
    ("asinh", "double(double)", "double(double)", "extern fn asinh(a : f64) -> f64"),
    ("asinhf", "float(float)", "float(float)", "extern fn asinhf(a : f32) -> f32"),
    ("asinhl", "long double(long double)", "", ""),
    ("asinl", "long double(long double)", "", ""),
    ("atan", "double(double)", "double(double)", "extern fn atan(a : f64) -> f64"),
    ("atan2", "double(double, double)", "double(double,double)", "extern fn atan2(a : f64, b : f64) -> f64"),
    ("atan2f", "float(float, float)", "float(float,float)", "extern fn atan2f(a : f32, b : f32) -> f32"),
    ("atan2l", "long double(long double, long double)", "", ""),
    ("atanf", "float(float)", "float(float)", "extern fn atanf(a : f32) -> f32"),
    ("atanh", "double(double)", "double(double)", "extern fn atanh(a : f64) -> f64"),
    ("atanhf", "float(float)", "float(float)", "extern fn atanhf(a : f32) -> f32"),
    ("atanhl", "long double(long double)", "", ""),
    ("atanl", "long double(long double)", "", ""),
    ("cabs", "double(_Complex double)", "", ""),
    ("cabsf", "float(_Complex float)", "", ""),
    ("cabsl", "long double(_Complex long double)", "", ""),
    ("cacos", "_Complex double(_Complex double)", "", ""),
    ("cacosf", "_Complex float(_Complex float)", "", ""),
    ("cacosh", "_Complex double(_Complex double)", "", ""),
    ("cacoshf", "_Complex float(_Complex float)", "", ""),
    ("cacoshl", "_Complex long double(_Complex long double)", "", ""),
    ("cacosl", "_Complex long double(_Complex long double)", "", ""),
    ("calloc", "void *(long unsigned int, long unsigned int)", "", ""),
    ("carg", "double(_Complex double)", "", ""),
    ("cargf", "float(_Complex float)", "", ""),
    ("cargl", "long double(_Complex long double)", "", ""),
    ("casin", "_Complex double(_Complex double)", "", ""),
    ("casinf", "_Complex float(_Complex float)", "", ""),
    ("casinh", "_Complex double(_Complex double)", "", ""),
    ("casinhf", "_Complex float(_Complex float)", "", ""),
    ("casinhl", "_Complex long double(_Complex long double)", "", ""),
    ("casinl", "_Complex long double(_Complex long double)", "", ""),
    ("catan", "_Complex double(_Complex double)", "", ""),
    ("catanf", "_Complex float(_Complex float)", "", ""),
    ("catanh", "_Complex double(_Complex double)", "", ""),
    ("catanhf", "_Complex float(_Complex float)", "", ""),
    ("catanhl", "_Complex long double(_Complex long double)", "", ""),
    ("catanl", "_Complex long double(_Complex long double)", "", ""),
    ("cbrt", "double(double)", "double(double)", "extern fn cbrt(a : f64) -> f64"),
    ("cbrtf", "float(float)", "float(float)", "extern fn cbrtf(a : f32) -> f32"),
    ("cbrtl", "long double(long double)", "", ""),
    ("ccos", "_Complex double(_Complex double)", "", ""),
    ("ccosf", "_Complex float(_Complex float)", "", ""),
    ("ccosh", "_Complex double(_Complex double)", "", ""),
    ("ccoshf", "_Complex float(_Complex float)", "", ""),
    ("ccoshl", "_Complex long double(_Complex long double)", "", ""),
    ("ccosl", "_Complex long double(_Complex long double)", "", ""),
    ("ceil", "double(double)", "double(double)", "extern fn ceil(a : f64) -> f64"),
    ("ceilf", "float(float)", "float(float)", "extern fn ceilf(a : f32) -> f32"),
    ("ceill", "long double(long double)", "", ""),
    ("cexp", "_Complex double(_Complex double)", "", ""),
    ("cexpf", "_Complex float(_Complex float)", "", ""),
    ("cexpl", "_Complex long double(_Complex long double)", "", ""),
    ("cimag", "double(_Complex double)", "", ""),
    ("cimagf", "float(_Complex float)", "", ""),
    ("cimagl", "long double(_Complex long double)", "", ""),
    ("clog", "_Complex double(_Complex double)", "", ""),
    ("clogf", "_Complex float(_Complex float)", "", ""),
    ("clogl", "_Complex long double(_Complex long double)", "", ""),
    ("conj", "_Complex double(_Complex double)", "", ""),
    ("conjf", "_Complex float(_Complex float)", "", ""),
    ("conjl", "_Complex long double(_Complex long double)", "", ""),
    ("copysign", "double(double, double)", "double(double,double)", "extern fn copysign(a : f64, b : f64) -> f64"),
    ("copysignf", "float(float, float)", "float(float,float)", "extern fn copysignf(a : f32, b : f32) -> f32"),
    ("copysignl", "long double(long double, long double)", "", ""),
    ("cos", "double(double)", "double(double)", "extern fn cos(a : f64) -> f64"),
    ("cosf", "float(float)", "float(float)", "extern fn cosf(a : f32) -> f32"),
    ("cosh", "double(double)", "double(double)", "extern fn cosh(a : f64) -> f64"),
    ("coshf", "float(float)", "float(float)", "extern fn coshf(a : f32) -> f32"),
    ("coshl", "long double(long double)", "", ""),
    ("cosl", "long double(long double)", "", ""),
    ("cpow", "_Complex double(_Complex double, _Complex double)", "", ""),
    ("cpowf", "_Complex float(_Complex float, _Complex float)", "", ""),
    ("cpowl", "_Complex long double(_Complex long double, _Complex long double)", "", ""),
    ("cproj", "_Complex double(_Complex double)", "", ""),
    ("cprojf", "_Complex float(_Complex float)", "", ""),
    ("cprojl", "_Complex long double(_Complex long double)", "", ""),
    ("creal", "double(_Complex double)", "", ""),
    ("crealf", "float(_Complex float)", "", ""),
    ("creall", "long double(_Complex long double)", "", ""),
    ("csin", "_Complex double(_Complex double)", "", ""),
    ("csinf", "_Complex float(_Complex float)", "", ""),
    ("csinh", "_Complex double(_Complex double)", "", ""),
    ("csinhf", "_Complex float(_Complex float)", "", ""),
    ("csinhl", "_Complex long double(_Complex long double)", "", ""),
    ("csinl", "_Complex long double(_Complex long double)", "", ""),
    ("csqrt", "_Complex double(_Complex double)", "", ""),
    ("csqrtf", "_Complex float(_Complex float)", "", ""),
    ("csqrtl", "_Complex long double(_Complex long double)", "", ""),
    ("ctan", "_Complex double(_Complex double)", "", ""),
    ("ctanf", "_Complex float(_Complex float)", "", ""),
    ("ctanh", "_Complex double(_Complex double)", "", ""),
    ("ctanhf", "_Complex float(_Complex float)", "", ""),
    ("ctanhl", "_Complex long double(_Complex long double)", "", ""),
    ("ctanl", "_Complex long double(_Complex long double)", "", ""),
    ("erf", "double(double)", "double(double)", "extern fn erf(a : f64) -> f64"),
    ("erfc", "double(double)", "double(double)", "extern fn erfc(a : f64) -> f64"),
    ("erfcf", "float(float)", "float(float)", "extern fn erfcf(a : f32) -> f32"),
    ("erfcl", "long double(long double)", "", ""),
    ("erff", "float(float)", "float(float)", "extern fn erff(a : f32) -> f32"),
    ("erfl", "long double(long double)", "", ""),
    ("exit", "void(int)", "void(int32_t)", "extern fn exit(a : i32)"),
    ("exp", "double(double)", "double(double)", "extern fn exp(a : f64) -> f64"),
    ("exp2", "double(double)", "double(double)", "extern fn exp2(a : f64) -> f64"),
    ("exp2f", "float(float)", "float(float)", "extern fn exp2f(a : f32) -> f32"),
    ("exp2l", "long double(long double)", "", ""),
    ("expf", "float(float)", "float(float)", "extern fn expf(a : f32) -> f32"),
    ("expl", "long double(long double)", "", ""),
    ("expm1", "double(double)", "double(double)", "extern fn expm1(a : f64) -> f64"),
    ("expm1f", "float(float)", "float(float)", "extern fn expm1f(a : f32) -> f32"),
    ("expm1l", "long double(long double)", "", ""),
    ("fabs", "double(double)", "double(double)", "extern fn fabs(a : f64) -> f64"),
    ("fabsf", "float(float)", "float(float)", "extern fn fabsf(a : f32) -> f32"),
    ("fabsl", "long double(long double)", "", ""),
    ("fdim", "double(double, double)", "double(double,double)", "extern fn fdim(a : f64, b : f64) -> f64"),
    ("fdimf", "float(float, float)", "float(float,float)", "extern fn fdimf(a : f32, b : f32) -> f32"),
    ("fdiml", "long double(long double, long double)", "", ""),
    ("feclearexcept", "int(int)", "int32_t(int32_t)", "extern fn feclearexcept(a : i32) -> i32"),
    ("fegetenv", "int(void *)", "int32_t(void *)", "extern fn fegetenv(a : ptr<normal, rw> T) -> i32"),
    ("fegetexceptflag", "int(void *, int)", "int32_t(void *,int32_t)", "extern fn fegetexceptflag(a : ptr<normal, rw> T, b : i32) -> i32"),
    ("fegetround", "int(void)", "int32_t(void)", "extern fn fegetround() -> i32"),
    ("feholdexcept", "int(void *)", "int32_t(void *)", "extern fn feholdexcept(a : ptr<normal, rw> T) -> i32"),
    ("feraiseexcept", "int(int)", "int32_t(int32_t)", "extern fn feraiseexcept(a : i32) -> i32"),
    ("fesetenv", "int(const void *)", "int32_t(const void *)", "extern fn fesetenv(a : ptr<normal, r> T) -> i32"),
    ("fesetexceptflag", "int(const void *, int)", "int32_t(const void *,int32_t)", "extern fn fesetexceptflag(a : ptr<normal, r> T, b : i32) -> i32"),
    ("fesetround", "int(int)", "int32_t(int32_t)", "extern fn fesetround(a : i32) -> i32"),
    ("fetestexcept", "int(int)", "int32_t(int32_t)", "extern fn fetestexcept(a : i32) -> i32"),
    ("feupdateenv", "int(const void *)", "int32_t(const void *)", "extern fn feupdateenv(a : ptr<normal, r> T) -> i32"),
    ("floorf", "float(float)", "float(float)", "extern fn floorf(a : f32) -> f32"),
    ("floorl", "long double(long double)", "", ""),
    ("fma", "double(double, double, double)", "double(double,double,double)", "extern fn fma(a : f64, b : f64, c : f64) -> f64"),
    ("fmaf", "float(float, float, float)", "float(float,float,float)", "extern fn fmaf(a : f32, b : f32, c : f32) -> f32"),
    ("fmal", "long double(long double, long double, long double)", "", ""),
    ("fmax", "double(double, double)", "double(double,double)", "extern fn fmax(a : f64, b : f64) -> f64"),
    ("fmaxf", "float(float, float)", "float(float,float)", "extern fn fmaxf(a : f32, b : f32) -> f32"),
    ("fmaxl", "long double(long double, long double)", "", ""),
    ("fmin", "double(double, double)", "double(double,double)", "extern fn fmin(a : f64, b : f64) -> f64"),
    ("fminf", "float(float, float)", "float(float,float)", "extern fn fminf(a : f32, b : f32) -> f32"),
    ("fminl", "long double(long double, long double)", "", ""),
    ("fmod", "double(double, double)", "double(double,double)", "extern fn fmod(a : f64, b : f64) -> f64"),
    ("fmodf", "float(float, float)", "float(float,float)", "extern fn fmodf(a : f32, b : f32) -> f32"),
    ("fmodl", "long double(long double, long double)", "", ""),
    ("fprintf", "int(void *, const char *, ...)", "", ""),
    ("fputc", "int(int, void *)", "int32_t(int32_t,void *)", "extern fn fputc(a : i32, b : ptr<normal, rw> T) -> i32"),
    ("fputs", "int(const char *, void *)", "", ""),
    ("free", "void(void *)", "void(void *)", "extern fn free(a : ptr<normal, rw> T)"),
    ("frexp", "double(double, int *)", "", ""),
    ("frexpf", "float(float, int *)", "", ""),
    ("frexpl", "long double(long double, int *)", "", ""),
    ("fscanf", "int(void *, const char *, ...)", "", ""),
    ("fwrite", "long unsigned int(const void *, long unsigned int, long unsigned int, void *)", "uint64_t(const void *,uint64_t,uint64_t,void *)", "extern fn fwrite(a : ptr<normal, r> T, b : u64, c : u64, d : ptr<normal, rw> T) -> u64"),
    ("hypot", "double(double, double)", "double(double,double)", "extern fn hypot(a : f64, b : f64) -> f64"),
    ("hypotf", "float(float, float)", "float(float,float)", "extern fn hypotf(a : f32, b : f32) -> f32"),
    ("hypotl", "long double(long double, long double)", "", ""),
    ("ilogb", "int(double)", "int32_t(double)", "extern fn ilogb(a : f64) -> i32"),
    ("ilogbf", "int(float)", "int32_t(float)", "extern fn ilogbf(a : f32) -> i32"),
    ("ilogbl", "int(long double)", "", ""),
    ("imaxabs", "long int(long int)", "int64_t(int64_t)", "extern fn imaxabs(a : i64) -> i64"),
    ("isalnum", "int(int)", "int32_t(int32_t)", "extern fn isalnum(a : i32) -> i32"),
    ("isalpha", "int(int)", "int32_t(int32_t)", "extern fn isalpha(a : i32) -> i32"),
    ("isblank", "int(int)", "int32_t(int32_t)", "extern fn isblank(a : i32) -> i32"),
    ("iscntrl", "int(int)", "int32_t(int32_t)", "extern fn iscntrl(a : i32) -> i32"),
    ("isdigit", "int(int)", "int32_t(int32_t)", "extern fn isdigit(a : i32) -> i32"),
    ("isgraph", "int(int)", "int32_t(int32_t)", "extern fn isgraph(a : i32) -> i32"),
    ("islower", "int(int)", "int32_t(int32_t)", "extern fn islower(a : i32) -> i32"),
    ("isprint", "int(int)", "int32_t(int32_t)", "extern fn isprint(a : i32) -> i32"),
    ("ispunct", "int(int)", "int32_t(int32_t)", "extern fn ispunct(a : i32) -> i32"),
    ("isspace", "int(int)", "int32_t(int32_t)", "extern fn isspace(a : i32) -> i32"),
    ("isupper", "int(int)", "int32_t(int32_t)", "extern fn isupper(a : i32) -> i32"),
    ("iswalnum", "int(unsigned int)", "int32_t(uint32_t)", "extern fn iswalnum(a : u32) -> i32"),
    ("iswalpha", "int(unsigned int)", "int32_t(uint32_t)", "extern fn iswalpha(a : u32) -> i32"),
    ("iswblank", "int(unsigned int)", "int32_t(uint32_t)", "extern fn iswblank(a : u32) -> i32"),
    ("iswcntrl", "int(unsigned int)", "int32_t(uint32_t)", "extern fn iswcntrl(a : u32) -> i32"),
    ("iswdigit", "int(unsigned int)", "int32_t(uint32_t)", "extern fn iswdigit(a : u32) -> i32"),
    ("iswgraph", "int(unsigned int)", "int32_t(uint32_t)", "extern fn iswgraph(a : u32) -> i32"),
    ("iswlower", "int(unsigned int)", "int32_t(uint32_t)", "extern fn iswlower(a : u32) -> i32"),
    ("iswprint", "int(unsigned int)", "int32_t(uint32_t)", "extern fn iswprint(a : u32) -> i32"),
    ("iswpunct", "int(unsigned int)", "int32_t(uint32_t)", "extern fn iswpunct(a : u32) -> i32"),
    ("iswspace", "int(unsigned int)", "int32_t(uint32_t)", "extern fn iswspace(a : u32) -> i32"),
    ("iswupper", "int(unsigned int)", "int32_t(uint32_t)", "extern fn iswupper(a : u32) -> i32"),
    ("iswxdigit", "int(unsigned int)", "int32_t(uint32_t)", "extern fn iswxdigit(a : u32) -> i32"),
    ("isxdigit", "int(int)", "int32_t(int32_t)", "extern fn isxdigit(a : i32) -> i32"),
    ("labs", "long int(long int)", "int64_t(int64_t)", "extern fn labs(a : i64) -> i64"),
    ("ldexp", "double(double, int)", "double(double,int32_t)", "extern fn ldexp(a : f64, b : i32) -> f64"),
    ("ldexpf", "float(float, int)", "float(float,int32_t)", "extern fn ldexpf(a : f32, b : i32) -> f32"),
    ("ldexpl", "long double(long double, int)", "", ""),
    ("lgamma", "double(double)", "double(double)", "extern fn lgamma(a : f64) -> f64"),
    ("lgammaf", "float(float)", "float(float)", "extern fn lgammaf(a : f32) -> f32"),
    ("lgammal", "long double(long double)", "", ""),
    ("llabs", "long long int(long long int)", "", ""),
    ("llrint", "long long int(double)", "", ""),
    ("llrintf", "long long int(float)", "", ""),
    ("llrintl", "long long int(long double)", "", ""),
    ("llround", "long long int(double)", "", ""),
    ("llroundf", "long long int(float)", "", ""),
    ("llroundl", "long long int(long double)", "", ""),
    ("log", "double(double)", "double(double)", "extern fn log(a : f64) -> f64"),
    ("log10", "double(double)", "double(double)", "extern fn log10(a : f64) -> f64"),
    ("log10f", "float(float)", "float(float)", "extern fn log10f(a : f32) -> f32"),
    ("log10l", "long double(long double)", "", ""),
    ("log1p", "double(double)", "double(double)", "extern fn log1p(a : f64) -> f64"),
    ("log1pf", "float(float)", "float(float)", "extern fn log1pf(a : f32) -> f32"),
    ("log1pl", "long double(long double)", "", ""),
    ("log2", "double(double)", "double(double)", "extern fn log2(a : f64) -> f64"),
    ("log2f", "float(float)", "float(float)", "extern fn log2f(a : f32) -> f32"),
    ("log2l", "long double(long double)", "", ""),
    ("logb", "double(double)", "double(double)", "extern fn logb(a : f64) -> f64"),
    ("logbf", "float(float)", "float(float)", "extern fn logbf(a : f32) -> f32"),
    ("logbl", "long double(long double)", "", ""),
    ("logf", "float(float)", "float(float)", "extern fn logf(a : f32) -> f32"),
    ("logl", "long double(long double)", "", ""),
    ("lrint", "long int(double)", "int64_t(double)", "extern fn lrint(a : f64) -> i64"),
    ("lrintf", "long int(float)", "int64_t(float)", "extern fn lrintf(a : f32) -> i64"),
    ("lrintl", "long int(long double)", "", ""),
    ("lround", "long int(double)", "int64_t(double)", "extern fn lround(a : f64) -> i64"),
    ("lroundf", "long int(float)", "int64_t(float)", "extern fn lroundf(a : f32) -> i64"),
    ("lroundl", "long int(long double)", "", ""),
    ("malloc", "void *(long unsigned int)", "", ""),
    ("memchr", "void *(const void *, int, long unsigned int)", "", ""),
    ("memcmp", "int(const void *, const void *, long unsigned int)", "int32_t(const void *,const void *,uint64_t)", "extern fn memcmp(a : ptr<normal, r> T, b : ptr<normal, r> T, c : u64) -> i32"),
    ("memcpy", "void *(void *, const void *, long unsigned int)", "", ""),
    ("memmove", "void *(void *, const void *, long unsigned int)", "", ""),
    ("memset", "void *(void *, int, long unsigned int)", "", ""),
    ("modf", "double(double, double *)", "", ""),
    ("modff", "float(float, float *)", "", ""),
    ("modfl", "long double(long double, long double *)", "", ""),
    ("nan", "double(const char *)", "", ""),
    ("nanf", "float(const char *)", "", ""),
    ("nanl", "long double(const char *)", "", ""),
    ("nearbyint", "double(double)", "double(double)", "extern fn nearbyint(a : f64) -> f64"),
    ("nearbyintf", "float(float)", "float(float)", "extern fn nearbyintf(a : f32) -> f32"),
    ("nearbyintl", "long double(long double)", "", ""),
    ("nextafter", "double(double, double)", "double(double,double)", "extern fn nextafter(a : f64, b : f64) -> f64"),
    ("nextafterf", "float(float, float)", "float(float,float)", "extern fn nextafterf(a : f32, b : f32) -> f32"),
    ("nextafterl", "long double(long double, long double)", "", ""),
    ("nexttoward", "double(double, long double)", "", ""),
    ("nexttowardf", "float(float, long double)", "", ""),
    ("nexttowardl", "long double(long double, long double)", "", ""),
    ("pow", "double(double, double)", "double(double,double)", "extern fn pow(a : f64, b : f64) -> f64"),
    ("powf", "float(float, float)", "float(float,float)", "extern fn powf(a : f32, b : f32) -> f32"),
    ("powl", "long double(long double, long double)", "", ""),
    ("printf", "int(const char *, ...)", "", ""),
    ("putc", "int(int, void *)", "int32_t(int32_t,void *)", "extern fn putc(a : i32, b : ptr<normal, rw> T) -> i32"),
    ("putchar", "int(int)", "int32_t(int32_t)", "extern fn putchar(a : i32) -> i32"),
    ("puts", "int(const char *)", "", ""),
    ("realloc", "void *(void *, long unsigned int)", "", ""),
    ("remainder", "double(double, double)", "double(double,double)", "extern fn remainder(a : f64, b : f64) -> f64"),
    ("remainderf", "float(float, float)", "float(float,float)", "extern fn remainderf(a : f32, b : f32) -> f32"),
    ("remainderl", "long double(long double, long double)", "", ""),
    ("remquo", "double(double, double, int *)", "", ""),
    ("remquof", "float(float, float, int *)", "", ""),
    ("remquol", "long double(long double, long double, int *)", "", ""),
    ("rint", "double(double)", "double(double)", "extern fn rint(a : f64) -> f64"),
    ("rintf", "float(float)", "float(float)", "extern fn rintf(a : f32) -> f32"),
    ("rintl", "long double(long double)", "", ""),
    ("round", "double(double)", "double(double)", "extern fn round(a : f64) -> f64"),
    ("roundf", "float(float)", "float(float)", "extern fn roundf(a : f32) -> f32"),
    ("roundl", "long double(long double)", "", ""),
    ("scalbln", "double(double, long int)", "double(double,int64_t)", "extern fn scalbln(a : f64, b : i64) -> f64"),
    ("scalblnf", "float(float, long int)", "float(float,int64_t)", "extern fn scalblnf(a : f32, b : i64) -> f32"),
    ("scalblnl", "long double(long double, long int)", "", ""),
    ("scalbn", "double(double, int)", "double(double,int32_t)", "extern fn scalbn(a : f64, b : i32) -> f64"),
    ("scalbnf", "float(float, int)", "float(float,int32_t)", "extern fn scalbnf(a : f32, b : i32) -> f32"),
    ("scalbnl", "long double(long double, int)", "", ""),
    ("scanf", "int(const char *, ...)", "", ""),
    ("sin", "double(double)", "double(double)", "extern fn sin(a : f64) -> f64"),
    ("sinf", "float(float)", "float(float)", "extern fn sinf(a : f32) -> f32"),
    ("sinh", "double(double)", "double(double)", "extern fn sinh(a : f64) -> f64"),
    ("sinhf", "float(float)", "float(float)", "extern fn sinhf(a : f32) -> f32"),
    ("sinhl", "long double(long double)", "", ""),
    ("sinl", "long double(long double)", "", ""),
    ("snprintf", "int(char *, long unsigned int, const char *, ...)", "", ""),
    ("sprintf", "int(char *, const char *, ...)", "", ""),
    ("sqrt", "double(double)", "double(double)", "extern fn sqrt(a : f64) -> f64"),
    ("sqrtf", "float(float)", "float(float)", "extern fn sqrtf(a : f32) -> f32"),
    ("sqrtl", "long double(long double)", "", ""),
    ("sscanf", "int(const char *, const char *, ...)", "", ""),
    ("strcat", "char *(char *, const char *)", "", ""),
    ("strchr", "char *(const char *, int)", "", ""),
    ("strcmp", "int(const char *, const char *)", "", ""),
    ("strcpy", "char *(char *, const char *)", "", ""),
    ("strcspn", "long unsigned int(const char *, const char *)", "", ""),
    ("strftime", "long unsigned int(char *, long unsigned int, const char *, const void *)", "", ""),
    ("strlen", "long unsigned int(const char *)", "", ""),
    ("strncat", "char *(char *, const char *, long unsigned int)", "", ""),
    ("strncmp", "int(const char *, const char *, long unsigned int)", "", ""),
    ("strncpy", "char *(char *, const char *, long unsigned int)", "", ""),
    ("strpbrk", "char *(const char *, const char *)", "", ""),
    ("strrchr", "char *(const char *, int)", "", ""),
    ("strspn", "long unsigned int(const char *, const char *)", "", ""),
    ("strstr", "char *(const char *, const char *)", "", ""),
    ("tan", "double(double)", "double(double)", "extern fn tan(a : f64) -> f64"),
    ("tanf", "float(float)", "float(float)", "extern fn tanf(a : f32) -> f32"),
    ("tanh", "double(double)", "double(double)", "extern fn tanh(a : f64) -> f64"),
    ("tanhf", "float(float)", "float(float)", "extern fn tanhf(a : f32) -> f32"),
    ("tanhl", "long double(long double)", "", ""),
    ("tanl", "long double(long double)", "", ""),
    ("tgamma", "double(double)", "double(double)", "extern fn tgamma(a : f64) -> f64"),
    ("tgammaf", "float(float)", "float(float)", "extern fn tgammaf(a : f32) -> f32"),
    ("tgammal", "long double(long double)", "", ""),
    ("tolower", "int(int)", "int32_t(int32_t)", "extern fn tolower(a : i32) -> i32"),
    ("toupper", "int(int)", "int32_t(int32_t)", "extern fn toupper(a : i32) -> i32"),
    ("towlower", "unsigned int(unsigned int)", "uint32_t(uint32_t)", "extern fn towlower(a : u32) -> u32"),
    ("towupper", "unsigned int(unsigned int)", "uint32_t(uint32_t)", "extern fn towupper(a : u32) -> u32"),
    ("trunc", "double(double)", "double(double)", "extern fn trunc(a : f64) -> f64"),
    ("truncf", "float(float)", "float(float)", "extern fn truncf(a : f32) -> f32"),
    ("truncl", "long double(long double)", "", ""),
    ("vfprintf", "int(void *, const char *, __va_list_tag *)", "", ""),
    ("vfscanf", "int(void *, const char *, __va_list_tag *)", "", ""),
    ("vprintf", "int(const char *, __va_list_tag *)", "", ""),
    ("vscanf", "int(const char *, __va_list_tag *)", "", ""),
    ("vsnprintf", "int(char *, long unsigned int, const char *, __va_list_tag *)", "", ""),
    ("vsprintf", "int(char *, const char *, __va_list_tag *)", "", ""),
    ("vsscanf", "int(const char *, const char *, __va_list_tag *)", "", ""),
];


/// **The rule: what is bound is what says where the data ends.**
///
/// `B2` asked the string question as a SIGNATURE question -- *"is it enough that `N046` lets
/// `[u8; N]` through as `char *` if the user writes it down?"* It is not, and the reason is
/// not about spelling:
///
/// > `[u8; N]` carries a LENGTH. `const char *` carries a TERMINATOR. Those are two different
/// > ways of marking an end, and the binding must translate one into the other. If a
/// > `[u8; N]` without a trailing NUL goes to `puts`, the C side reads past the end.
///
/// So the question at an `extern fn` is not *"can Gabbro spell this type"* but **"can Gabbro
/// write down the obligation this call puts on the caller?"** -- and that has a measured
/// answer, which is why this is a rule and not a preference:
///
/// | how the callee finds the end | the obligation | can Gabbro state it? |
/// |---|---|---|
/// | a COUNT in the signature -- `write(fd, p, n)` | `n` must not exceed the buffer | **yes** -- `requires n <= KAP`, and `M115` discharges it at every call site |
/// | a TERMINATOR in the data -- `puts(s)` | there must be a NUL at or before the end | **no** -- nothing in the signature names how far the callee reads |
///
/// **The first row is measured, not argued.** With `extern fn write(…, n : u64) requires
/// n <= 8`, the call `write(1, t, 999)` is refused:
///
/// ```text
/// error: [M115] `write` requires `n <= 8`, and the argument lies in 999 .. 999
///        = the callee's precondition is not merely unproved at this site but EXCLUDED
/// ```
///
/// *A length-taking binding does not make the call safe -- it makes the danger EXPRESSIBLE,
/// and the checker already holds it.* That is the whole difference. A terminator-taking
/// binding leaves nothing to hold: there is no expression over the parameters that bounds the
/// read, because the bound is a byte somewhere in the data.
///
/// **And this explains `putchar` at the same time.** It takes a value, has no end to find,
/// and needs no obligation -- which is why the front door opened on 2026-09-01 with a
/// value-taking call and no string. *Three kinds, one test, and the answer follows from the
/// representation instead of from a judgement about C's library.*
///
/// > **What the rule REFUSES to claim.** It says nothing about whether `n` is the length the
/// > writer meant -- only that `n` can be bounded and that the bound is checked where the
/// > call stands. The obligation still has to be written; the rule makes it writable.
///
/// **The names whose end is in the data**, over both tables. Generated by
/// `./instrumente/miss-c-signaturen.py --abschluss`, and the test it runs is on the
/// DECLARATION: *a `char *` parameter with no count beside it.* Four names where the
/// derivation is wrong are named in the script and added by hand -- `snprintf`, `vsnprintf`
/// and `strftime` carry a count that bounds the OUTPUT while the format string is still
/// scanned, and `strncat` carries one that bounds the READ while the write starts at the
/// destination's own NUL. *A derivation with four named exceptions is a measurement.*
static ABSCHLUSS: [&str; 44] = [
    "access",
    "chdir",
    "chown",
    "execl",
    "execle",
    "execlp",
    "execv",
    "execve",
    "execvp",
    "fprintf",
    "fputs",
    "fscanf",
    "link",
    "nan",
    "nanf",
    "nanl",
    "pathconf",
    "printf",
    "puts",
    "rmdir",
    "scanf",
    "snprintf",
    "sprintf",
    "sscanf",
    "strcat",
    "strchr",
    "strcmp",
    "strcpy",
    "strcspn",
    "strftime",
    "strlen",
    "strncat",
    "strpbrk",
    "strrchr",
    "strspn",
    "strstr",
    "unlink",
    "vfprintf",
    "vfscanf",
    "vprintf",
    "vscanf",
    "vsnprintf",
    "vsprintf",
    "vsscanf",
];

/// **The header this measurement reads -- and the whole of the guard's POSIX edge.**
pub const POSIX_KOPF: &str = "unistd.h";

/// **The names `<unistd.h>` declares, and the hole they were found in.**
///
/// `N041` guards the names *C11* took. **POSIX falls straight through that net**, and the
/// shape is the one `N041` itself was built against, one namespace over:
///
/// ```text
/// extern fn write(fd : i32, p : ptr<normal, r> Text, n : u64) -> i64
///     ->  int64_t write(int32_t fd, const Text *p, uint64_t n);
///     gabbro pruefe: 0 errors      cc (no header): compiles, links, RUNS
///     cc with <unistd.h> beside it: error: conflicting types for 'write';
///                                   the real one is ssize_t(int, const void *, size_t)
/// ```
///
/// *Measured 2026-09-02.* The generated unit includes no POSIX header, so `cc` never sees the
/// second declaration and has nothing to complain about. **The refusal that should have come
/// from the foreign compiler cannot come from it at all** -- which is exactly why the
/// checker has to hold it, and why `messung/proben/probe-c-namen-frei.gab` was wrong to hold
/// these five names up as *free*: they are not taken by C11 and they are not free either.
///
/// > **How far it reaches, exactly.** One header, measured with `cc -aux-info`, and only the
/// > declarations whose site IS `<unistd.h>` -- 47 names after the C11 table's are subtracted,
/// > **13 of them bindable** and all 13 through `cc -Wall -Wextra -Werror`.
/// >
/// > **What is OUTSIDE, and named rather than implied:**
/// >
/// > * every other POSIX header -- `<signal.h>`, `<sys/socket.h>`, `<fcntl.h>`, `<pthread.h>`.
/// >   *The corpus reaches two of them today:* `signal` and `recv` in `messung/fragmente/F05.gab`
/// >   bind unchecked, and that is a hole with a name on it, not a green.
/// > * every GNU extension, every other library, and every symbol the writer links themself.
/// > * the glibc spellings `__pid_t`, `__uid_t`, `__gid_t`, `__off_t`: a table that resolved
/// >   them would measure glibc and call it POSIX -- the same decision the 558-name table
/// >   already took for the 883 underscore macros. *So `getpid` is not bindable, and the
/// >   refusal names the type it could not read.*
/// > * this is a measurement of THIS toolchain, LP64, and it says so the way the C11 half does.
///
/// **Read at an `extern fn` and nowhere else** -- see `posix` for why that boundary is the
/// right one and not a shortcut.
static POSIX: [(&str, &str, &str, &str); 47] = [
    ("_exit", "void(int)", "void(int32_t)", "extern fn _exit(a : i32)"),
    ("access", "int(const char *, int)", "", ""),
    ("alarm", "unsigned int(unsigned int)", "uint32_t(uint32_t)", "extern fn alarm(a : u32) -> u32"),
    ("chdir", "int(const char *)", "", ""),
    ("chown", "int(const char *, __uid_t, __gid_t)", "", ""),
    ("close", "int(int)", "int32_t(int32_t)", "extern fn close(a : i32) -> i32"),
    ("dup", "int(int)", "int32_t(int32_t)", "extern fn dup(a : i32) -> i32"),
    ("dup2", "int(int, int)", "int32_t(int32_t,int32_t)", "extern fn dup2(a : i32, b : i32) -> i32"),
    ("execl", "int(const char *, const char *, ...)", "", ""),
    ("execle", "int(const char *, const char *, ...)", "", ""),
    ("execlp", "int(const char *, const char *, ...)", "", ""),
    ("execv", "int(const char *, char *const *)", "", ""),
    ("execve", "int(const char *, char *const *, char *const *)", "", ""),
    ("execvp", "int(const char *, char *const *)", "", ""),
    ("fork", "__pid_t(void)", "", ""),
    ("fpathconf", "long int(int, int)", "int64_t(int32_t,int32_t)", "extern fn fpathconf(a : i32, b : i32) -> i64"),
    ("fsync", "int(int)", "int32_t(int32_t)", "extern fn fsync(a : i32) -> i32"),
    ("getcwd", "char *(char *, size_t)", "", ""),
    ("getegid", "__gid_t(void)", "", ""),
    ("geteuid", "__uid_t(void)", "", ""),
    ("getgid", "__gid_t(void)", "", ""),
    ("getgroups", "int(int, __gid_t *)", "", ""),
    ("getlogin", "char *(void)", "", ""),
    ("getpgrp", "__pid_t(void)", "", ""),
    ("getpid", "__pid_t(void)", "", ""),
    ("getppid", "__pid_t(void)", "", ""),
    ("getuid", "__uid_t(void)", "", ""),
    ("isatty", "int(int)", "int32_t(int32_t)", "extern fn isatty(a : i32) -> i32"),
    ("link", "int(const char *, const char *)", "", ""),
    ("lseek", "__off_t(int, __off_t, int)", "", ""),
    ("pathconf", "long int(const char *, int)", "", ""),
    ("pause", "int(void)", "int32_t(void)", "extern fn pause() -> i32"),
    ("pipe", "int(int *)", "", ""),
    ("read", "ssize_t(int, void *, size_t)", "int64_t(int32_t,void *,uint64_t)", "extern fn read(a : i32, b : ptr<normal, rw> T, c : u64) -> i64"),
    ("rmdir", "int(const char *)", "", ""),
    ("setgid", "int(__gid_t)", "", ""),
    ("setpgid", "int(__pid_t, __pid_t)", "", ""),
    ("setsid", "__pid_t(void)", "", ""),
    ("setuid", "int(__uid_t)", "", ""),
    ("sleep", "unsigned int(unsigned int)", "uint32_t(uint32_t)", "extern fn sleep(a : u32) -> u32"),
    ("sysconf", "long int(int)", "int64_t(int32_t)", "extern fn sysconf(a : i32) -> i64"),
    ("tcgetpgrp", "__pid_t(int)", "", ""),
    ("tcsetpgrp", "int(int, __pid_t)", "", ""),
    ("ttyname", "char *(int)", "", ""),
    ("ttyname_r", "int(int, char *, size_t)", "", ""),
    ("unlink", "int(const char *)", "", ""),
    ("write", "ssize_t(int, const void *, size_t)", "int64_t(int32_t,const void *,uint64_t)", "extern fn write(a : i32, b : ptr<normal, r> T, c : u64) -> i64"),
];
