//! **`~` -- and the only question is the WIDTH.**
//!
//! The emitter writes `({c})~({c})(x)` and not a bare `~`. The reason is the integer
//! promotion: C lifts every operand narrower than `int` up to `int`, and `~(uint16_t)0xF0F0`
//! is `0xFFFF0F0F` there instead of `0x0F0F`.
//!
//! **This file measures that on a RUNNING program**, because neither the text probe alone
//! nor the return-value probe alone can:
//!
//! * *Measured 2026-09-01:* with and without the casts, `maske8`, `falte`, `maske32` and
//!   `loesche` yield **the same numbers** -- the `uint8_t`/`uint16_t` return type truncates
//!   the promotion away again. **A probe that measures the same thing in both directions
//!   measures nothing.**
//! * It becomes visible only where the complement's value is used without being cut back:
//!   in a COMPARISON (`~b == 3855`) and in a WIDENING (`let w : u32 = ~b;`).
//! * And `cc -Wall -Wextra -Werror` catches **exactly one** of those two: at the comparison
//!   `-Wsign-compare` fires; at the widening it compiles without a word and computes
//!   `4294905615`, where M1 says `u16 in 0 .. 65535`.
//!
//! > *A guardian that catches only the one case covers half of it* -- and that is why a RUN
//! > stands here and not a compilation.
//!
//! **The second half of the same item stands at the bottom of this file**: `u32::max` in an
//! expression. It is the same question -- a mask and its width -- and it had the same shape
//! of defect: the `const` path folded it, nobody else asked, and the expression path lowered
//! a WORD of the vocabulary as if it were a place.

use gabbro_syntax::diag::Stufe;
use std::path::PathBuf;
use std::process::Command;

fn wurzel() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|p| p.parent())
        .expect("the tree lies two levels above the crate")
        .to_path_buf()
}

const TREIBER: &str = r#"
#include <stdio.h>

int main(void) {
    int abweichungen = 0;
#define P(name, wert, gemeint) \
    do { unsigned long g = (unsigned long)(wert); \
         if (g != (unsigned long)(gemeint)) { abweichungen++; \
             printf("ABWEICHUNG %s: geliefert=%lu gemeint=%lu\n", name, g, (unsigned long)(gemeint)); } \
    } while (0)
    /* ~0xF0 over eight bits */
    P("maske8", maske8(240u), 15u);
    /* RFC 1071: 0x0001 + 0x0002 = 3, complement 0xFFFC */
    P("falte", falte(0x00010002u), 65532u);
    /* the double fold: 0xFFFF + 0xFFFF folds to 0xFFFF, complement 0 */
    P("falte-rand", falte(0xFFFFFFFFu), 0u);
    P("maske32", maske32(240u), 4294967055u);
    P("loesche", loesche(0xFF0Fu, 0x0F0Fu), 61440u);
    /* THE two rows that carry the claim: without the cast the promotion is visible */
    P("vergleich", (unsigned)ist_gleich(0xF0F0u), 1u);
    P("verbreiterung", verbreitert(0xF0F0u), 3855u);
    /* the exact range: ~(u8 in 0..15) is u8 in 240..255, and the declaration says so */
    P("nibble", hohes_nibble(5u), 250u);
    printf("geprueft=8 abweichungen=%d\n", abweichungen);
    return 0;
}
"#;

const GRENZTREIBER: &str = r#"
#include <stdio.h>

int main(void) {
    int abweichungen = 0;
#define Q(name, wert, gemeint) \
    do { long long g = (long long)(wert); \
         if (g != (long long)(gemeint)) { abweichungen++; \
             printf("ABWEICHUNG %s: geliefert=%lld gemeint=%lld\n", name, g, (long long)(gemeint)); } \
    } while (0)
    Q("invertiere", invertiere(0x0F0F0F0Fu), 4042322160u);
    Q("passt-ja",   passt_in_16(65535u), 1);
    Q("passt-nein", passt_in_16(65536u), 0);
    Q("min-ja",     ist_kleinster(-2147483647 - 1), 1);
    Q("min-nein",   ist_kleinster(0), 0);
    /* the two spellings of one mask have to be one number */
    Q("zwei-wege",  zwei_wege_eine_maske(240u), 1);
    printf("geprueft=6 abweichungen=%d\n", abweichungen);
    return 0;
}
"#;

// ---------------------------------------------------------------------------------------
// **No null spelling in the emitted C of `beispiele/38` -- lane 145.**
//
// Until 2026-09-13 the file bound its pointer as
// `static tz : ptr<normal, rw> Platz = 0;`, which lowered to
// `static Platz * const tz = (Platz *)(uintptr_t)0;` -- still a null pointer
// constant (C11 6.3.2.3p3), so the store below it was undefined behaviour
// (C11 6.5.3.2p4; UBSan: `member access within null pointer`). The
// `(uintptr_t)` cast changed the spelling, not the address. The checker now
// refuses that declaration with `N260`
// (`beispiele/gift/931-null-pointer-through-an-immutable-static.gab`), and
// the file binds its pointer to declared storage instead
// (`let tz : ptr<normal, rw> Platz = SPEICHER;`).
//
// **This probe pins the after-state**: the write through the pointer is still
// there, and no null spelling is. It falls in both directions -- a returning
// `(uintptr_t)0`, or a lost store.
// ---------------------------------------------------------------------------------------

const W1CTREIBER: &str = r#"
#include <stdio.h>
#include <string.h>

int main(void) {
    /* A stand-in for the register window. Enough to tell the two lowerings apart: the
       question is not what the device does with the word, it is WHICH word gets written. */
    static volatile uint8_t fenster[256];
    memset((void *)fenster, 0, sizeof fenster);
    Vtd v = { fenster };
    /* Both error bits are standing, and the index says entry 7. */
    *(volatile uint32_t *)(fenster + 0x34) = 0x0703u;
    if (fehlerindex(&v) != 7u) { printf("INDEX FALSCH\n"); return 1; }
    fehler_quittieren(&v);
    unsigned geschrieben = (unsigned)*(volatile uint32_t *)(fenster + 0x34);
    /* 1 = a one at PFO alone.  3 = a one at PPF too, and on the device that clears an
       error nobody acknowledged. */
    printf("quittiert=%u\n", geschrieben);
    return 0;
}
"#;
