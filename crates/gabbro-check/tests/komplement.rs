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

