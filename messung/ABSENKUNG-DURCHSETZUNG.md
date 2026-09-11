# Lowering enforcement — per-primitive statement budget in `absenkung.rs`

Date: `2026-09-11`. Base: `6f26e76`. Lane: `lane-145`.

The lowering contract in `grammatik/Grammatik/Ziel.lean` assumes every
Gabbro primitive lowers to a bounded list of C forms (`proPrimitiv <=
18`, witnessed by the measured maximum `17`). Until now nothing in the
checker held the emitter to that number: a primitive that lowered to
`19` statements would emit, compile, and pass, and no line would say
the contract no longer holds. This file books the enforcement — the
mechanism, the hook that applies it, and what is still missing.

Scope kept: two files created, none edited. `crates/gabbro-check/src/`
gains `absenkung.rs`; this file is the other. In particular `lib.rs`
carries no new `mod` line (the pass list and the module register are
owned centrally) and `emit.rs` carries no new call (the hook below is
specified, not applied).

## 1. The bound and where it comes from

```
proPrimitiv : Nat
begrenzt : proPrimitiv <= 18
def absenkung : Absenkung := ⟨17, by decide⟩
```

`17` is the statically counted maximum per Gabbro primitive, at
`Schleife`, subform `traverse over descendants of` (`nachfahren`,
`emit.rs:8523-8560`); `18` is that maximum plus one headroom. Both
figures are from `messung/ABSENKUNG-MESSUNG.md` section 4, recounted in
`messung/ABSENKUNG-SCHRANKEN-ENTSCHEID.md` section 2 (`3 + 3 + 1 + 2 +
4 + 2 + 2 = 17`). The module repeats them as constants, not as
parameters:

```
STATEMENTS_PER_PRIMITIVE = 18
MEASURED_MAXIMUM = 17
```

A bound passed as an argument is a bound the caller can move; a bound
written as a constant beside the Lean sentence is a bound a reader can
hold against it. The headroom direction is fixed the same way: the
runtime lexer pass (`messung/ABSENKUNG-ZAEHLUNG.md` section 2) can only
confirm `17` or raise it, never lower it below `17`. A rise to `18`
fits the bound; a rise past `18` moves the bound again — in `Ziel.lean`
first, here second.

## 2. The enforcement mechanism

The module (`crates/gabbro-check/src/absenkung.rs`, `std` only, no
crate imports) has three public items:

```
count_c_statements(c: &str) -> usize
check_primitive(primitive: &str, emitted: &str) -> Result<usize, OverBudget>
PRIMITIVES: [&str; 17]
```

`count_c_statements` is the measurement lexer, moved into the checker:
one `;` in emitted C text is one statement, with three exclusions from
`messung/ABSENKUNG-MESSUNG.md` section 1 (`for (...; ...; ...)`
header separators, `//` and `/* */` comment text, refusal strings —
which never reach the output buffer) plus a fourth the static
measurement never needed: `;` inside string and character literals
(`"a;b"`, `';'`). The static pass read format strings out of the
emitter source, where no literal carries a `;`; the enforcement reads
emitted text, where one someday could. Excluding them refuses LESS,
and the direction is booked in the module head rather than hidden in
the lexer.

`check_primitive` holds one primitive against the bound: it counts the
statements in the fragment the emitter produced for exactly that
primitive, returns the count when it fits, and refuses when it does
not. The refusal (`OverBudget`) names the primitive, the counted
statements, the bound, and the first `512` characters of the emitted
fragment — the named C code beside the refusal, not the whole file
behind it. Twelve unit tests inside the module cover the boundary
(`17` held, `18` held, `19` refused), each lexer exclusion, the
17-row registry, and the no-early-stop property: statements past the
bound are still counted, so the refusal states the true count, not
the bound plus one.

`PRIMITIVES` is the seventeen `StmtArt` variant names in enum order —
the row registry the hook maps each lowering arm to. One row per
variant, no more: a primitive the emitter lowers without an arm has
no row, and the hook has nowhere to hang its name.

## 3. The hook specification — the ONE call site

The enforcement is applied in exactly one place, and it is not in
this lane. Call site: `emit.rs`, `fn anweisung` (`emit.rs:6654-7755`):

```
fn anweisung(
    s: &Stmt,
    aus: &mut String,
    u: &Namen,
    absagen: &mut Absagen,
    tiefe: usize,
    austritt: &Austritt,
)
```

`Stmt` carries both facts the hook needs (`pub struct Stmt { pub art:
StmtArt, pub span: Span }`, `crates/gabbro-syntax/src/ast.rs:1158`):
the variant for the row name, the span for the refusal. The buffer
`aus` is shared across statements, so the hook slices it: one line at
the top of `anweisung` records the mark, one line at the bottom checks
the slice. Signature of the central wrapper, beside `anweisung` in
`emit.rs`:

```
fn absenkung_anwenden(s: &Stmt, fragment: &str, absagen: &mut Absagen)
```

Concretely, central adds:

```
let marke = aus.len();                       // top of `anweisung`
absenkung_anwenden(s, &aus[marke..], absagen); // bottom of `anweisung`

fn absenkung_anwenden(s: &Stmt, fragment: &str, absagen: &mut Absagen) {
    let name = match &s.art {
        StmtArt::Let(_) => "Let",
        // ... one arm per variant, names from `absenkung::PRIMITIVES`
    };
    if let Err(zu_viel) = crate::absenkung::check_primitive(name, fragment) {
        weigere(absagen, s.span, &zu_viel.to_string());
    }
}
```

The refusal reuses the existing emitter refusal `weigere`
(`emit.rs:2542`), which issues `C001 "no lowering: {was}"`. No new
refusal code, no new pass, no new register: an over-budget primitive
reads like every other named refusal of the emitter, and the
`OverBudget` display text is written to fit that slot.

Why the slice and not the whole buffer: nested body statements are
booked on the body, not on the row (`messung/ABSENKUNG-MESSUNG.md`
section 1). `&aus[marke..]` holds exactly the scaffold the primitive
itself emitted for this statement — the same direct-scaffold reading
the `17` was counted under. Counting the whole buffer would charge
every primitive for its sisters.

## 4. What was expressly not done here

- No registration: `lib.rs` is untouched, so the module compiles
  standalone and `cargo check -p gabbro-check` reads the crate
  unchanged. The module is written to compile unchanged the day
  central adds the single `pub mod absenkung;` line — `std` only, no
  crate names anywhere.
- No application: `emit.rs` is untouched. The hook above is a
  specification with line numbers and a signature, not a call.
- No new refusal code and no new pass number: the refusal is `C001`
  through `weigere`, and the module owns no sentences.
- No bound change: `STATEMENTS_PER_PRIMITIVE` repeats the `18` from
  `Ziel.lean`; it does not re-derive it.
- The runtime half of `messung/ABSENKUNG-ZAEHLUNG.md` section 2
  (minimal units, real `emit` outputs, one lexer) is still missing.
  When it lands and confirms `17`, the hook turns from specified to
  applied with the numbers already in place; when it raises the
  maximum past `18`, the bound moves first in `Ziel.lean`, then here.

Evidence beside the mechanism: `rustc --test` over the single new
file (twelve tests, all green), `cargo check -p gabbro-check` over
the untouched crate (green). No build of the full workspace, no
`emit` run, no Lean invocation took place.
