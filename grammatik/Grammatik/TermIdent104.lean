/-
  File:     Grammatik/TermIdent104.lean
  Subject:  Term identity, Rust half (differential, lane 158).

  Lane 149 proved the Lean half (`ZeugnisIdent.lean`: `printInt` followed by
  `elabInt` round-trips) and named the remaining trust base: that
  `certemit.rs` prints exactly `printInt e` for the checked `e`. This file
  is the differential witness: for each `CertExpr` shape the Rust printer
  (`crates/gabbro-check/src/certemit.rs`, `CertExpr::print`) can emit, a
  checked Lean term `e` with `printInt e = some c` by `rfl`, where `c` is
  written EXACTLY as the Rust printer spells it (verified against the
  `print` arms and unit tests of `certemit.rs`). The first program that
  works is `beispiele/104-referenz.gab` (`const NKONTO : u32 = 2`, witness
  1 below); the only `CertExpr` the Rust side emits for the corpus today
  is `CertExpr::Lit` via `konst_zertifikate` (`emit.rs:2909`).

  CHECK
    ./lean-probe grammatik/Grammatik/TermIdent104.lean
-/
import Grammatik.ZeugnisIdent
import Grammatik.ReferenzB

namespace Gabbro.Grammatik

/-- Differential witness 1 (first program that works):
    `beispiele/104-referenz.gab` declares `const NKONTO : u32 = 2`, and the
    only `CertExpr` the Rust side emits for the corpus today is
    `CertExpr::Lit` via `konst_zertifikate` (`emit.rs:2909`), printing
    `(.lit 2)`. The Lean side prints the checked literal identically. -/
example : printInt (D := refD) (Γ := []) (Λ := []) (Expr.lit 2)
    = some (CertExpr.lit (D := refD) 2) := rfl

/-- Differential witness 2: Rust `Add(lit 2, lit 3)` prints
    `(.add (.lit 2) (.lit 3))` (`certemit.rs` unit test
    `add_prints_and_sums_bounds`); the Lean side prints the same. -/
example : printInt (D := refD) (Γ := []) (Λ := [])
    (Expr.add (Expr.lit 2) (Expr.lit 3))
    = some (CertExpr.add (D := refD) (.lit 2) (.lit 3)) := rfl

/-- Differential witness 3: Rust `Div(lit 7, lit 2)` prints
    `(.div (.lit 7) (.lit 2))` (`div_prints_and_claims_zero_to_hi`); the
    Lean side prints the same (side proofs by `decide`, recomputed). -/
example : printInt (D := refD) (Γ := []) (Λ := [])
    (Expr.div (by decide) (by decide) (Expr.lit 7) (Expr.lit 2))
    = some (CertExpr.div (D := refD) (.lit 7) (.lit 2)) := rfl

/-- Differential witness 4: Rust `Band(lit 6, lit 3)` prints
    `(.band (.lit 6) (.lit 3))` (`band_prints_and_claims`). -/
example : printInt (D := refD) (Γ := []) (Λ := [])
    (Expr.band (by decide) (by decide) (Expr.lit 6) (Expr.lit 3))
    = some (CertExpr.band (D := refD) (.lit 6) (.lit 3)) := rfl

/-- Differential witness 5: Rust `Bor(3, lit 6, lit 3)` prints
    `(.bor 3 (.lit 6) (.lit 3))` (`bor_prints_with_width_and_claims_full_width`). -/
example : printInt (D := refD) (Γ := []) (Λ := [])
    (Expr.bor (w := 3) (l1 := 6) (h1 := 6) (l2 := 3) (h2 := 3)
      (by decide) (by decide) (by decide) (by decide)
      (Expr.lit 6) (Expr.lit 3))
    = some (CertExpr.bor (D := refD) 3 (.lit 6) (.lit 3)) := rfl

/-- Differential witness 6: Rust `Bxor(3, lit 6, lit 3)` prints
    `(.bxor 3 (.lit 6) (.lit 3))` (`bxor_prints_with_width_and_claims_full_width`). -/
example : printInt (D := refD) (Γ := []) (Λ := [])
    (Expr.bxor (w := 3) (l1 := 6) (h1 := 6) (l2 := 3) (h2 := 3)
      (by decide) (by decide) (by decide) (by decide)
      (Expr.lit 6) (Expr.lit 3))
    = some (CertExpr.bxor (D := refD) 3 (.lit 6) (.lit 3)) := rfl

/-- Differential witness 7 (MISMATCH, see the script report): the Lean side
    prints the width (`shl_prints_and_scales_by_shift` on the Rust side
    prints `(.shl (.lit 3) (.lit 2))` with NO width, which is not a
    `CertExpr.shl` term). What the Lean side prints for the checked term: -/
example : printInt (D := refD) (Γ := []) (Λ := [])
    (Expr.shl (w := 3) (l1 := 3) (h1 := 3) (l2 := 2) (h2 := 2)
      (by decide) (by decide) (by decide) (by decide)
      (Expr.lit 3) (Expr.lit 2))
    = some (CertExpr.shl (D := refD) 3 (.lit 3) (.lit 2)) := rfl

/-- Differential witness 8 (MISMATCH, same cause as witness 7): the Lean
    side prints the width; Rust `Shr(lit 12, lit 2)` prints
    `(.shr (.lit 12) (.lit 2))` (`shr_prints_and_claims`). -/
example : printInt (D := refD) (Γ := []) (Λ := [])
    (Expr.shr (w := 4) (l1 := 12) (h1 := 12) (l2 := 2) (h2 := 2)
      (by decide) (by decide) (by decide) (by decide)
      (Expr.lit 12) (Expr.lit 2))
    = some (CertExpr.shr (D := refD) 4 (.lit 12) (.lit 2)) := rfl

/-- Differential witness 9: Rust `Wide(0, 7, lit 3)` prints
    `(.wide 0 7 (.lit 3))` (`wide_narrows_within_bounds`). -/
example : printInt (D := refD) (Γ := []) (Λ := [])
    (Expr.weiter (lo' := 0) (hi' := 7) (lo := 3) (hi := 3)
      (by decide) (by decide) (Expr.lit 3))
    = some (CertExpr.wide (D := refD) 0 7 (.lit 3)) := rfl

/-- Differential witness 10: Rust `Var(0)` against context `[(3, 3)]`
    prints `(.var 0)` (`var_reads_the_context`). -/
example : printInt (D := refD) (Γ := [.int 3 3]) (Λ := [])
    (Expr.var Var.hier)
    = some (CertExpr.var (D := refD) 0) := rfl

/-- Differential witness 11: Rust `Slot(t, f, Wide(0, count - 1, lit))`
    prints `(.slot t f (.wide 0 (count - 1) (.lit …)))`
    (`slot_reads_field_under_exact_index_shape`); the Lean side prints the
    same shape on the fixture table (count 2, index `0 .. 1`). Table and
    field travel as constructors here (`()`, `()`) and as names there
    (`Konto`, `stand`): same shape, different spelling of the carrier. -/
example : printInt (D := refD) (Γ := [.int 0 10]) (Λ := [Res.held (D := refD) ()])
    (Expr.slot () () refIdxEin refDarf)
    = some (CertExpr.slot (D := refD) () () (.wide 0 1 (.lit 0))) := rfl

/-- Differential witness 12: Rust `Glob(g)` prints `(.glob g)`
    (`glob_reads_carrier_and_guard`). The fixture has no globals
    (`refD.Glob := Empty`), so there is no concrete fixture term; the shape
    is checked generically instead (no premise quantifies over program
    syntax, so no rule-13 witness is owed: `D` is a declaration, `g` one
    of its globals, both used). -/
example (D : Deklaration) (g : D.Glob) (h : gdarf D g [])
    : printInt (D := D) (Γ := []) (Λ := []) (Expr.glob g h)
    = some (CertExpr.glob (D := D) g) := rfl

/-
  CUTS: what is not proved here.
  - Every `CertExpr` shape the Rust printer (`certemit.rs`) can emit is
    witnessed above (`lit`, `add`, `div`, `band`, `bor`, `bxor`, `shl`,
    `shr`, `wide`, `var`, `slot`, `glob`) -- except that the Rust
    `shl`/`shr` prints carry NO width while `CertExpr.shl/shr` (and
    `printInt`) do (witnesses 7-8 state the Lean-side truth; the Rust
    strings `(.shl …)`/`(.shr …)` with two arguments are not `CertExpr`
    terms at all). That mismatch is a finding of the differential script
    (`instrumente/pruefe-termidentitaet.py`), not weakened here.
  - The Rust side has NO `sub`/`neg`/`mul`/`rem`/`sdiv`/`srem` variants
    while `printInt` prints them: nothing to compare, booked in the script
    report (same gap as `ZeugnisIdent.lean` CUTS).
  - Table/field carriers travel as constructors here and as names there
    (witness 11): the shape is identical, the spelling differs by
    construction of the two printers.
  - The Lean half (`print_elab_all`) applies exactly where the Rust print
    equals `printInt e`; this file exhibits the equality per shape but does
    not prove the Rust printer reads the checked term (that implication is
    not in Lean: it is the trust base lane 149 booked).
-/

end Gabbro.Grammatik
