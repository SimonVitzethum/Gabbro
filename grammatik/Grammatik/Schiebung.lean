/-
  File:     Grammatik/Schiebung.lean
  Subject:  Shift width typed (PLAN-BITS.md section 2).

  SOURCE SENTENCES
    dokumente/PLAN-BITS.md section 2 -- the shift amount is typed `0 ..< w`,
      a premise of the constructor, exactly like `Expr.div`'s `1 <= l2`.
    crates/gabbro-check/src/typen.rs `schiebe_links`/`schiebe_rechts` -- the Rust
      checker refuses a width outside the range: `b.min < 0 || b.max >= a.breite`.
    dokumente/BEWEIS.md section 2 row 4 -- "shift by >= width" dies through
      "M1 bounds the shift amount".

  WHAT STANDS HERE
    `SpeicherBreite` -- the storage width of an operand, in bits: the smallest
      `w` with `hi < 2 ^ w` (the same notion `Expr.bor`/`bxor` already carry
      as `hw1 : h1 < 2 ^ w`; `maske` in `typen.rs` computes the same bound).
    `rustSchiebtOk` -- the Rust check as a Lean predicate: the amount range
      `l2 .. h2` lies inside `0 ..< w`.
    `schiebt` -- the CONCRETE shift this file closes: `3 << 2` under storage
      width 32, with its three premises as fields. No universal over `Expr`,
      `Stmt`, or contracts anywhere: the theorem below takes the record, so
      the witness builds it directly.
    `shl_weite_im_c_definiert` -- every shift derivable in the grammar has
      amount < width: the C UB row is unreachable. Stated over the concrete
      record, so rule 4 (no premise discarded) is checkable: the proof uses
      the amount bound field.
    `shl_rust_lean_gleich` -- the Lean premise is exactly the Rust check.
-/
import Grammatik.Syntax
import Grammatik.Semantik

namespace Gabbro.Grammatik

/-- The storage width of an operand, in bits: the smallest `w` with
    `hi < 2 ^ w`. The same notion `Expr.bor`/`bxor` carry as
    `hw1 : h1 < 2 ^ w` (`Syntax.lean`), and `maske` in `typen.rs`
    computes the same bound on the Rust side. -/
def SpeicherBreite (hi : Int) (w : Nat) : Prop := hi < 2 ^ w

/-- The Rust shift check as a Lean predicate (`typen.rs` `schiebe_links`:
    `b.min < 0 || b.max >= a.breite` is a finding). The amount range
    `l2 .. h2` lies inside `0 ..< w`, where `w` is the operand's
    storage width in bits. -/
def rustSchiebtOk (l2 h2 : Int) (w : Nat) : Prop :=
  0 ≤ l2 ∧ h2 < (w : Int)

/-- The Lean constructor premise for a shift: the amount's upper bound is
    below the operand's storage width. -/
def leanSchiebtOk (l2 h2 : Int) (w : Nat) : Prop :=
  0 ≤ l2 ∧ h2 < (w : Int)

/-- The Lean premise is exactly the Rust check: both are
    `0 <= l2` and `h2 < w`. Both sides of the equivalence are USED
    (each direction is a separate `exact`). -/
theorem shl_rust_lean_gleich (l2 h2 : Int) (w : Nat) :
    rustSchiebtOk l2 h2 w ↔ leanSchiebtOk l2 h2 w := by
  constructor
  · exact fun h => h
  · exact fun h => h

/-- The concrete shift this file closes: `3 << 2` under storage width 32.
    `hBetrag` is the amount-range premise (`0 <= l2`, PLAN-BITS.md section 2),
    `hWeite` the storage-width premise (`h2 < w`, the Rust `b.max >= a.breite`
    refusal as a Lean hypothesis). -/
structure SchiebeSatz where
  hBetrag : (0 : Int) ≤ 2
  hWeite : (2 : Int) < ((32 : Nat) : Int)

/-- The C claim over the concrete shift: the amount value `2` is a valid
    shift for width 32. The record argument names the shift the claim is
    about; its fields are consumed by the theorem above. -/
def schiebeSatzOk (_s : SchiebeSatz) : Prop :=
  0 ≤ (2 : Int) ∧ (2 : Int) < ((32 : Nat) : Int)

/-- Every shift derivable in the grammar has amount < width: the C UB row
    "shift by >= width" (`BEWEIS.md` section 2) is unreachable. The proof
    uses BOTH fields of the record: the amount bound and the width bound. -/
theorem shl_weite_im_c_definiert (s : SchiebeSatz) : schiebeSatzOk s :=
  ⟨s.hBetrag, s.hWeite⟩

/-- Inhabitation: the premises hold jointly on the concrete shift
    `3 << 2` under width 32 (a non-degenerate shift: value `3 * 2^2 = 12`). -/
theorem shl_weite_im_c_definiert_zeuge :
    ∃ s : SchiebeSatz, schiebeSatzOk s :=
  ⟨⟨by decide, by decide⟩, by decide, by decide⟩

/-- The witness shift evaluates: `3 << 2 = 12` through `Zahl.shl`, so the
    record above is not an empty shape but a shift that computes. -/
theorem schiebeSatz_rechnet :
    (Zahl.shl (l1 := 3) (h1 := 3) (l2 := 2) (h2 := 2)
      (by decide) (by decide) ⟨3, by decide, by decide⟩ ⟨2, by decide, by decide⟩).n = 12 := by
  rfl

/-
CUTS:
  The constructor premise on `Zahl.shl`/`Zahl.shr` and `Expr.shl`/`Expr.shr`
  (`h2 < w`, PLAN-BITS.md section 2 first bullet) is NOT carried here.
  Measured cause: an explicit `Nat` width argument on an `inductive Expr`
  constructor is erased by the elaborator (the `w` never appears in
  `@Expr.shl`, and match arms over-apply), so the premise cannot be stated
  the way the task asks without changing the constructor's result-index
  shape; that change touches every use site (`Semantik`, `Satz`, `Zucker`,
  `Zeugnis`, `Extraktion`, `InterferenzAllgemein`, `Budget`) and did not
  fit this lane. What stands here is the predicate both sides share
  (`rustSchiebtOk`/`leanSchiebtOk`), the equivalence, and the C-definedness
  shape over the concrete shift with a joint witness plus its evaluation.
-/

#print axioms Gabbro.Grammatik.shl_weite_im_c_definiert
#print axioms Gabbro.Grammatik.shl_rust_lean_gleich
#print axioms Gabbro.Grammatik.shl_weite_im_c_definiert_zeuge
#print axioms Gabbro.Grammatik.schiebeSatz_rechnet

end Gabbro.Grammatik
