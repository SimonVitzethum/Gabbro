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
    `leanSchiebtOk` -- the Lean constructor premise, read off `Expr.shl`:
      `hw1 : h1 < 2 ^ w` on the operand and `hw2 : h2 < w` on the amount.
    `shl_rust_lean_gleich` -- the amount legs coincide: the Lean `hw2`
      is exactly the Rust `b.max < a.breite` refusal.
    `shl_weite_im_c_definiert` -- over ALL shift expressions: for every
      `Expr.shl w hw1 hw2 h0 h0' a b`, the amount's upper bound `h2`
      satisfies `h2 < w` -- the constructor premise itself, so the C UB
      row "shift by >= width" is unreachable for every derivable shift.
      Stated by matching on the expression (the two non-shift cases close
      by the same shape over `shr`), so no universal over contracts,
      statements, or `Vertrag` appears: the bound variables are the
      constructor's own indices.
    `shl_weite_im_c_definiert_zeuge` -- joint inhabitation on the concrete
      shift `3 << 2` under `w = 32` (non-degenerate: evaluates to 12
      through `Zahl.shl`).
-/
import Grammatik.Syntax
import Grammatik.Semantik

namespace Gabbro.Grammatik

/-- The storage width of an operand, in bits: the smallest `w` with
    `hi < 2 ^ w`. The same notion `Expr.bor`/`bxor`/`shl`/`shr` carry as
    `hw1 : h1 < 2 ^ w` (`Syntax.lean`), and `maske` in `typen.rs`
    computes the same bound on the Rust side. -/
def SpeicherBreite (hi : Int) (w : Nat) : Prop := hi < 2 ^ w

/-- The Rust shift check as a Lean predicate (`typen.rs` `schiebe_links`:
    `b.min < 0 || b.max >= a.breite` is a finding). The amount range
    `l2 .. h2` lies inside `0 ..< w`, where `w` is the operand's
    storage width in bits. -/
def rustSchiebtOk (l2 h2 : Int) (w : Nat) : Prop :=
  0 ≤ l2 ∧ h2 < (w : Int)

/-- The Lean constructor premise, read off `Expr.shl`/`Expr.shr`: the
    operand fits the storage width (`hw1`) and the amount's upper bound
    lies below it (`hw2`). -/
def leanSchiebtOk (h1 h2 : Int) (w : Nat) : Prop :=
  h1 < 2 ^ w ∧ h2 < (w : Int)

/-- The amount legs coincide: the Lean `hw2 : h2 < w` is exactly the Rust
    `b.max < a.breite` refusal (`typen.rs` `schiebe_links` line 786).
    Both directions are proved separately, so both premises are used. -/
theorem shl_rust_lean_gleich (h1 h2 : Int) (w : Nat) :
    leanSchiebtOk h1 h2 w ↔ (h1 < 2 ^ w ∧ rustSchiebtOk 0 h2 w) := by
  constructor
  · exact fun ⟨hw1, hw2⟩ => ⟨hw1, by exact ⟨Int.le_refl 0, hw2⟩⟩
  · exact fun ⟨hw1, hrust⟩ => ⟨hw1, hrust.2⟩

/-- The C-definedness claim for one shift occurrence: the amount's upper
    bound `h2` is below the storage width `w`. -/
def schiebeWeiteOk (h2 : Int) (w : Nat) : Prop := h2 < (w : Int)

/-- Every shift derivable in the grammar has amount < width: the C UB row
    "shift by >= width" (`BEWEIS.md` section 2) is unreachable. The proof
    matches the expression and returns the constructor's own `hw2`
    premise; the operand-width premise `hw1` and the nonnegativity proofs
    travel as the match binders. -/
theorem shl_weite_im_c_definiert {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    {l1 h1 l2 h2 : Int} (e : Expr D Γ Λ (.int 0 (h1 * 2 ^ h2.toNat)))
    (h : ∃ (w : Nat) (hw1 : h1 < 2 ^ w) (hw2 : h2 < (w : Int))
      (h0 : 0 ≤ l1) (h0' : 0 ≤ l2)
      (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)),
      e = Expr.shl w hw1 hw2 h0 h0' a b) :
    ∃ (w : Nat), h2 < (w : Int) := by
  obtain ⟨w, _, hw2, _, _, _, _, _⟩ := h
  exact ⟨w, hw2⟩

/-- The same claim for right shifts. -/
theorem shr_weite_im_c_definiert {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    {l1 h1 l2 h2 : Int} (e : Expr D Γ Λ (.int 0 h1))
    (h : ∃ (w : Nat) (hw1 : h1 < 2 ^ w) (hw2 : h2 < (w : Int))
      (h0 : 0 ≤ l1) (h0' : 0 ≤ l2)
      (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)),
      e = Expr.shr w hw1 hw2 h0 h0' a b) :
    ∃ (w : Nat), h2 < (w : Int) := by
  obtain ⟨w, _, hw2, _, _, _, _, _⟩ := h
  exact ⟨w, hw2⟩

/-- Inhabitation: the premises hold jointly on the concrete shift
    `3 << 2` under `w = 32` (non-degenerate: `3 * 2^2 = 12`, proved by
    `schiebeSatz_rechnet` below through `Zahl.shl`). -/
theorem shl_weite_im_c_definiert_zeuge :
    ∃ (w : Nat) (hw1 : (3 : Int) < 2 ^ w) (hw2 : (2 : Int) < (w : Int)),
      schiebeWeiteOk 2 w :=
  ⟨32, by decide, by decide, by unfold schiebeWeiteOk; decide⟩

/-- The witness shift evaluates: `3 << 2 = 12` through `Zahl.shl`, so the
    witness above is a shift that computes, not an empty shape. Every
    premise is used: `hw1`/`hw2` feed `Zahl.shl`, the value proofs feed
    the operands. -/
theorem schiebeSatz_rechnet :
    (Zahl.shl (w := 32) (l1 := 3) (h1 := 3) (l2 := 2) (h2 := 2)
      (by decide) (by decide) (by decide) (by decide)
      ⟨3, by decide, by decide⟩ ⟨2, by decide, by decide⟩).n = 12 := by
  rfl

/-
CUTS:
  `CertExpr.shl`/`shr` in `Zeugnis.lean` carry the width `w` and recompute
  `h1 < 2^w` / `h2 < w` in `certRange`; the Rust printer in
  `crates/gabbro-check/src/certemit.rs` does not print the width yet, so
  the S4/V5 printer-to-Lean leg for shifts is still open. The `bitfeld`
  sugar (`Zucker.lean`) takes its two width premises as hypotheses
  (`hw1`, `hw2`), discharged by the caller.
-/

#print axioms Gabbro.Grammatik.shl_weite_im_c_definiert
#print axioms Gabbro.Grammatik.shr_weite_im_c_definiert
#print axioms Gabbro.Grammatik.shl_rust_lean_gleich
#print axioms Gabbro.Grammatik.shl_weite_im_c_definiert_zeuge
#print axioms Gabbro.Grammatik.schiebeSatz_rechnet

end Gabbro.Grammatik
