/-
  File:      Grammatik/Speichermodell/DarstellungTy.lean
  Subject:   The Lean side of the minimal-width / packed data layout,
             at the type level (agent 03, usability/efficiency team).

  `Darstellung.lean` proves the layout over bare `Int` ranges;
  `encW` (below) encodes Gabbro values as integers.
  This file joins them: `tyBits` (bits per `Ty`, with the `option`
  sentinel and the `grund` case count as values), `encN` (the offset
  encoding of a value), the fit (`encN_lt`), the round trip
  (`decN_encN`), the narrow cell (`narrowCell`, `narrow_fits`,
  `narrow_le_wide`), and packed arrays (`getCell`/`setCell` with
  non-interference, `packBytes_cells`). Over every type, no program
  named. Nothing here is an Arm instruction fact; Sail citations do
  not apply (rule 7 N/A, recorded in CUTS).
-/
module
public import Grammatik.Speichermodell.Darstellung
public import Grammatik.Kern.Syntax.Typen.Teil2
@[expose] public section


namespace Gabbro.Grammatik

/-- The integer encoding of an `option index into T`: the index, or the sentinel `n`
    (`T_NONE`) for `none`. -/
def encOpt (n : Int) : Option (Zahl 0 (n - 1)) → Int
  | none => n
  | some z => z.n

/-- The integer encoding of a Gabbro value: the number for ranges, `0`/`1` for `bool`, the index
    or the sentinel `N` for `option index into T`, the case number for `reason`. The remaining
    types have no integer cell. (Until 2026-10-18 this lived in `CSpeicher.lean`, the C memory
    model, deleted with the C emitter.) -/
def encW {F : Type} {sig : F → Nat → Bool} : (τ : Ty) → Val F sig τ → Int
  | .int _ _, v => Zahl.n v
  | .bool, b => if (show Bool from b) then 1 else 0
  | .opt n, o => encOpt n o
  | .why n, i => ((show Fin n from i) : Nat)
  | .ref _, r => (Val.zelle r : Int)
  | _, _ => 0

end Gabbro.Grammatik

namespace Grammatik.Speichermodell.DarstellungTy

/-! ## 1. Bits per type, and the offset encoding of a value. -/

/-- Bits of the offset encoding of a `Ty`: ranges via `Darstellung.bits`;
    `bool` is one bit; `option` counts the sentinel `n` as a value;
    `grund n` counts its `n` cases (`n ≥ 1`, else no cell). All other
    types have no minimal-width cell. -/
def tyBits : Gabbro.Grammatik.Ty → Option Nat
  | .int lo hi => some (Grammatik.Speichermodell.Darstellung.bits lo hi)
  | .bool => some 1
  | .opt n => some (Grammatik.Speichermodell.Darstellung.bits 0 n)
  | .why n => if 1 ≤ n then
      some (Grammatik.Speichermodell.Darstellung.bits 0 ((n : Int) - 1))
      else none
  | _ => none

/-- The offset base of a type: `lo` for ranges, `0` for the rest. -/
def tyLo : Gabbro.Grammatik.Ty → Int
  | .int lo _ => lo
  | _ => 0

/-- The offset encoding of a value: `Darstellung.enc` of `encW`. -/
def encN {F : Type} {sig : F → Nat → Bool} (t : Gabbro.Grammatik.Ty)
    (v : Gabbro.Grammatik.Val F sig t) : Nat :=
  Grammatik.Speichermodell.Darstellung.enc (tyLo t)
    (Gabbro.Grammatik.encW t v)

/-! ## 2. Every value fits its bits. -/

/-- **The offset encoding of every value fits in `tyBits`.**
    Ranges via `Darstellung.enc_lt_two_pow` (with `Zahl.lo_le` /
    `le_hi`, as the range check does); `option` via `encOpt` (the sentinel
    `n` included); `grund` via `Fin`. -/
theorem encN_lt {F : Type} {sig : F → Nat → Bool} (t : Gabbro.Grammatik.Ty)
    (b : Nat) (hb : tyBits t = some b)
    (v : Gabbro.Grammatik.Val F sig t) : encN t v < 2 ^ b := by
  cases t with
  | int lo hi =>
      simp only [tyBits] at hb
      cases hb
      simp only [encN, tyLo, Gabbro.Grammatik.encW]
      exact Grammatik.Speichermodell.Darstellung.enc_lt_two_pow lo hi _
        (Gabbro.Grammatik.Zahl.lo_le v) (Gabbro.Grammatik.Zahl.le_hi v)
  | bool =>
      simp only [tyBits] at hb
      cases hb
      cases v <;> simp only [encN, tyLo, Gabbro.Grammatik.encW,
        Grammatik.Speichermodell.Darstellung.enc] <;> decide
  | opt n =>
      simp only [tyBits] at hb
      cases hb
      cases v with
      | none =>
          simp only [encN, tyLo, Gabbro.Grammatik.encW,
            Gabbro.Grammatik.encOpt,
            Grammatik.Speichermodell.Darstellung.enc]
          by_cases h : 0 ≤ n
          · exact Grammatik.Speichermodell.Darstellung.enc_lt_two_pow
              0 n n h (by omega)
          · have hpos : 0 < 2 ^ Grammatik.Speichermodell.Darstellung.bits 0 n :=
              Nat.two_pow_pos _
            omega
      | some z =>
          simp only [encN, tyLo, Gabbro.Grammatik.encW,
            Gabbro.Grammatik.encOpt]
          exact Grammatik.Speichermodell.Darstellung.enc_lt_two_pow 0 n _
            (by have h1 := Gabbro.Grammatik.Zahl.lo_le z; omega)
            (by have h2 := Gabbro.Grammatik.Zahl.le_hi z; omega)
  | why n =>
      simp only [tyBits] at hb
      split at hb
      · cases hb
        simp only [encN, tyLo, Gabbro.Grammatik.encW]
        have h1 : (0 : Int) ≤ ((v.val : Nat) : Int) := by
          exact_mod_cast Nat.zero_le _
        have h2 : ((v.val : Nat) : Int) ≤ (n : Int) - 1 := by
          have := v.isLt
          omega
        exact Grammatik.Speichermodell.Darstellung.enc_lt_two_pow 0 _ _ h1 h2
      · simp only [reduceCtorEq] at hb
  | sum _ => simp only [tyBits] at hb; simp only [reduceCtorEq] at hb
  | never => simp only [tyBits] at hb; simp only [reduceCtorEq] at hb
  | fl _ => simp only [tyBits] at hb; simp only [reduceCtorEq] at hb
  | fnptr _ => simp only [tyBits] at hb; simp only [reduceCtorEq] at hb
  | ptr _ => simp only [tyBits] at hb; simp only [reduceCtorEq] at hb
  | ref _ => simp only [tyBits] at hb; simp only [reduceCtorEq] at hb
  | arr _ _ => simp only [tyBits] at hb; simp only [reduceCtorEq] at hb
  | str _ => simp only [tyBits] at hb; simp only [reduceCtorEq] at hb
  | prod _ _ => simp only [tyBits] at hb; simp only [reduceCtorEq] at hb

/-! ## 3. The round trip (with the `option` side condition).

    `dec (tyLo t) (encN t v) = encW t v` needs, for `.opt n`, that the
    sentinel is non-negative: at `n < 0`, `encW` answers `n` while the
    offset encoding clamps to `0` (`dec 0 (enc 0 n) = 0 ≠ n`), so the
    unconditional form is false. Ranges need no condition
    (`dec_enc` takes its bounds as hypotheses, contradictory or not);
    `grund` cases come from `Fin`; the remaining types encode `0`. -/
theorem decN_encN {F : Type} {sig : F → Nat → Bool} (t : Gabbro.Grammatik.Ty)
    (v : Gabbro.Grammatik.Val F sig t)
    (hOpt : ∀ n : Int, t = .opt n → 0 ≤ n) :
    Grammatik.Speichermodell.Darstellung.dec (tyLo t) (encN t v) =
      Gabbro.Grammatik.encW t v := by
  cases t with
  | int lo hi =>
      simp only [tyLo, encN]
      exact Grammatik.Speichermodell.Darstellung.dec_enc lo hi _
        (Gabbro.Grammatik.Zahl.lo_le v) (Gabbro.Grammatik.Zahl.le_hi v)
  | bool =>
      cases v <;>
        simp only [tyLo, encN, Gabbro.Grammatik.encW,
          Grammatik.Speichermodell.Darstellung.enc,
          Grammatik.Speichermodell.Darstellung.dec] <;> decide
  | opt n =>
      cases v with
      | none =>
          have h0 := hOpt n rfl
          simp only [tyLo, encN]
          exact Grammatik.Speichermodell.Darstellung.dec_enc 0 n n h0
            (by omega)
      | some z =>
          simp only [tyLo, encN]
          exact Grammatik.Speichermodell.Darstellung.dec_enc 0
            (Gabbro.Grammatik.Zahl.n z) (Gabbro.Grammatik.Zahl.n z)
            (Gabbro.Grammatik.Zahl.lo_le z) (by omega)
  | why n =>
      simp only [tyLo, encN]
      exact Grammatik.Speichermodell.Darstellung.dec_enc 0
        ((v.val : Nat) : Int) ((v.val : Nat) : Int)
        (by exact_mod_cast Nat.zero_le _) (by omega)
  | sum _ =>
      simp only [tyLo, encN, Gabbro.Grammatik.encW]
      rfl
  | never =>
      simp only [tyLo, encN, Gabbro.Grammatik.encW]
      rfl
  | fl _ =>
      simp only [tyLo, encN, Gabbro.Grammatik.encW]
      rfl
  | fnptr _ =>
      simp only [tyLo, encN, Gabbro.Grammatik.encW]
      rfl
  | ptr _ =>
      simp only [tyLo, encN, Gabbro.Grammatik.encW]
      rfl
  | ref _ =>
      simp only [tyLo, encN, Gabbro.Grammatik.encW]
      exact Grammatik.Speichermodell.Darstellung.dec_enc 0
        ((Gabbro.Grammatik.Val.zelle v : Nat) : Int) ((Gabbro.Grammatik.Val.zelle v : Nat) : Int)
        (by exact_mod_cast Nat.zero_le _) (Int.le_refl _)
  | arr _ _ =>
      simp only [tyLo, encN, Gabbro.Grammatik.encW]
      rfl
  | str _ =>
      simp only [tyLo, encN, Gabbro.Grammatik.encW]
      rfl
  | prod _ _ =>
      simp only [tyLo, encN, Gabbro.Grammatik.encW]
      rfl


end Grammatik.Speichermodell.DarstellungTy
