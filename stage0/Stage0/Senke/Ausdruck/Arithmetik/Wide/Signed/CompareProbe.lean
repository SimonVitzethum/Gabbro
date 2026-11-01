/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Signed/CompareProbe.lean
  Subject:   Actual-memory mixed comparisons across limbs, both signedness orders and all three modes.

  The alias fixture gives both operands IDENTICAL two-limb encodings: signed -(2^100)-1 and
  unsigned 2^128-2^100-1. Equality must be false despite identical bits; order needs the extra limb.
  The equality fixture compares 2^100+1 in both domains, checking true eq and inclusive le.
-/
module
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.Signed.CompareRun
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.Probe
@[expose] public section


namespace Gabbro.Stage0.Senke.MixedWideProbe
open Runner.IR Runner.Mem Gabbro.Stage0.Senke.WideProbe

theorem probe_frame32 (code : List II) (words : List Nat) : FrameOK (probeMem code words) 4096 32 :=
  ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩

def aliasX (signed : Bool) : Int := if signed then -(2 ^ 100) - 1 else 2 ^ 128 - 2 ^ 100 - 1

def aliasMem (signed : Bool) (mode : WideCompare) : Runner.Mem :=
  probeMem (wideMixedC signed mode 2 8)
    [18446744073709551615, 18446744004990074879, 18446744073709551615, 18446744004990074879]

theorem aliasMem_x (signed : Bool) (mode : WideCompare) :
    WordsAt (aliasMem signed mode) 4096 8 (integerEncoding 2 (aliasX signed)) := by
  intro i hi
  have : i < 2 := hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;>
    (clear this; revert hi; cases signed <;> cases mode <;> decide +kernel)

theorem aliasMem_y (signed : Bool) (mode : WideCompare) :
    WordsAt (aliasMem signed mode) 4096 10 (integerEncoding 2 (aliasX (!signed))) := by
  intro i hi
  have : i < 2 := hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;>
    (clear this; revert hi; cases signed <;> cases mode <;> decide +kernel)

def aliasResult (signed : Bool) : WideCompare → Runner.W
  | .eq => 0
  | .lt | .le => Runner.IR.bool signed

/-- Every comparison and both operand orders distinguish identical bits with different signed meanings. -/
theorem wideMixed_alias_zeuge [Kern] (signed : Bool) (mode : WideCompare) :
    ∃ m', Star ⟨2048, 4096⟩ (aliasMem signed mode)
        ⟨2048 + BitVec.ofNat 64 (16 * (wideMixedC signed mode 2 8).length), 4096⟩ m' ∧
      Agree 4096 8 32 (aliasMem signed mode) m' ∧
      m'.rd64 (slot 4096 (BitVec.ofNat 64 8)) = some (aliasResult signed mode) := by
  have far : CodeFar 2048 (wideMixedC signed mode 2 8).length 4096 32 := by
    cases signed <;> cases mode <;> unfold CodeFar <;> decide +kernel
  obtain ⟨m', run, agree, res⟩ := wideMixed_run (m := aliasMem signed mode) (pc := 2048) (fp := 4096)
    (K := 32) (k := 2) (a := 8) signed mode (aliasX signed) (aliasX (!signed)) (by decide)
    (by cases signed <;> norm_num [WideFits, aliasX])
    (by cases signed <;> norm_num [WideFits, aliasX]) (probe_frame32 _ _) (by decide) (by decide)
    (probe_code (wideMixedC signed mode 2 8) _ (by cases signed <;> cases mode <;> decide +kernel)
      (by cases signed <;> cases mode <;> decide +kernel)) far (aliasMem_x signed mode) (aliasMem_y signed mode)
  refine ⟨m', run, agree, ?_⟩
  rw [res]
  congr 1
  cases signed <;> cases mode <;> decide +kernel

def equalMem (signed : Bool) (mode : WideCompare) : Runner.Mem :=
  probeMem (wideMixedC signed mode 2 8) [1, 68719476736, 1, 68719476736]

def equalResult : WideCompare → Runner.W
  | .lt => 0
  | .le | .eq => 1

/-- The common positive domain includes values crossing a limb boundary; le includes equality. -/
theorem wideMixed_equal_zeuge [Kern] (signed : Bool) (mode : WideCompare) :
    ∃ m', Star ⟨2048, 4096⟩ (equalMem signed mode)
        ⟨2048 + BitVec.ofNat 64 (16 * (wideMixedC signed mode 2 8).length), 4096⟩ m' ∧
      Agree 4096 8 32 (equalMem signed mode) m' ∧
      m'.rd64 (slot 4096 (BitVec.ofNat 64 8)) = some (equalResult mode) := by
  have input : ∀ base, base = 8 ∨ base = 10 →
      WordsAt (equalMem signed mode) 4096 base (integerEncoding 2 (2 ^ 100 + 1)) := by
    intro base hb i hi
    have : i < 2 := hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;>
      (clear this; revert hi; rcases hb with rfl | rfl <;> cases signed <;> cases mode <;> decide +kernel)
  have far : CodeFar 2048 (wideMixedC signed mode 2 8).length 4096 32 := by
    cases signed <;> cases mode <;> unfold CodeFar <;> decide +kernel
  obtain ⟨m', run, agree, res⟩ := wideMixed_run (m := equalMem signed mode) (pc := 2048) (fp := 4096)
    (K := 32) (k := 2) (a := 8) signed mode (2 ^ 100 + 1) (2 ^ 100 + 1) (by decide)
    (by cases signed <;> norm_num [WideFits]) (by cases signed <;> norm_num [WideFits])
    (probe_frame32 _ _) (by decide) (by decide)
    (probe_code (wideMixedC signed mode 2 8) _ (by cases signed <;> cases mode <;> decide +kernel)
      (by cases signed <;> cases mode <;> decide +kernel)) far (input 8 (Or.inl rfl)) (input 10 (Or.inr rfl))
  refine ⟨m', run, agree, ?_⟩
  rw [res]
  congr 1
  cases mode <;> decide +kernel

end Gabbro.Stage0.Senke.MixedWideProbe
