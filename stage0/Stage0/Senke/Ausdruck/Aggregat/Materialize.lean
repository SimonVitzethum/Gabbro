/- Complete constant values use the same canonical words as copies and the ABI. -/
import Stage0.Senke.Ausdruck.Gleit.Wort
import Stage0.Senke.Ausdruck.Quant.Frame

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}

theorem wordConst_ok {m : Runner.Mem} {pc fp : Runner.W} {K d : Nat}
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop} (w : Runner.W)
    (fits : (wordConst w d).2 ≤ K)
    (pre : Pre L m pc fp K d (wordConst w d).1 ρ W reserved) :
    Ok m pc fp K d (wordConst w d).1 (· = w) := by
  unfold wordConst at fits pre ⊢
  split at fits
  · next small =>
    rw [if_pos small] at pre ⊢
    exact (const_ok pre small (by omega)).mono fun r hr => by
      rw [hr, BitVec.ofInt_toInt]
  · next large =>
    rw [if_neg large] at pre ⊢
    have room : d + 2 ≤ K := by
      simpa [konstWL, bin2, Nat.max_assoc, Nat.max_comm, Nat.max_left_comm] using fits
    exact (konstWL_ok 4 w.toNat (by simpa using w.isLt) room pre).mono fun r hr => by
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using hr

theorem constWords_ok {fp : Runner.W} {K : Nat} {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} (words : List Runner.W) :
    ∀ {m : Runner.Mem} {pc : Runner.W} {d : Nat}, (constWords words d).2 ≤ K →
    Pre L m pc fp K d (constWords words d).1 ρ W reserved →
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (constWords words d).1.length), fp⟩ m' ∧
      Agree fp d K m m' ∧ WordsAt m' fp d words := by
  induction words with
  | nil =>
    intro m pc d fits pre
    exact ⟨m, by simpa [constWords] using Star.refl ⟨pc, fp⟩ m, Agree.refl _ _ _ _,
      by intro i hi; simp at hi⟩
  | cons w ws ih =>
    intro m pc d fits pre
    have headTop := wordConst_top w d
    have hp : Pre L m pc fp K d
        ((wordConst w d).1 ++ (constWords ws (d + 1)).1) ρ W reserved := pre
    obtain ⟨m1, run1, changed1, r, read1, equal⟩ := wordConst_ok w
      (by simp only [constWords] at fits; omega) hp.left
    subst r
    have next := hp.next changed1 (Nat.le_succ d) (by simp only [constWords] at fits; omega)
    obtain ⟨m2, run2, changed2, output⟩ := ih (d := d + 1)
      (by simp only [constWords] at fits; omega) next
    refine ⟨m2, ?_, changed1.trans (changed2.mono (Nat.le_succ d)), ?_⟩
    · simpa only [constWords, List.length_append, pc_add] using run1.trans run2
    · intro i hi
      cases i with
      | zero =>
        rw [Nat.add_zero, agree_rd_low changed2 (pre.frame.agree changed1).room (by omega)
          (by simp only [constWords] at fits; omega)]
        exact read1
      | succ i =>
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using output i (by simp at hi; omega)

theorem materialize_value_ok {m : Runner.Mem} {pc fp : Runner.W} {K d : Nat}
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop} {τ : Ty} (v : Wert D τ)
    (valid : ValueValid L τ v) (fits : (constWords (encodeWords L τ v) d).2 ≤ K)
    (pre : Pre L m pc fp K d (constWords (encodeWords L τ v) d).1 ρ W reserved) :
    ValueOk L m pc fp K d (constWords (encodeWords L τ v) d).1 τ v := by
  obtain ⟨m', run, changed, output⟩ := constWords_ok (encodeWords L τ v) fits pre
  exact ⟨m', run, changed, valid, output⟩

theorem constValue_ok {m : Runner.Mem} {pc fp : Runner.W} {K d top : Nat}
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop} {τ : Ty} {c : List II}
    (v : Wert D τ) (valid : ValueValid L τ v)
    (lower : some (constWords (encodeWords L τ v) d) = some (c, top))
    (fits : top ≤ K) (pre : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c τ v := by
  have pair := Option.some.inj lower
  have codeEq := congrArg Prod.fst pair
  have topEq := congrArg Prod.snd pair
  dsimp only at codeEq topEq
  subst c
  subst top
  exact materialize_value_ok v valid fits pre

/-- A supplied typed root environment is written with the ordinary parameter
    encoding. The frame header, code and any stable world predicate survive.
    Source extraction of that environment is a separate frontend obligation. -/
theorem parameters_ok {m : Runner.Mem} {pc fp : Runner.W} {K : Nat}
    {Γ : Ctx} (ρ : Env D Γ) {W : Runner.Mem → Prop}
    (valid : ∀ τ (x : Var Γ τ), ValueValid L τ (ρ.get x))
    (fits : (constWords (encodeEnv L ρ) (FB + reserved)).2 ≤ K)
    (pre : Pre L m pc fp K (FB + reserved)
      (constWords (encodeEnv L ρ) (FB + reserved)).1 (Env.nil : Env D []) W reserved) :
    Executes m pc fp K (FB + reserved) (constWords (encodeEnv L ρ) (FB + reserved)).1
      (fun m' => EnvAt L m' fp ρ reserved ∧ W m') := by
  obtain ⟨m', run, changed, words⟩ := constWords_ok (encodeEnv L ρ) fits pre
  exact ⟨m', run, changed, (envAt_encoding ρ).mpr ⟨valid, words⟩,
    pre.wstab m m' pre.welt (changed.mono (Nat.zero_le _))⟩

/-- Actual literal lowering, for every declared string capacity and byte list. -/
theorem strLit_ok {n : Nat} {Γ : Ctx} {Λ : List (Res D)}
    {σ₀ σ : World D} {fp : Runner.W} {K d top : Nat} {W : Runner.Mem → Prop}
    {ρ : Env D Γ} {c : List II} {m : Runner.Mem} {pc : Runner.W}
    (bs : List (Zahl 0 255)) (hb : bs.length ≤ n)
    (lower : lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (.strLit bs hb) d = some (c, top))
    (fits : top ≤ K) (pre : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.str n) (eval σ₀ (Expr.strLit (Λ := Λ) bs hb) σ ρ) := by
  exact constValue_ok (L := L) (τ := .str n) ⟨bs, hb⟩ trivial lower fits pre

end Gabbro.Stage0.Senke
