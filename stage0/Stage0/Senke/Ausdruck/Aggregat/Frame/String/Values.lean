/- Packed and span string operations meet in the actual expression theorem. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Frame.String.CatOk
public import Stage0.Senke.Ausdruck.Aggregat.Frame.String.OrderScan
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat} {currentOld : Bool}
variable {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ} {W : Runner.Mem → Prop}
variable {σ₀ σ : World D} {fp : Runner.W} {K d top : Nat} {c : List II} {m : Runner.Mem} {pc : Runner.W}

theorem strLtSpan_ok {n q : Nat} (vs : Wert D (.str n)) (vt : Wert D (.str q))
    (s t : Option (List II × Nat))
    (ihs : ∀ ca ta, s = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K (d + 1) ca ρ W reserved → ValueOk L m pc fp K (d + 1) ca (.str n) vs)
    (iht : ∀ ca ta, t = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K (d + 1 + (stringCapacity n + 1)) ca ρ W reserved →
      ValueOk L m pc fp K (d + 1 + (stringCapacity n + 1)) ca (.str q) vt)
    (made : strLtSpanL n q d s t = some (c, top)) (fits : top ≤ K)
    (pre : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c .bool (strLtW vs vt) := by
  unfold strLtSpanL at made
  split at made
  · next bounds =>
    let a := d + 1
    let b := a + (stringCapacity n + 1)
    let acc := b + (stringCapacity q + 1)
    let count := max (stringCapacity n) (stringCapacity q)
    let scan := stringScanC count (stringCapacity n) (stringCapacity q) a b acc
    let tail := [ci 1 acc 0 0] ++ (scan ++ [ci 2 d acc 0])
    refine stringPair_ok (a := a) (b := b) (need := acc + 5) (tail := tail)
      vs vt (fun m' => ValueAt L m' fp d .bool (strLtW vs vt))
      (by omega : d ≤ a) rfl (by omega : b + (stringCapacity q + 1) ≤ acc + 5)
      ihs iht (by simpa only [a, b, acc, count, scan, tail, ci, List.append_assoc] using made) fits pre ?_
    intro m pc hp need spanA spanB
    have ha : a + stringCapacity n + 1 ≤ acc := by dsimp [acc, b]; omega
    have hb : b + stringCapacity q + 1 ≤ acc := by dsimp [acc]; omega
    have scanA := stringScan_admitted bounds.1 bounds.2 ha hb need
    have admitted : ∀ i ∈ tail, AluIns K d i := by
      intro i hi
      simp only [tail, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl | (hi | rfl)
      · exact AluIns.const _ _ (by dsimp [acc, b, a]; omega) (by omega) (by decide)
      · exact (scanA count i hi).lower (by dsimp [acc, b, a]; omega)
      · exact AluIns.mov _ _ (Nat.le_refl _) (by dsimp [acc, b, a] at need; omega) (by omega)
    let vals := slotVal m fp
    have sa : StringSlots vals a (stringCapacity n) vs.1 :=
      stringSlots_of_span (stringCapacity_ge n) hp.frame (by omega) (stringSpanValue vs) spanA
    have sb : StringSlots vals b (stringCapacity q) vt.1 :=
      stringSlots_of_span (stringCapacity_ge q) hp.frame (by omega) (stringSpanValue vt) spanB
    let init := [ci 1 acc 0 0]
    have ai : ∀ i ∈ init, AluIns K acc i := by
      intro i hi
      simp only [init, List.mem_cons, List.mem_nil_iff, or_false] at hi
      subst i
      exact AluIns.const _ _ (Nat.le_refl _) (by omega) (by decide)
    let vals0 := aluRun init vals
    have sa0 := StringSlots.low ai ha vals vs.1 sa
    have sb0 := StringSlots.low ai hb vals vt.1 sb
    have zero : vals0 acc = Runner.IR.bool false := by
      simp [vals0, init, aluRun, aluStep, aluVal, ci, slotUpd, Runner.IR.bool]
    have result := stringScan_value bounds.1 bounds.2 ha hb need vs.1 vt.1
      (Nat.le_trans vs.2 (stringCapacity_bound n)) (Nat.le_trans vt.2 (stringCapacity_bound q))
      count vals0 false sa0 sb0 zero
    have meaning := keyScan_bytes count vs.1 vt.1
      (Nat.le_trans vs.2 (Nat.le_trans (stringCapacity_bound n) (Nat.le_max_left _ _)))
      (Nat.le_trans vt.2 (Nat.le_trans (stringCapacity_bound q) (Nat.le_max_right _ _)))
    have move (state : Nat → Runner.W) : aluRun [ci 2 d acc 0] state d = state acc := by
      simp only [aluRun_cons, aluRun_nil, aluStep, aluVal, ci, Int.toNat_natCast,
        slotUpd_same, Nat.reduceEqDiff, ite_false, ite_true]
    have value : aluRun tail vals d = Runner.IR.bool (strLtW vs vt) := by
      calc
        aluRun tail vals d = aluRun [ci 2 d acc 0] (aluRun scan vals0) d := by
          simp only [tail, init, vals0, aluRun_append]
        _ = aluRun scan vals0 acc := move _
        _ = Runner.IR.bool (strLtW vs vt) := result.trans (congrArg Runner.IR.bool meaning)
    obtain ⟨m', run, changed, reads⟩ := alu_run hp.frame hp.small hp.code hp.far admitted vals
      (fun j hj => slotVal_rd hp.frame hj)
    have encoded : Enc L .bool (strLtW vs vt) (Runner.IR.bool (strLtW vs vt)) := by
      simpa only [Enc, wahr?] using (bool_word (strLtW vs vt))
    refine ⟨m', run, changed, ValueAt.of_enc
      (w := Runner.IR.bool (strLtW vs vt)) rfl ?_ encoded⟩
    rw [reads d (by dsimp [acc, b, a] at need; omega), value]
  · cases made


theorem strCatExpr_ok {n q : Nat} (s : Expr D Γ Λ (.str n)) (t : Expr D Γ Λ (.str q))
    (ihs : ∀ ca ta, lowE (currentOld := currentOld) L (reserved := reserved) s d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → ValueOk L m pc fp K d ca (.str n) (eval σ₀ s σ ρ))
    (iht : ∀ ca ta, lowE (currentOld := currentOld) L (reserved := reserved) t d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → ValueOk L m pc fp K d ca (.str q) (eval σ₀ t σ ρ))
    (ihsa : ∀ ca ta, lowE (currentOld := currentOld) L (reserved := reserved) s (d + (n + q + 1)) = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K (d + (n + q + 1)) ca ρ W reserved →
        ValueOk L m pc fp K (d + (n + q + 1)) ca (.str n) (eval σ₀ s σ ρ))
    (ihtb : ∀ ca ta, lowE (currentOld := currentOld) L (reserved := reserved) t
        (d + (n + q + 1) + (stringCapacity n + 1)) = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K (d + (n + q + 1) + (stringCapacity n + 1)) ca ρ W reserved →
        ValueOk L m pc fp K (d + (n + q + 1) + (stringCapacity n + 1)) ca (.str q) (eval σ₀ t σ ρ))
    (h : lowE (currentOld := currentOld) L (reserved := reserved) (.strCat s t) d = some (c, top))
    (fits : top ≤ K) (pre : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.str (n + q)) (eval σ₀ (.strCat s t) σ ρ) := by
  rw [lowE_strCat] at h
  split at h
  · next short =>
    exact strCat_ok s t ihs iht (by simpa only [lowE_strCat, ite_eq_left short] using h) fits pre
  · unfold strCatSpanL at h
    split at h
    · next bounds =>
      let a := d + (n + q + 1)
      let b := a + (stringCapacity n + 1)
      let ptr := b + (stringCapacity q + 1)
      let need := max (ptr + 2) (constWords (List.replicate q 0) (d + 1 + n)).2
      let tail := stringCatC n q d a b ptr
      refine stringPair_ok (a := a) (b := b) (need := need) (tail := tail)
        (eval σ₀ s σ ρ) (eval σ₀ t σ ρ)
        (fun m' => ValueAt L m' fp d (.str (n + q)) (eval σ₀ (.strCat s t) σ ρ))
        (by omega : d ≤ a) rfl (by dsimp [need, ptr]; omega) ihsa ihtb
        (by simpa only [a, b, ptr, need, tail, List.append_assoc] using h) fits pre ?_
      intro m pc hp needFits spanA spanB
      exact stringCatC_ok (a := a) (b := b) (ptr := ptr) (need := need)
        (eval σ₀ s σ ρ) (eval σ₀ t σ ρ) bounds.1 rfl rfl rfl
        (Nat.le_refl need) needFits spanA spanB hp
    · cases h

theorem strLtExpr_ok {n q : Nat} (s : Expr D Γ Λ (.str n)) (t : Expr D Γ Λ (.str q))
    (ihs : ∀ ca ta, lowE (currentOld := currentOld) L (reserved := reserved) s d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → ValueOk L m pc fp K d ca (.str n) (eval σ₀ s σ ρ))
    (iht : ∀ ca ta, lowE (currentOld := currentOld) L (reserved := reserved) t (d + 1) = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K (d + 1) ca ρ W reserved → ValueOk L m pc fp K (d + 1) ca (.str q) (eval σ₀ t σ ρ))
    (ihsa : ∀ ca ta, lowE (currentOld := currentOld) L (reserved := reserved) s (d + 1) = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K (d + 1) ca ρ W reserved → ValueOk L m pc fp K (d + 1) ca (.str n) (eval σ₀ s σ ρ))
    (ihtb : ∀ ca ta, lowE (currentOld := currentOld) L (reserved := reserved) t
        (d + 1 + (stringCapacity n + 1)) = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K (d + 1 + (stringCapacity n + 1)) ca ρ W reserved →
        ValueOk L m pc fp K (d + 1 + (stringCapacity n + 1)) ca (.str q) (eval σ₀ t σ ρ))
    (h : lowE (currentOld := currentOld) L (reserved := reserved) (.strLt s t) d = some (c, top))
    (fits : top ≤ K) (pre : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c .bool (eval σ₀ (.strLt s t) σ ρ) := by
  rw [lowE_strLt] at h
  split at h
  · next short => exact strCompare_ok true s t ihs iht (by rw [if_pos short]; exact h) fits pre
  · exact strLtSpan_ok (eval σ₀ s σ ρ) (eval σ₀ t σ ρ) _ _ ihsa ihtb h fits pre

end Gabbro.Stage0.Senke
