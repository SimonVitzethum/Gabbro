/- Generic long-string order, connected to normalized operand evaluation. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Frame.String.Span
public import Stage0.Senke.Ausdruck.Aggregat.Frame.String.OrderScan
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}
variable {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
variable {fp : Runner.W} {K d top : Nat} {c : List II} {m : Runner.Mem} {pc : Runner.W}

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
    let tail := [ci 1 acc 0 0] ++ scan ++ [ci 2 d acc 0]
    refine stringPair_ok vs vt (fun m' => ValueAt L m' fp d .bool (strLtW vs vt))
      (by omega : d ≤ a) rfl (by omega : b + (stringCapacity q + 1) ≤ acc + 5)
      ihs iht made fits pre ?_
    intro m pc hp need spanA spanB
    have ha : a + stringCapacity n + 1 ≤ acc := by dsimp [acc, b]; omega
    have hb : b + stringCapacity q + 1 ≤ acc := by dsimp [acc]; omega
    have scanA := stringScan_admitted bounds.1 bounds.2 ha hb need
    have admitted : ∀ i ∈ tail, AluIns K d i := by
      intro i hi
      simp only [tail, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with (rfl | hi) | rfl
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
    have value : aluRun tail vals d = Runner.IR.bool (strLtW vs vt) := by
      simp only [tail, aluRun_append]
      simp only [aluRun_cons, aluRun_nil, aluStep, aluVal, ci, Int.toNat_natCast, slotUpd_same,
        Nat.reduceEqDiff, ite_false, ite_true]
      rw [result, meaning]
      rfl
    obtain ⟨m', run, changed, reads⟩ := alu_run hp.frame hp.small hp.code hp.far admitted vals
      (fun j hj => slotVal_rd hp.frame hj)
    refine ⟨m', run, changed, ValueAt.of_enc rfl ?_ (bool_word _)⟩
    rw [reads d (by dsimp [acc, b, a] at need; omega), value]
  · cases made

end Gabbro.Stage0.Senke
