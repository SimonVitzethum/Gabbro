/- Bounded optional-index chains against G's kette. -/
import Stage0.Senke.Ausdruck.Wenn
import Stage0.Senke.Ausdruck.Lesen

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable [Kern] {D : Deklaration}

theorem reachEqL_ok {fp : Runner.W} {K d top : Nat} {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc : Runner.W} {a b : Option (List II × Nat)} {c : List II} {x y : Int}
    (hx : -2 ^ 63 ≤ x ∧ x < 2 ^ 63) (hy : -2 ^ 63 ≤ y ∧ y < 2 ^ 63)
    (h : reachEqL d a b = some (c, top)) (hK : top ≤ K)
    (ha : ∀ c t, a = some (c, t) → t ≤ K → ∀ m pc, Pre m pc fp K d c ρ W →
      Ok m pc fp K d c (fun w => w = BitVec.ofInt 64 x))
    (hb : ∀ c t, b = some (c, t) → t ≤ K → ∀ m pc, Pre m pc fp K (d + 1) c ρ W →
      Ok m pc fp K (d + 1) c (fun w => w = BitVec.ofInt 64 y))
    (hp : Pre m pc fp K d c ρ W) :
    Ok m pc fp K d c (fun w => w = if decide (x = y) then 1 else 0) := by
  simp only [reachEqL, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨⟨ca, ta⟩, hca, ⟨cb, tb⟩, hcb, h⟩ := h
  simp only [Prod.mk.injEq, bin2] at h
  obtain ⟨rfl, rfl⟩ := h
  refine bin_ok (ha _ _ hca (by omega)) (hb _ _ hcb (by omega))
    (g := fun x y => some (Runner.IR.bool (x == y))) ?_ rfl (by decide) (by omega) hp
  intro a b pa pb
  exact ⟨_, rfl, by rw [pa, pb, bool_word, beq_in hx hy]⟩

theorem reachL_ok {L : Lay D} {t : D.Tab} {f : D.Feld t} (hf : D.typ t f = .opt (D.count t))
    {σ : World D} {fp : Runner.W} {K d : Nat} {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    (hWL : ∀ m, W m → WeltAt m L σ) (hn : (D.count t).toNat < 2 ^ 31)
    (goal : Zahl 0 (D.count t - 1)) :
    ∀ fuel (a b : Option (List II × Nat)) (k : Zahl 0 (D.count t - 1)) c top,
    reachL L t f d fuel a b = some (c, top) → top ≤ K →
    (∀ c t', a = some (c, t') → t' ≤ K → ∀ m pc, Pre m pc fp K d c ρ W →
      Ok m pc fp K d c (fun w => w = BitVec.ofInt 64 k.n)) →
    (∀ c t', b = some (c, t') → t' ≤ K → ∀ m pc, Pre m pc fp K (d + 1) c ρ W →
      Ok m pc fp K (d + 1) c (fun w => w = BitVec.ofInt 64 goal.n)) →
    ∀ m pc, Pre m pc fp K d c ρ W → Ok m pc fp K d c
      (fun w => w = if kette (fun i => hf ▸ σ.slots t i f) fuel k.n goal.n then 1 else 0)
  | 0, a, b, k, c, top, h, hK, ha, hb, m, pc, hp => by
    have hk0 := k.lo_le; have hk1 := k.le_hi
    have hg0 := goal.lo_le; have hg1 := goal.le_hi
    exact reachEqL_ok (by omega) (by omega) h hK ha hb hp
  | fuel + 1, a, b, k, c, top, h, hK, ha, hb, m, pc, hp => by
    have hk0 := k.lo_le; have hk1 := k.le_hi
    have hg0 := goal.lo_le; have hg1 := goal.le_hi
    let next := a.bind (slotC L t f d)
    have hnxt : ∀ c top, next = some (c, top) → top ≤ K → ∀ m pc,
        Pre m pc fp K d c ρ W → Ok m pc fp K d c (Enc (.opt (D.count t)) (hf ▸ σ.slots t k.n f)) := by
      intro c top h ht m pc hp
      simp only [next, Option.bind_eq_some_iff] at h
      obtain ⟨⟨ca, ta⟩, he, hs⟩ := h
      have haTop := slotC_top hs
      have hh := slotC_value_ok (k := k) hs ht (ha ca ta he (by omega)) hWL hp
      exact hh.mono fun w hw => (enc_transport hf _ w).mp hw
    have hdk := reachL_top (fuel + 1) a b h
    refine wennL_ok h hK (by omega) (fun c top h ht m pc hp => reachEqL_ok (by omega) (by omega) h ht ha hb hp)
      (fun he c top hh ht m pc hp => ?_) (fun he c top hh ht m pc hp => ?_) hp
    · have heq : k.n = goal.n := of_decide_eq_true he
      simp only [Option.some.injEq, Prod.mk.injEq] at hh
      obtain ⟨rfl, rfl⟩ := hh
      exact (const_ok hp (by decide) (by omega)).mono fun w hw => by simp [kette, heq, hw]
    · have hne : k.n ≠ goal.n := by simpa using he
      cases heq : (hf ▸ σ.slots t k.n f : Wert D (.opt (D.count t))) with
      | none =>
        refine wennL_ok (bc := true) hh ht (by omega) ?_ ?_ ?_ hp
        · intro c top hh ht m pc hp
          exact reachEqL_ok (x := -1) (y := -1) (by omega) (by omega) hh ht
            (fun c top h ht m pc hp => (hnxt c top h ht m pc hp).mono fun w hw => by simpa [heq, Enc, optN] using hw)
            (fun c top hh ht m pc hp => by cases hh; exact const_ok hp (by decide) (by omega)) hp
        · intro _ c top hh ht m pc hp
          cases hh
          exact (const_ok hp (by decide) (by omega)).mono fun w hw => by simp [kette, hne, heq, hw]
        · intro hh; cases hh
      | some q =>
        have hq0 := q.lo_le; have hq1 := q.le_hi
        have htest : decide (q.n = -1) = false := by simp; omega
        refine wennL_ok (bc := false) hh ht (by omega) ?_ ?_ ?_ hp
        · intro c top hh ht m pc hp
          have hh' := reachEqL_ok (x := q.n) (y := -1) (by omega) (by omega) hh ht
            (fun c top h ht m pc hp => (hnxt c top h ht m pc hp).mono fun w hw => by simpa [heq, Enc, optN] using hw)
            (fun c top hh ht m pc hp => by cases hh; exact const_ok hp (by decide) (by omega)) hp
          simpa only [htest] using hh'
        · intro hh; cases hh
        · intro _ c top hh ht m pc hp
          have hr := reachL_ok hf hWL hn goal fuel next b q c top hh ht
            (fun c top h ht m pc hp => (hnxt c top h ht m pc hp).mono fun w hw => by simpa [heq, Enc, optN] using hw) hb m pc hp
          simpa only [kette, if_neg hne, heq] using hr

/-- The preflight checks and the bounded-chain proof for a complete reachability expression. -/
theorem reachesL_ok {L : Lay D} {t : D.Tab} {f : D.Feld t} (hf : D.typ t f = .opt (D.count t))
    {σ : World D} {fp : Runner.W} {K d top : Nat} {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc : Runner.W} {a b : Option (List II × Nat)} {c : List II}
    (hWL : ∀ m, W m → WeltAt m L σ) (k goal : Zahl 0 (D.count t - 1))
    (h : reachesL L t f d a b = some (c, top)) (hK : top ≤ K)
    (ha : ∀ c t', a = some (c, t') → t' ≤ K → ∀ m pc, Pre m pc fp K d c ρ W →
      Ok m pc fp K d c (fun w => w = BitVec.ofInt 64 k.n))
    (hb : ∀ c t', b = some (c, t') → t' ≤ K → ∀ m pc, Pre m pc fp K (d + 1) c ρ W →
      Ok m pc fp K (d + 1) c (fun w => w = BitVec.ofInt 64 goal.n))
    (hp : Pre m pc fp K d c ρ W) : Ok m pc fp K d c
      (fun w => w = if kette (fun i => hf ▸ σ.slots t i f) (D.count t).toNat k.n goal.n then 1 else 0) := by
  simp only [reachesL, bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨ca, ta⟩, hca, ⟨cb, tb⟩, hcb, h⟩ := h
  split at h
  · next hn =>
    exact reachL_ok hf hWL hn.1 goal _ _ _ k c top h hK
      (fun c t he ht => ha c t (hca.trans he) ht) (fun c t he ht => hb c t (hcb.trans he) ht) m pc hp
  · cases h

end Gabbro.Stage0.Senke
