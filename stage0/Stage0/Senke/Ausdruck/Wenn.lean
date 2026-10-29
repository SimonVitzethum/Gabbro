/-
  File:      stage0/Stage0/Senke/Ausdruck/Wenn.lean
  Subject:   `if c then a else b` as a value (`wennC`): the condition into slot `d`, `brz` to the `else` code, the
             `then` code and a jump over the `else` code. Whichever branch the condition's word selects ends in slot
             `d` (`wenn_ok`).
-/
import Stage0.Senke.Ausdruck.Top

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration} {L : Lay D}

theorem wenn_ok {m : Runner.Mem} {pc fp : Runner.W} {K d : Nat} {cc ca cb : List II} {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {P : Runner.W → Prop} {bc : Bool}
    (hp : Pre L m pc fp K d (wennC d cc ca cb) ρ W) (hlen : 16 * (ca.length + cb.length + 2) < 2 ^ 31) (hd : d < K)
    (hc : ∀ m pc, Pre L m pc fp K d cc ρ W → Ok m pc fp K d cc (fun w => w = if bc then 1 else 0))
    (ha : bc = true → ∀ m pc, Pre L m pc fp K d ca ρ W → Ok m pc fp K d ca P)
    (hb : bc = false → ∀ m pc, Pre L m pc fp K d cb ρ W → Ok m pc fp K d cb P) :
    Ok m pc fp K d (wennC d cc ca cb) P := by
  have hK := hp.small
  have h' : Pre L m pc fp K d (cc ++ ([ci 19 d ((16 * (ca.length + 2) : Nat) : Int) 0] ++ (ca ++
      ([ci 18 ((16 * (cb.length + 1) : Nat) : Int) 0 0] ++ cb)))) ρ W := by
    simpa [wennC, List.append_assoc] using hp
  obtain ⟨m1, s1, a1, w, r, hw⟩ := hc m pc h'.left
  have h1 := h'.next a1 (Nat.le_refl _) (by omega)
  have hi := h1.code 0 (by simp)
  simp only [ci, List.cons_append, List.nil_append, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
  rw [← sx_nat (d := d) (by omega)] at r
  have hlen' : (wennC d cc ca cb).length = cc.length + 1 + ca.length + 1 + cb.length := by
    simp [wennC]; omega
  cases bc with
  | true =>
    simp only [ite_true] at hw
    subst hw
    have sb := Star.one (run_step (t := ⟨_, fp⟩) hi (by decide) (run_brz_ne hi r (by decide)))
    have h2 := h1.next (Agree.refl fp d K m1) (Nat.le_refl _) (by omega)
    obtain ⟨m2, s2, a2, w2, r2, p2⟩ := ha rfl _ _ h2.left
    have h3 := h2.next a2 (Nat.le_refl _) (by omega)
    have hj := h3.code 0 (by simp)
    simp only [ci, List.cons_append, List.nil_append, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hj
    have sj := Star.one (run_step (t := ⟨_, fp⟩) hj (by decide) (run_jmp hj))
    refine ⟨m2, s1.trans (star_cast sb rfl ?_ |>.trans (s2.trans (star_cast sj rfl ?_))), a1.trans a2, w2, r2, p2⟩
    · simp only [nxt, T.mk.injEq, and_true]
      rw [show (16 : Runner.W) = BitVec.ofNat 64 (16 * [ci 19 d ((16 * (ca.length + 2) : Nat) : Int) 0].length) from rfl]
    · simp only [T.mk.injEq, and_true]
      rw [sx_nat (by omega), hlen', pc_add, pc_add, pc_add]
      congr 2 <;> simp <;> omega
  | false =>
    simp only [Bool.false_eq_true, ite_false] at hw
    subst hw
    have sb := Star.one (run_step (t := ⟨_, fp⟩) hi (by decide) (run_brz_zero hi r))
    have h1' : Pre L m1 (pc + BitVec.ofNat 64 (16 * cc.length)) fp K d
        (([ci 19 d ((16 * (ca.length + 2) : Nat) : Int) 0] ++ ca ++ [ci 18 ((16 * (cb.length + 1) : Nat) : Int) 0 0])
          ++ cb) ρ W := by simpa [List.append_assoc] using h1
    have h2 := h1'.next (Agree.refl fp d K m1) (Nat.le_refl _) (by omega)
    obtain ⟨m2, s2, a2, w2, r2, p2⟩ := hb rfl _ _ h2
    refine ⟨m2, s1.trans ((star_cast sb rfl ?_).trans (star_cast s2 rfl ?_)), a1.trans a2, w2, r2, p2⟩
    · simp only [T.mk.injEq, and_true]
      rw [sx_nat (by omega), pc_add, pc_add]
      congr 2 <;> simp <;> omega
    · simp only [T.mk.injEq, and_true]
      rw [hlen', pc_add, pc_add]
      congr 2 <;> simp <;> omega

/-- Conditional lowering with the component code and slot bounds still packaged as options. -/
theorem wennL_ok {fp : Runner.W} {K d top : Nat} {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc : Runner.W} {cc ca cb : Option (List II × Nat)} {c : List II}
    {bc : Bool} {P : Runner.W → Prop}
    (h : wennL d cc ca cb = some (c, top)) (hK : top ≤ K) (hd : d < K)
    (hc : ∀ c t, cc = some (c, t) → t ≤ K → ∀ m pc, Pre L m pc fp K d c ρ W →
      Ok m pc fp K d c (fun w => w = if bc then 1 else 0))
    (ha : bc = true → ∀ c t, ca = some (c, t) → t ≤ K → ∀ m pc, Pre L m pc fp K d c ρ W → Ok m pc fp K d c P)
    (hb : bc = false → ∀ c t, cb = some (c, t) → t ≤ K → ∀ m pc, Pre L m pc fp K d c ρ W → Ok m pc fp K d c P)
    (hp : Pre L m pc fp K d c ρ W) : Ok m pc fp K d c P := by
  simp only [wennL, bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨cc', tc⟩, hcc, ⟨ca', ta⟩, hca, ⟨cb', tb⟩, hcb, h⟩ := h
  split at h
  · next hlen =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact wenn_ok hp hlen hd (hc _ _ hcc (by omega))
      (fun he => ha he _ _ hca (by omega)) (fun he => hb he _ _ hcb (by omega))
  · cases h

end Gabbro.Stage0.Senke
