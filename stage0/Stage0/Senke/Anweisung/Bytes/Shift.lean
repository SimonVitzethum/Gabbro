/-
  Subject: State transitions check the old cell before writing the new value.
  A failed prestate check reaches exit_group(106), exactly G's `vorzustand`.
-/
import Stage0.Senke.Anweisung.Simulation
import Stage0.Senke.Anweisung.Schreiben
import Stage0.Senke.Anweisung

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable [Kern] {D : Deklaration}

/-- State-field lowering preserves G's successful write and its failed-prestate stop. -/
theorem shift_ok {L : Lay D} {P : Programm D} {f : D.Fn} {σ0 : World D}
    {ρ0 : Env D (D.params f)} {rp cfp fp pc : Runner.W} {K Ks lo : Nat} {pr : List Nat}
    {A : D.Fn → Nat} {ens : List II × Nat} {ex : Int × Int} {O : Orakel D} {passes : Nat}
    {R : (g : D.Fn) → World D → Env D (D.params g) → RufAusgang g}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {t : D.Tab} {field : D.Feld t} {a b : Int}
    (ht : D.typ t field = .int a b) (i : Expr D Γ Λ (.index (D.count t))) (von nach : Int)
    (hn : a ≤ nach ∧ nach ≤ b) (he : D.erlaubt t field von nach = true)
    (hw : (vertragVon D f).schreibt t = true) (hl : darf D t Λ)
    {c : List II} {top : Nat} {m : Runner.Mem} {σ : World D} {ρ : Env D Γ}
    (h : lowS passes A L lo ens pr ex (Stmt.shift (l := l) t field ht i von nach hn he hw hl) = some (c, top))
    (hK : top ≤ Ks) (hW : WIn L fp Ks K) (hp : PreS L m pc fp K (frei Γ) c ρ)
    (hlo : lo ≤ frei Γ) (hWa : WeltAt m L σ) (hpr : ∀ j ∈ pr, j < frei Γ) :
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length))
      (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2)
      (execStmt O passes R (Stmt.shift (l := l) t field ht i von nach hn he hw hl) σ ρ) := by
  simp only [lowS] at h
  split at h
  · next hfit =>
    simp only [Bool.and_eq_true] at hfit
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ci', ti⟩, hi, ⟨cr, tr⟩, hr, ⟨cj, tj⟩, hj, ⟨ca, ta⟩, ha, h⟩ := h
    simp only [bin2, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hks := hW.ks
    have htop := slotA_top ha
    have htopr : frei Γ + 2 ≤ tr := by
      simp only [slotC, ht, aggregateFits, ↓reduceIte, Option.map_eq_some_iff] at hr
      obtain ⟨⟨cc, tc⟩, hc, hh⟩ := hr
      have := slotA_top hc
      simp only [Option.some.injEq, Prod.mk.injEq] at hh
      omega
    let σE := σ.lese Λ (.inl t :: i.orte)
    have hWE : WeltAt m L σE := hWa
    let old : Wert D (.int a b) := ht ▸ σE.slots t (eval σE i σE ρ).n field
    have heq : Enc L (D.typ t field) (σE.slots t (eval σE i σE ρ).n field) =
        (fun w => w = BitVec.ofInt 64 old.n) := by funext w; exact propext (enc_int_cast ht _ w)
    let test := cr ++ [ci 1 (frei Γ + 1) von 0] ++ [ci 14 (frei Γ) (frei Γ) (frei Γ + 1)]
    let tail := [ci 1 (frei Γ) nach 0] ++ ca ++ [stC (frei Γ)]
    have hp' : PreS L m pc fp K (frei Γ) (test ++ (guardC (frei Γ) 106 (frei Γ) ++ tail)) ρ := hp
    have hpw := PreS.welt hp'.left hks hWE hW.lay (by have := hW.lo; omega)
    have hread : ∀ m pc, Pre L m pc fp Ks (frei Γ) cr ρ (fun m => WeltAt m L σE) →
        Ok m pc fp Ks (frei Γ) cr (fun w => w = BitVec.ofInt 64 old.n) := by
      intro m pc hp
      rw [← heq]
      exact slotC_ok hr (by omega)
        (fun m pc hp => lowE_ok σE σE (fun _ h => h) i _ ci' ti hi
          (by have := slotC_top hr; simp only at this; omega) m pc ρ hp) (fun _ h => h) hp
    have htest : Ok m pc fp Ks (frei Γ) test (fun w => w = Runner.IR.bool (decide (old.n = von))) := by
      refine bin_ok hread (fun m pc hp => const_ok hp hfit.1.2 (by omega))
        (g := fun x y => some (Runner.IR.bool (x == y))) ?_ rfl (by decide) (by omega) hpw
      intro wa wb pa pb
      refine ⟨_, rfl, ?_⟩
      rw [pa, pb, beq_in (inW_spec hfit.1.1 old.lo_le old.le_hi)
        (by simp only [lit32, Bool.and_eq_true, decide_eq_true_eq] at hfit; omega)]
    obtain ⟨m1, s1, a1s, w, hw1, rfl⟩ := htest
    have a1 := Agree.widen a1s hks
    have hp1 := hp'.next a1 (Nat.le_refl _) (by omega)
    have hWE1 := hpw.wstab m m1 hWE (a1s.mono (Nat.zero_le _))
    simp only [execStmt]
    change Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m _ _ _
      (if old.n = von then Ausgang.ok _ ρ else .logik .vorzustand)
    by_cases hv : old.n = von
    · rw [if_pos hv]
      have sg := guard_pass hp1.left.code (by have := hp.small; omega) hw1 (by simp [hv, Runner.IR.bool])
      have hp2 := hp1.next (a := guardC (frei Γ) 106 (frei Γ)) (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)
      have hn0 := (eval σE i σE ρ).lo_le
      have hkc : ((eval σE i σE ρ).n.toNat : Int) < D.count t := by have := (eval σE i σE ρ).le_hi; omega
      have hkn : ((eval σE i σE ρ).n.toNat : Int) = (eval σE i σE ρ).n := Int.toNat_of_nonneg hn0
      obtain ⟨m2, s2, a2, en, hw2⟩ := store_ok (σ := σE) hp2 hW hWE1 (by omega)
        (fun m pc hp => (const_ok hp hfit.2 (by omega)).mono (fun w hw => (enc_int_back ht ⟨nach, hn.1, hn.2⟩ w).mpr hw))
        (fun m pc hp => slotA_ok ha (by omega)
          (fun m pc hp => lowE_ok σE σE (fun _ h => h) i _ cj tj hj (by have := slotA_top ha; omega) m pc ρ hp) hp)
        (hW.lay.1 t field _ (L.bounded hkc)) (fun m w hm hw => by
          have hnw : Enc L (D.typ t field) ((ht ▸ (⟨nach, hn.1, hn.2⟩ : Zahl a b) : Wert D (D.typ t field))) w := hw
          have hh := weltAt_slot hm hW.lay hW.dis (L.bounded hkc) hnw
          rw [hkn] at hh
          exact hh)
      have aa : AgreeW L fp (frei Γ) K m m2 := (agreeW_of a1).trans a2
      refine ⟨m2, s1.trans (sg.trans ?_), aa.mono hlo, en, hw2, keeps_of_agreeW hW aa hpr (by omega)⟩
      simpa only [test, List.length_append, pc_add, Nat.add_assoc] using s2
    · rw [if_neg hv]
      change Stops ⟨pc, fp⟩ m 106
      exact Stops.prefix s1 (guard_stop hp1.left.code (by simpa [guardC, stopC, sysC] using hp1.left.far)
        hp1.frame (by omega) (by omega) hp.small (by decide) (by simpa [hv, Runner.IR.bool] using hw1))
  · cases h

end Gabbro.Stage0.Senke
