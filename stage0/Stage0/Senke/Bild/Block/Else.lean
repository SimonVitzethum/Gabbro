/- Both return channels of a fallible block binder, up to the selected arm. -/
module
public import Stage0.Senke.Bild.Block.Bind
public import Stage0.Senke.Anweisung.Faelle.CallElse
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik Gabbro.Stage0.Senke Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable {D : Deklaration} [Kern]

/-- The image copies the shared return area, then dispatches on the separate status
    word. Normal status binds the result in the success block; reason status binds
    the reason in the end block. The success arm's loop exits skip the error suffix.
    Logic and hardware failures stop exactly as the underlying call does. -/
theorem BodyFrame.randBIR_bindCallElse {B : BodyFrame D} (hB : B.Ok) {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {τ : Ty} {g : D.Fn} {args : Args D Γ Λ (D.params g)}
    {he : D.erg g = some τ} {hp : RufPasst D (vertragVon D B.f) (D.signatur g) Λ}
    {hr : 0 < D.gruende g}
    {err : Endblock D (vertragVon D B.f) l (.why (D.gruende g) :: Γ) (nach D g Λ)}
    {rest : Block D (vertragVon D B.f) l (τ :: Γ) (nach D g Λ) Λ'}
    {pc : Runner.W} {m : Runner.Mem} {σ : World D} {ρ : Env D Γ}
    (h : B.RandBIR (.bindCallElse g args he hp hr err rest) pc m σ ρ) :
    (∃ (σ2 : World D) (v : ErgVal D (D.erg g)) (pc2 : Runner.W) (m2 : Runner.Mem) (n : Nat),
      B.R g (σ.lese Λ args.orte) (rufEnv g σ Λ args ρ) = .ok σ2 v ∧
      Star ⟨pc, B.fp⟩ m ⟨pc2, B.fp⟩ m2 ∧ AgreeW B.L B.fp B.lo B.K m m2 ∧
      (B.suffix n).RandBIR rest pc2 m2 σ2 (.cons (ergWert he v) ρ)) ∨
    (∃ (σ2 : World D) (r : Fin (D.gruende g)) (pc2 : Runner.W) (m2 : Runner.Mem),
      B.R g (σ.lese Λ args.orte) (rufEnv g σ Λ args ρ) = .why σ2 r ∧
      Star ⟨pc, B.fp⟩ m ⟨pc2, B.fp⟩ m2 ∧ AgreeW B.L B.fp B.lo B.K m m2 ∧
      B.RandIR err pc2 m2 σ2 (.cons r ρ)) ∨
    (∃ e, B.R g (σ.lese Λ args.orte) (rufEnv g σ Λ args ρ) = .logik e ∧
      Stops ⟨pc, B.fp⟩ m (logikCode e)) ∨
    (∃ e, B.R g (σ.lese Λ args.orte) (rufEnv g σ Λ args ρ) = .hardware e ∧
      Stops ⟨pc, B.fp⟩ m (hwCode e)) := by
  obtain ⟨c, top, hl, ht, hs, pre, hlo, hu, hk, hw, hpr, hH⟩ := h
  simp only [lowB, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hl
  obtain ⟨⟨ca, ta⟩, hca, ⟨ce, te⟩, hce, ⟨cr, tr⟩, hcr, hc⟩ := hl
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  simp only [elseTop] at ht
  have hW := hB.win
  have hsR : 16 * cr.length < 2 ^ 31 := by
    simp only [elseC, List.length_append, List.length_singleton] at hs
    omega
  have hsE : 16 * ce.length < 2 ^ 31 := by
    simp only [elseC, List.length_append, List.length_singleton] at hs
    omega
  rcases callElse_ok hB.spec (hB.addr g) args he (σ.lese Λ args.orte) hca (by omega) pre hs hu hW hw
      (HeldIn.ruf (V := vertragVon D B.f) hH hp) with
    ⟨σ2, v, m2, hR, st, a, pre2, hw2⟩ | ⟨σ2, r, m2, hR, st, a, pre2, hw2⟩ |
    ⟨e, hR, st⟩ | ⟨e, hR, st⟩
  · refine Or.inl ⟨σ2, v, _, m2, ce.length + 1, hR, st, a.mono hlo,
      cr, tr, hcr, by omega, hsR, pre2, ?_, hu.agreeW hW a (by simp only [frei]; omega),
      hk.agreeW hW a (by rw [← hB.lo0]; exact hlo), hw2, ?_, hH.sig⟩
    · simp only [BodyFrame.suffix, frei_cons]
      omega
    · intro i hi
      have := hpr i hi
      simp only [BodyFrame.suffix, frei_cons]
      omega
  · refine Or.inr (Or.inl ⟨σ2, r, _, m2, hR, st, a.mono hlo,
      ce, te, hce, by omega, hsE, pre2, ?_, hu.agreeW hW a (by simp only [frei]; omega),
      hk.agreeW hW a (by rw [← hB.lo0]; exact hlo), hw2, ?_, hH.sig⟩)
    · simp only [frei_cons]
      omega
    · intro i hi
      have := hpr i hi
      simp only [frei_cons]
      omega
  · exact Or.inr (Or.inr (Or.inl ⟨e, hR, st⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨e, hR, st⟩))

/-- Select the normal arm without assuming that it runs to completion. -/
theorem BodyFrame.randBIR_bindCallElse_ok {B : BodyFrame D} (hB : B.Ok) {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {τ : Ty} {g : D.Fn} {args : Args D Γ Λ (D.params g)}
    {he : D.erg g = some τ} {hp : RufPasst D (vertragVon D B.f) (D.signatur g) Λ}
    {hr : 0 < D.gruende g}
    {err : Endblock D (vertragVon D B.f) l (.why (D.gruende g) :: Γ) (nach D g Λ)}
    {rest : Block D (vertragVon D B.f) l (τ :: Γ) (nach D g Λ) Λ'}
    {pc : Runner.W} {m : Runner.Mem} {σ σ2 : World D} {ρ : Env D Γ} {v : ErgVal D (D.erg g)}
    (h : B.RandBIR (.bindCallElse g args he hp hr err rest) pc m σ ρ)
    (hR : B.R g (σ.lese Λ args.orte) (rufEnv g σ Λ args ρ) = .ok σ2 v) :
    ∃ (pc2 : Runner.W) (m2 : Runner.Mem) (n : Nat),
      Star ⟨pc, B.fp⟩ m ⟨pc2, B.fp⟩ m2 ∧ AgreeW B.L B.fp B.lo B.K m m2 ∧
      (B.suffix n).RandBIR rest pc2 m2 σ2 (.cons (ergWert he v) ρ) := by
  rcases BodyFrame.randBIR_bindCallElse hB h with
    ⟨σ', v', pc2, m2, n, heq, hs, ha, hb⟩ | ⟨σ', r, pc2, m2, heq, _⟩ | ⟨e, heq, _⟩ | ⟨e, heq, _⟩
  · rw [hR] at heq
    cases heq
    exact ⟨pc2, m2, n, hs, ha, hb⟩
  all_goals rw [hR] at heq; cases heq

/-- Select the reason arm. It binds a `why` value, never a normal result value. -/
theorem BodyFrame.randBIR_bindCallElse_why {B : BodyFrame D} (hB : B.Ok) {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {τ : Ty} {g : D.Fn} {args : Args D Γ Λ (D.params g)}
    {he : D.erg g = some τ} {hp : RufPasst D (vertragVon D B.f) (D.signatur g) Λ}
    {hr : 0 < D.gruende g}
    {err : Endblock D (vertragVon D B.f) l (.why (D.gruende g) :: Γ) (nach D g Λ)}
    {rest : Block D (vertragVon D B.f) l (τ :: Γ) (nach D g Λ) Λ'}
    {pc : Runner.W} {m : Runner.Mem} {σ σ2 : World D} {ρ : Env D Γ} {r : Fin (D.gruende g)}
    (h : B.RandBIR (.bindCallElse g args he hp hr err rest) pc m σ ρ)
    (hR : B.R g (σ.lese Λ args.orte) (rufEnv g σ Λ args ρ) = .why σ2 r) :
    ∃ (pc2 : Runner.W) (m2 : Runner.Mem),
      Star ⟨pc, B.fp⟩ m ⟨pc2, B.fp⟩ m2 ∧ AgreeW B.L B.fp B.lo B.K m m2 ∧
      B.RandIR err pc2 m2 σ2 (.cons r ρ) := by
  rcases BodyFrame.randBIR_bindCallElse hB h with
    ⟨σ', v, pc2, m2, n, heq, _⟩ | ⟨σ', r', pc2, m2, heq, hs, ha, hb⟩ | ⟨e, heq, _⟩ | ⟨e, heq, _⟩
  · rw [hR] at heq
    cases heq
  · rw [hR] at heq
    cases heq
    exact ⟨pc2, m2, hs, ha, hb⟩
  all_goals rw [hR] at heq; cases heq

#print axioms BodyFrame.randBIR_bindCallElse

end Gabbro.Stage0.Senke.BildLauf
