module
public import Bruecke.Teil.Lokal.Ruf
public import Bruecke.Teil.Lauf
public import Bruecke.Anweisung.Lokal.Kopf
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

/-- What the run of a lowered body says against its Body translation (the carried run conclusion):
    every `logik` outcome is a callee's, and a return has an answer table under which the Body
    run ends in a related state with the same answer. -/
abbrev LaufZielTeilB (u : UProg) (C : Fin u.fns.length → Prop) (c : Fin u.fns.length) (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    {Γ : Ctx} {Λ : List (Res (declOf u))} (b0 : Endblock (declOf u) (verOf u c) false Γ Λ)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (bs : List Gabbro.Body.Stmt) : Prop :=
  (∀ e, execEnd O passes R b0 σ ρ = .logik e →
    ∃ (g : (declOf u).Fn) (σr : World (declOf u)) (envA : Env (declOf u) ((declOf u).params g)),
      C g ∧ R g σr envA = .logik e) ∧
  (∀ σ' v, execEnd O passes R b0 σ ρ = .zurueck σ' v →
    ∃ A : List Eintrag, (∀ e ∈ A, EintragGut u e) ∧ Oben u A s.world ∧ Schluessel A ∧
      ∀ ρB, Treu A ρB → RahmenAlleC u C ρB →
        ∃ s', Gabbro.Body.finalState (Gabbro.Body.exec ρB bs s) = some s' ∧
          Gabbro.Body.finalValue (Gabbro.Body.exec ρB bs s) = ergValOf (verOf u c).erg v ∧
          WRel u σ' s'.world)

/-- **One step**: where the G outcome of `b0` is the one of `b1` (for `logik` and for a return), and
    the Body statement `x` steps to `s₁` without lowering a ghost counter, the conclusion for
    `b1` from `s₁` over `xs` is the conclusion for `b0` from `s` over `x :: xs`. -/
theorem laufZiel_schritt_teilB {c : Fin u.fns.length} {O : Orakel (declOf u)} {passes : Nat}
    {R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f}
    {Γ Γ₁ : Ctx} {Λ Λ₁ : List (Res (declOf u))}
    {b0 : Endblock (declOf u) (verOf u c) false Γ Λ}
    {b1 : Endblock (declOf u) (verOf u c) false Γ₁ Λ₁}
    {σ σ₁ : World (declOf u)} {ρ : Env (declOf u) Γ} {ρ₁ : Env (declOf u) Γ₁}
    {s s₁ : Gabbro.Body.State} {x : Gabbro.Body.Stmt} {xs : List Gabbro.Body.Stmt}
    (hrun : (∀ e, execEnd O passes R b0 σ ρ = .logik e → execEnd O passes R b1 σ₁ ρ₁ = .logik e) ∧
      (∀ σ' v, execEnd O passes R b0 σ ρ = .zurueck σ' v →
        execEnd O passes R b1 σ₁ ρ₁ = .zurueck σ' v))
    (hstep : ∀ ρB, RahmenAlleC u C ρB → Gabbro.Body.step ρB x s = .running s₁)
    (hgz : ∀ w, gz w s.world ≤ gz w s₁.world)
    (ih : LaufZielTeilB u C c O passes R b1 σ₁ ρ₁ s₁ xs) :
    LaufZielTeilB u C c O passes R b0 σ ρ s (x :: xs) := by
  refine ⟨fun e h => ih.1 e (hrun.1 e h), fun σ' v h => ?_⟩
  obtain ⟨A, hg, ho, hk, hb⟩ := ih.2 σ' v (hrun.2 σ' v h)
  refine ⟨A, hg, oben_mono hgz ho, hk, fun ρB hT hF => ?_⟩
  obtain ⟨s', h1, h2, h3⟩ := hb ρB hT hF
  refine ⟨s', ?_, ?_, h3⟩
  · rw [exec_cons_running ρB x xs s s₁ (hstep ρB hF)]; exact h1
  · rw [exec_cons_running ρB x xs s s₁ (hstep ρB hF)]; exact h2

end Gabbro.Bruecke
