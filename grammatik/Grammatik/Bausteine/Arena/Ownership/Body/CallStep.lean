import Grammatik.Bausteine.Arena.Ownership.Body.Call

/-! A call against the actual call handler `R`. The only fact about `R` is
`Respects` for the interface contracts, which `rufAt_ownership` derives
from checked bodies; nothing is assumed of the callee. -/

namespace Gabbro.Grammatik.ArenaOwnership.Body

open Source

variable {D : Deklaration} {A : FreiForm D}

/-- An ownership interface for every function of the program. -/
abbrev Interfaces (A : FreiForm D) := ∀ f : D.Fn, Flow.Interface A f

def Interfaces.contracts (I : Interfaces A) : ∀ f, Contract D f := fun f => (I f).contract A

/-- What a value return gives the caller, by the callee's result kind. -/
def ValueBound (A : FreiForm D) (fr : Frame) (s0 : State) (c : Context) (σ : World D) {Γ : Ctx}
    (ρ : Env D Γ) : {erg : Option Ty} → Flow.Output A erg → ErgVal D erg → Prop
  | _, .plain, _ => Holds A fr s0 c σ ρ
  | _, .owner, v => Holds A fr s0 c.bindFresh σ (Env.cons (τ := Ty.index (D.count A.tab)) v ρ)

/-- The caller context with the result bound. -/
def resultContext (c : Context) {erg : Option Ty} : Flow.Output A erg → Context
  | .plain => c.bind none
  | .owner => c.bindFresh

/-- The caller context with the result discarded: an owning result keeps its
(now nameless) right, which `finish` refuses at every later return. -/
def dropContext (c : Context) {erg : Option Ty} : Flow.Output A erg → Context
  | .plain => c
  | .owner => c.bindFresh.drop

theorem ValueBound.bind {fr : Frame} {s0 : State} {c : Context} {σ : World D} {Γ : Ctx} {ρ : Env D Γ}
    {erg : Option Ty} {τ : Ty} (out : Flow.Output A erg) (he : erg = some τ) (v : ErgVal D erg)
    (h : ValueBound A fr s0 c σ ρ out v) :
    Holds A fr s0 (resultContext c out) σ (.cons (ergWert he v) ρ) := by
  cases out with
  | plain => exact Holds.bindNone h _
  | owner => cases he; exact h

theorem ValueBound.discard {fr : Frame} {s0 : State} {c : Context} {σ : World D} {Γ : Ctx} {ρ : Env D Γ}
    {erg : Option Ty} (out : Flow.Output A erg) (v : ErgVal D erg)
    (h : ValueBound A fr s0 c σ ρ out v) : Holds A fr s0 (dropContext c out) σ ρ := by
  cases out with
  | plain => exact h
  | owner => exact Holds.drop h

section Step

variable {fr : Frame} {s0 s : State} {c : Context} {g : Ghost} {σ : World D} {Γ : Ctx} {ρ : Env D Γ}
  {ms : List (Option PassingMode)} {os : List (Option Nat)}

theorem returnOk_closed {s1 s2 : State} {cf : Frame} (hv : s2.valid) (hl : s1.local s2 cf)
    (hp : s1.progress s2) (hc : s2.closed cf) : ReturnOk s1 s2 cf none :=
  ⟨hv, hl, hp, fun j c hj ho => absurd ho (hc j c hj), fun _ h => by cases h⟩

theorem returnOk_single {s1 s2 : State} {cf : Frame} {h : Handle} (hv : s2.valid) (hl : s1.local s2 cf)
    (hp : s1.progress s2) (ho : s2.owns cf h) (hs : s2.single cf h) : ReturnOk s1 s2 cf (some h) := by
  refine ⟨hv, hl, hp, ?_, fun k hk => by cases hk; exact ho⟩
  intro j c hj howner
  obtain ⟨hslot, hloans⟩ := hs j c hj howner
  subst hslot
  have hm : c.matches h := by simp only [State.owns, hj] at ho; exact ho.1
  exact ⟨h, rfl, rfl, hloans, hm⟩

/-- The result kind decides how the caller continues. -/
theorem bound_of_result {erg : Option Ty} (out : Flow.Output A erg) (v : ErgVal D erg)
    (hR : Realizes c g A fr s σ ρ) (hc : Complete c g s fr) (hl : s0.local s fr) (hpr : s0.progress s)
    (hp : planFits c ms os = true) {s2 : State} {σ' : World D}
    (hloc : (s.handoff (calleeFrame A s fr) (movedHandles g ms os) (lentHandles g ms os)).local s2
      (calleeFrame A s fr))
    (hprog : (s.handoff (calleeFrame A s fr) (movedHandles g ms os) (lentHandles g ms os)).progress s2)
    (ha : s2.agrees A σ') (hf : A.FreiOk σ') (hres : out.result A (calleeFrame A s fr) s2 v) :
    ValueBound A fr s0 (c.afterCall ms os) σ' ρ out v := by
  cases out with
  | plain => exact return_plain hR hc hl hpr hp (returnOk_closed ha.1 hloc hprog hres) ha hf
  | owner =>
    obtain ⟨h, ho, hslot, hsingle⟩ := hres
    exact return_owner hR hc hl hpr hp (returnOk_single ha.1 hloc hprog ho hsingle) ha hf v hslot

variable (I : Interfaces A) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

/-- **A direct call that returns a value.** -/
theorem call_value (hR : Respects A I.contracts R) {Λ : List (Res D)} (f : D.Fn)
    (args : Args D Γ Λ (D.params f)) (h : Holds A fr s0 c σ ρ)
    (hp : planFits c (modeList (I f).parameters) (originList c args) = true)
    {σ' : World D} {v : ErgVal D (D.erg f)}
    (hrun : R f σ (evalArgs σ args σ ρ) = .ok σ' v) :
    ValueBound A fr s0 (c.afterCall (modeList (I f).parameters) (originList c args)) σ' ρ (I f).output v := by
  obtain ⟨g, s, hRz, hc, hl, hpr⟩ := h
  have hok := handoff_ok (ms := modeList (I f).parameters) (os := originList c args) hRz hp
  obtain ⟨href, hr, hcomp⟩ := handoff_requires (I f).parameters args rfl rfl hRz hp σ σ
  have hpost := (hR f _ _ σ _ (handoff_agrees hok hRz.1) hRz.2.1 ⟨_, href, hr, hcomp⟩).1 σ' v hrun
  obtain ⟨s2, ha2, hf2, hloc, hprog, hres⟩ := hpost
  exact bound_of_result (I f).output v hRz hc hl hpr hp hloc hprog ha2 hf2 hres

/-- **A direct call that returns a declared reason.** -/
theorem call_reason (hR : Respects A I.contracts R) {Λ : List (Res D)} (f : D.Fn)
    (args : Args D Γ Λ (D.params f)) (h : Holds A fr s0 c σ ρ)
    (hp : planFits c (modeList (I f).parameters) (originList c args) = true)
    {σ' : World D} {r : Fin (D.gruende f)}
    (hrun : R f σ (evalArgs σ args σ ρ) = .why σ' r) :
    Holds A fr s0 (c.afterCall (modeList (I f).parameters) (originList c args)) σ' ρ := by
  obtain ⟨g, s, hRz, hc, hl, hpr⟩ := h
  have hok := handoff_ok (ms := modeList (I f).parameters) (os := originList c args) hRz hp
  obtain ⟨href, hr, hcomp⟩ := handoff_requires (I f).parameters args rfl rfl hRz hp σ σ
  have hpost := (hR f _ _ σ _ (handoff_agrees hok hRz.1) hRz.2.1 ⟨_, href, hr, hcomp⟩).2 σ' r hrun
  obtain ⟨s2, ha2, hf2, hloc, hprog, hclosed⟩ := hpost
  exact return_plain hRz hc hl hpr hp (returnOk_closed ha2.1 hloc hprog hclosed) ha2 hf2

end Step

#print axioms call_value
#print axioms call_reason

end Gabbro.Grammatik.ArenaOwnership.Body
