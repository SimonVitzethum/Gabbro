/- Part 7 of `FremdRuf` (C08): footprint locality of the interface contract.

   T5 carries the interim locality of the generalized contract (`AxVorLokal`,
   `AxNachLokal`: the pre/post is blind to everything outside the item's WRITE
   carriers). The contract expressions are ordinary `Expr`s, so their locality is a
   THEOREM of the evaluator (`Extraktion.eval_liest_nur_orte`): the pre reads only
   `(ax a).pre.orte`, the post only `(ax a).post.orte`, entry (`old`) and exit world
   separately. Here the two interim predicates are derived from one syntactic cover
   condition -- every carrier the contract reads is in the item's declared frame --
   and the cover condition itself is decidable over the finite unit. Reads of
   carriers outside the frame (protected read-only carriers under held guards) join
   as guarded footprints with the call-site duty; they are not claimed here. -/
module

public import Grammatik.Logik.Ruf.FremdRuf.T5
public import Grammatik.Kern.Syntax.Extensions.Extraktion.T3

@[expose] public section

namespace Gabbro.Grammatik

open Zielsatz

variable {D : Deklaration}

/-- **The pre reads only its footprint**: worlds that agree on the slots and globals the
    pre mentions agree on the pre. -/
theorem axVor_gleich (ax : ∀ a : D.Ax, CallContract D (D.asignatur a)) (a : D.Ax)
    (σ σ' : World D) (ρ : Env D (D.aparams a))
    (hT : ∀ t : D.Tab, Sum.inl t ∈ (ax a).pre.orte → σ.slots t = σ'.slots t)
    (hG : ∀ g : D.Glob, Sum.inr g ∈ (ax a).pre.orte → σ.globs g = σ'.globs g) :
    AxVor ax a σ ρ ↔ AxVor ax a σ' ρ := by
  have h := Extraktion.eval_liest_nur_orte (ax a).pre (ax a).pre.orte (fun o ho => ho)
    σ σ' σ σ' ρ
    (fun t ht k f => congrFun (congrFun (hT t ht) k) f) (fun g hg => hG g hg)
    (fun t ht k f => congrFun (congrFun (hT t ht) k) f) (fun g hg => hG g hg)
  unfold AxVor
  rw [h]

/-- **The post reads only its footprint**, entry world (`old`) and exit world separately:
    worlds that agree on the carriers the post mentions agree on the post. -/
theorem axNach_gleich (ax : ∀ a : D.Ax, CallContract D (D.asignatur a)) (a : D.Ax)
    (σ0 σ0' σ1 σ1' : World D) (ρ : Env D (D.aparams a)) (v : ErgVal D (D.aerg a))
    (hT0 : ∀ t : D.Tab, Sum.inl t ∈ (ax a).post.orte → σ0.slots t = σ0'.slots t)
    (hG0 : ∀ g : D.Glob, Sum.inr g ∈ (ax a).post.orte → σ0.globs g = σ0'.globs g)
    (hT1 : ∀ t : D.Tab, Sum.inl t ∈ (ax a).post.orte → σ1.slots t = σ1'.slots t)
    (hG1 : ∀ g : D.Glob, Sum.inr g ∈ (ax a).post.orte → σ1.globs g = σ1'.globs g) :
    AxNach ax a σ0 ρ σ1 v ↔ AxNach ax a σ0' ρ σ1' v := by
  have h := Extraktion.eval_liest_nur_orte (ax a).post (ax a).post.orte (fun o ho => ho)
    σ0 σ0' σ1 σ1' (ergEnv (D.aerg a) v ρ)
    (fun t ht k f => congrFun (congrFun (hT1 t ht) k) f) (fun g hg => hG1 g hg)
    (fun t ht k f => congrFun (congrFun (hT0 t ht) k) f) (fun g hg => hG0 g hg)
  unfold AxNach
  rw [h]

/-- **The frame covers the pre's reads**: every carrier the pre mentions is a carrier the
    item declares it writes. A syntactic check over the finite unit. -/
def AxVorGedeckt (ax : ∀ a : D.Ax, CallContract D (D.asignatur a)) : Prop :=
  ∀ a : D.Ax, (∀ t : D.Tab, Sum.inl t ∈ (ax a).pre.orte → D.aschreibt a t = true) ∧
    (∀ g : D.Glob, Sum.inr g ∈ (ax a).pre.orte → D.agschreibt a g = true)

/-- **The frame covers the post's reads.** -/
def AxNachGedeckt (ax : ∀ a : D.Ax, CallContract D (D.asignatur a)) : Prop :=
  ∀ a : D.Ax, (∀ t : D.Tab, Sum.inl t ∈ (ax a).post.orte → D.aschreibt a t = true) ∧
    (∀ g : D.Glob, Sum.inr g ∈ (ax a).post.orte → D.agschreibt a g = true)

/-- The interim pre locality of T5 is a theorem once the frame covers the pre's reads. -/
theorem axVorLokal_of_gedeckt {ax : ∀ a : D.Ax, CallContract D (D.asignatur a)}
    (h : AxVorGedeckt ax) : AxVorLokal ax :=
  fun a σ σ' ρ hT hG =>
    axVor_gleich ax a σ σ' ρ (fun t ht => hT t ((h a).1 t ht)) (fun g hg => hG g ((h a).2 g hg))

/-- The interim post locality of T5 is a theorem once the frame covers the post's reads. -/
theorem axNachLokal_of_gedeckt {ax : ∀ a : D.Ax, CallContract D (D.asignatur a)}
    (h : AxNachGedeckt ax) : AxNachLokal ax :=
  fun a σ0 σ1 σ1' ρ v hT hG =>
    axNach_gleich ax a σ0 σ0 σ1 σ1' ρ v (fun _ _ => rfl) (fun _ _ => rfl)
      (fun t ht => hT t ((h a).1 t ht)) (fun g hg => hG g ((h a).2 g hg))

/-- The trivial contract reads nothing, so every frame covers it. -/
theorem axVorGedeckt_wahr (ax : ∀ a : D.Ax, CallContract D (D.asignatur a))
    (h : ∀ a, (ax a).pre = .tru) : AxVorGedeckt ax := by
  intro a
  have h0 : (ax a).pre.orte = [] := by rw [h a]; rfl
  exact ⟨fun t ht => by rw [h0] at ht; exact absurd ht (by simp),
    fun g hg => by rw [h0] at hg; exact absurd hg (by simp)⟩

/-- The trivial contract reads nothing, so every frame covers it. -/
theorem axNachGedeckt_wahr (ax : ∀ a : D.Ax, CallContract D (D.asignatur a))
    (h : ∀ a, (ax a).post = .tru) : AxNachGedeckt ax := by
  intro a
  have h0 : (ax a).post.orte = [] := by rw [h a]; rfl
  exact ⟨fun t ht => by rw [h0] at ht; exact absurd ht (by simp),
    fun g hg => by rw [h0] at hg; exact absurd hg (by simp)⟩

end Gabbro.Grammatik
