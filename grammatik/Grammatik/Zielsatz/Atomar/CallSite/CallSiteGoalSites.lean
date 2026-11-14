/- C08 R3b: THE CALL-SITE DUTY OF THE WITNESS UNIT, over every run.

   `call_sites : CallSitePflicht wE` -- for every binding, budget and runtime start, every
   software call a GX run of `wE.P.mitRuhe` reaches has a true pre. Not vacuous: the start
   head IS the call `g(1)` (`start_call`), and the pre is falsifiable (`pre_false`).

   The invariant `Koepfe`: every thread has an empty stack and its head is a return, or the
   call `let r = g(args); return …` whose arguments meet `g`'s pre in every world. It holds at
   every start (the idle root returns, the declared function is the call), every step keeps it
   (`ret_leer_schritt`, `bindAxiom_ende_schritt`, other threads untouched), and a GX step is a
   G step on a presented memory with the same threads. -/
module

public import Grammatik.Zielsatz.Atomar.CallSite.CallSiteGoalFixture
public import Grammatik.Zielsatz.Atomar.CallSite.CallSiteGoalStep

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz.CallSiteGoal

open Gabbro.Grammatik Speichermodell

/-- The heads of every run of the unit. -/
def Koepfe (M : RufMaschineG wD.mitRuhe) : Prop :=
  ∀ t, (M.faeden t).stapel = [] ∧
    ((∃ (l : Bool) (Γ : Ctx) (Λ : List (Res wD.mitRuhe)) (ρ : Env wD.mitRuhe Γ)
        (e : ErgExpr wD.mitRuhe Γ Λ (vertragVon wD.mitRuhe (M.faeden t).kopf.f).erg)
        (hp : Λ.Perm (vertragVon wD.mitRuhe (M.faeden t).kopf.f).ende),
        (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.ret e hp)⟩) ∨
     (∃ (l : Bool) (Γ : Ctx) (Λ : List (Res wD.mitRuhe)) (ρ : Env wD.mitRuhe Γ) (τ : Ty)
        (args : Args wD.mitRuhe Γ Λ (wD.mitRuhe.aparams ()))
        (he : wD.mitRuhe.aerg () = some τ) (hw : _) (hg : _) (hd : _) (hgd : _)
        (e : ErgExpr wD.mitRuhe (τ :: Γ) Λ (vertragVon wD.mitRuhe (M.faeden t).kopf.f).erg)
        (hp : Λ.Perm (vertragVon wD.mitRuhe (M.faeden t).kopf.f).ende),
        (∀ (σ σ' : World wD.mitRuhe) (ρ' : Env wD.mitRuhe Γ),
          AxVor wE.P.mitRuhe.axVertrag () σ (evalArgs σ' args σ' ρ')) ∧
        (M.faeden t).kopf.rest =
          ⟨l, Γ, Λ, ρ, .ende (.bindAxiom () args he hw hg hd hgd (.ret e hp))⟩))

/-- Every start: the idle root is at its return, the declared function at the call `g(1)`. -/
theorem koepfe_start (sp : Speicher wD.mitRuhe)
    (init : Faden → Σ f : wD.mitRuhe.Fn, Env wD.mitRuhe (wD.mitRuhe.params f)) :
    Koepfe (RufStartG wE.P.mitRuhe sp init) := by
  unfold Koepfe
  intro t
  dsimp only [RufStartG]
  refine ⟨rfl, ?_⟩
  cases hi : init t with
  | mk f ρ =>
    cases f with
    | none =>
      simp only [hi]
      exact Or.inl ⟨false, [], [], ρ, .empty, List.Perm.nil, rfl⟩
    | some f =>
      cases f
      simp only [hi]
      refine Or.inr ⟨false, _, _, ρ, _, _, ?_, ?_, ?_, ?_, ?_, _, ?_, ?_, rfl⟩
      all_goals first
        | rfl
        | exact List.Perm.refl _
        | (intro _ _ _; rfl)
        | (intro t; cases t)
        | (intro t _; cases t)
        | decide
        | (intro _ h; exact absurd h (by decide))
        | simp_all

/-- A G step keeps the heads. -/
theorem koepfe_schritt {P : Programm wD.mitRuhe} {O : Orakel wD.mitRuhe} {passes : Nat}
    {M M' : RufMaschineG wD.mitRuhe} {u : Faden}
    (hm : Koepfe M) (hs : RufSchrittG P O passes M u M') : Koepfe M' := by
  intro t
  by_cases htu : t = u
  · subst t
    obtain ⟨hst, ⟨l, Γ, Λ, ρ, e, hp, hr⟩ | ⟨l, Γ, Λ, ρ, τ, args, he, hw, hg, hd, hgd, e, hp, _, hr⟩⟩ :=
      hm u
    · obtain ⟨spur, he'⟩ := ret_leer_schritt hs _ rfl hst e hp ρ hr
      rw [he']
      exact ⟨hst, Or.inl ⟨l, Γ, Λ, ρ, e, hp, hr⟩⟩
    · obtain ⟨w, spur, he'⟩ :=
        bindAxiom_ende_schritt hs _ rfl () args he hw hg hd hgd (.ret e hp) ρ hr
      rw [he']
      exact ⟨hst, Or.inl ⟨l, τ :: Γ, Λ, .cons w ρ, e, hp, rfl⟩⟩
  · rw [rufSchrittG_fremd hs t htu]
    exact hm t

/-- A GX step keeps the heads: G on a presented memory, the same threads after. -/
theorem koepfe_gx {P : Programm wD.mitRuhe} {O : Orakel wD.mitRuhe} {passes : Nat}
    {Tg : wD.mitRuhe.Tab ⊕ wD.mitRuhe.Glob → Prop} {M M' : RufMaschineG wD.mitRuhe} {u : Faden}
    (hm : Koepfe M) (hs : RufSchrittGX P O passes Tg M u M') : Koepfe M' := by
  obtain ⟨sp, N, hs, _, _, _, he, _, _⟩ := hs
  have hn := koepfe_schritt (M := mitSpeicher M sp) hm hs
  unfold Koepfe at hn ⊢
  rw [he]
  exact hn

/-- At the heads, the only question is the call, and its pre holds. -/
theorem koepfe_pre {M : RufMaschineG wD.mitRuhe} (hm : Koepfe M) {t : Faden} {a : wD.mitRuhe.Ax}
    {σ : World wD.mitRuhe} {ρ : Env wD.mitRuhe (wD.mitRuhe.aparams a)}
    (hk : M.foreignCallKey t = some ⟨a, σ, ρ⟩) : AxVor wE.P.mitRuhe.axVertrag a σ ρ := by
  obtain ⟨_, ⟨l, Γ, Λ, ρ0, e, hp, hr⟩ | ⟨l, Γ, Λ, ρ0, τ, args, he, hw, hg, hd, hgd, e, hp, hpre, hr⟩⟩ :=
    hm t
  · rw [RufMaschineG.foreignCallKey_rest hr] at hk
    cases hk
  · rw [RufMaschineG.foreignCallKey_rest hr] at hk
    have h1 := Option.some.inj hk
    try unfold foreignCallKey at h1
    cases h1
    exact hpre _ _ _

/-- **(b), the call-site duty**: every software call a run reaches meets `g`'s pre. -/
theorem call_sites : CallSitePflicht wE := by
  intro O H hh hf passes sp init hl a σ ρ hreach hsw
  obtain ⟨M, presented, t, hr, hsame, hk⟩ := hreach
  have hm : Koepfe M := by
    clear hk hsame
    induction hr with
    | start => exact koepfe_start sp init
    | schritt M M' u _ hs ih => exact koepfe_gx ih hs
  exact koepfe_pre (M := mitSpeicher M presented) hm hk

/-- Not vacuous: at the runtime's start, thread 0 asks `g` with a true pre. -/
theorem start_call :
    ∃ k, (RufStartG wE.P.mitRuhe (speicherR wE.sp0) (initRuhe wE.starts)).foreignCallKey 0 =
      some k ∧ AxVor wE.P.mitRuhe.axVertrag k.1 k.2.1 k.2.2 :=
  ⟨_, rfl, rfl⟩

end Gabbro.Grammatik.Zielsatz.CallSiteGoal
