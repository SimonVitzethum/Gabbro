/- C08 replay-blocker regression: the unused false software summary still
   makes the old global oracle class empty, but the conditional body class
   is inhabited. The false body post is now refused by premise (b); a true
   body post remains provable. No goal or machine semantics is changed. -/
module

public import Grammatik.Logik.Ruf.FremdRuf.T10CallSiteZeuge
public import Grammatik.Zielsatz.Atomar.AtomarZiel
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T12

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz.CallSiteReplayBlocker

open Gabbro.Grammatik Speichermodell
open CallSiteZeuge (decl memory world rho)
open CallSiteBlocker (traceOracle traceOracle_gut)

/-- This software item is declared but never called. -/
def contract : CallContract decl (decl.asignatur ()) where
  pre := .fls
  post := .fls

/-- The body immediately returns, violating its own normal post. -/
def program : Programm decl where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => .fls
  rumpf := fun _ => .ret .empty List.Perm.nil
  axVertrag := fun _ => contract

def unit : Einheit decl where
  P := program
  S := SperrInv.leer decl
  Q := fun _ _ _ => false
  starts := [⟨(), .nil⟩]
  sp0 := memory

/-- Unit results always decode, so no oracle can satisfy the global false Q.
    This does not depend on a frame, on the oracle's answer, or on reachability. -/
theorem no_global_summary (O : Orakel decl) : ¬ AxVertragO unit.Q O := by
  intro h
  exact Bool.false_ne_true (h () world (rho true) () rfl)

theorem binding : ForeignVertrag unit traceOracle := by
  constructor
  · intro a hsw σ ρ hp
    exact False.elim (Bool.false_ne_true hp)
  · intro a hsw σ ρ
    change some (Sum.inl ()) ≠ none
    intro h
    cases h

theorem post_cover : PostDeckt unit := by
  intro a hsw σ0 ρ σ1 v hp
  exact False.elim (Bool.false_ne_true hp)

theorem hardware [RootNativeFloat.Hardware] : HardwareAnnahmenHw traceOracle unit.Q :=
  ⟨traceOracle_gut, ⟨fun r => nomatch r, fun g => nomatch g⟩,
    (fun a hsw => absurd rfl hsw), inferInstance⟩

/-- Unlike the global false summary, the conditional class has an actual
    frame-respecting, register-local member: the unused software pre is false. -/
theorem conditional_summary : AxVertragOP (PreQ program) unit.Q traceOracle := by
  intro a σ ρ v hp
  have hf : PreQ program a (σ.fragt (.inl a)) ρ = false := by
    rw [preQ_sw program (by cases a; rfl)]
    rfl
  rw [hf] at hp
  exact False.elim (Bool.false_ne_true hp)

/-- The counterexample formerly used by `proposedGoal_false` no longer
    satisfies premise (b): an immediate return must prove its false post
    against the inhabited conditional oracle class. -/
theorem not_user : ¬ NutzerPflichtA unit := by
  intro h
  have hk := ((h.logik.1 0 ()).1).1 traceOracle (gutO_rahmenO traceOracle_gut)
    ⟨fun r => nomatch r, fun g => nomatch g⟩ conditional_summary
    (fun _ σ => σ) (fun L => nomatch L) idA (havocA_id _)
    (rufAusV []) (rufAusV_rahmen (vertraegeOkR_nil program))
    (rufAusV_ohneVorbedingung (vertraegeOkR_nil program).1) world .nil rfl
  exact Bool.false_ne_true (hk.1 _ () rfl)

/-- The repaired class also admits a positive duty witness: the same
    immediate return with a true body post, despite the unused false Q. -/
def goodProgram : Programm decl :=
  { program with
    ensures := fun _ => .tru }

def goodUnit : Einheit decl :=
  { unit with
    P := goodProgram }

theorem good_user : NutzerPflichtA goodUnit where
  logik := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro passes f
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · intro O hr hl hQ U hU A hA R hR hOV σ ρ hreq
        exact ⟨fun _ _ _ => rfl, fun _ h => by cases h⟩
      · intro O hr hl hQ U hU A hA R hR hOL σ ρ hreq e h
        cases h
      · intro O hr hl hQ U hU A hA R hR hOV σ ρ hreq σ' v h i
        exact nomatch i
      · intro O hr hl hQ U hU A hA R hR hOV σ ρ hreq σ' r
        exact r.elim0
    · intro L
      exact nomatch L
    · intro a σ σ' v ht hg
      rfl
    · exact ptrVerfeinert_trivial (fun _ _ _ => rfl) (fun _ => rfl)
  start :=
    { sperren := fun L => nomatch L
      req := fun _ _ => rfl }

/-- Premise (a) does not check logical truth of a function's ensures. -/
theorem checker : akzeptiertX_pruefer.akzeptiert unit [()] [] [] = true := by
  have hvoll : ∀ f : decl.Fn, f ∈ [()] := fun f => by
    cases f
    exact List.mem_singleton_self _
  simp only [akzeptiertX_pruefer, AkzeptiertX, Bool.and_eq_true]
  and_intros
  all_goals first
    | exact (schnittstellenB_iff hvoll).mpr (schnittstellen_standard _ _)
    | decide

/- The following small invariant proves the full unit call-site duty, not just
   a duty on an empty chosen replay history. Every runtime start is already at
   a bare return. Such heads remain returns under G and under presented memory. -/
private def ReturnedHeads {D : Deklaration} (M : RufMaschineG D) : Prop :=
  ∀ t, (M.faeden t).stapel = [] ∧
    ∃ (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (ρ : Env D Γ)
      (e : ErgExpr D Γ Λ (vertragVon D (M.faeden t).kopf.f).erg)
      (hp : Λ.Perm (vertragVon D (M.faeden t).kopf.f).ende),
      (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.ret e hp)⟩

private theorem returnedHeads_step {D : Deklaration} {P : Programm D} {O : Orakel D}
    {passes : Nat} {M M' : RufMaschineG D} {u : Faden}
    (hm : ReturnedHeads M) (hs : RufSchrittG P O passes M u M') : ReturnedHeads M' := by
  intro t
  by_cases htu : t = u
  · subst t
    obtain ⟨hst, l, Γ, Λ, ρ, e, hp, hr⟩ := hm u
    obtain ⟨spur, he⟩ := ret_leer_schritt hs _ rfl hst e hp ρ hr
    rw [he]
    exact ⟨hst, l, Γ, Λ, ρ, e, hp, hr⟩
  · rw [rufSchrittG_fremd hs t htu]
    exact hm t

private theorem returnedHeads_gx {D : Deklaration} {P : Programm D} {O : Orakel D}
    {passes : Nat} {Tg : D.Tab ⊕ D.Glob → Prop} {M M' : RufMaschineG D} {u : Faden}
    (hm : ReturnedHeads M) (hs : RufSchrittGX P O passes Tg M u M') : ReturnedHeads M' := by
  obtain ⟨sp, N, hs, _, _, _, he, _, _⟩ := hs
  have hn := returnedHeads_step (M := mitSpeicher M sp) hm hs
  unfold ReturnedHeads at hn ⊢
  rw [he]
  exact hn

private theorem returnedHeads_no_call {D : Deklaration} {M : RufMaschineG D}
    (hm : ReturnedHeads M) (t : Faden) : M.foreignCallKey t = none := by
  obtain ⟨_, l, Γ, Λ, ρ, e, hp, hr⟩ := hm t
  unfold RufMaschineG.foreignCallKey
  rw [hr]
  rfl

private theorem returnedHeads_start (sp : Speicher decl.mitRuhe)
    (init : Faden → Σ f : decl.mitRuhe.Fn, Env decl.mitRuhe (decl.mitRuhe.params f)) :
    ReturnedHeads (RufStartG unit.P.mitRuhe sp init) := by
  intro t
  refine ⟨rfl, ?_⟩
  cases hi : init t with
  | mk f ρ =>
    cases f with
    | none =>
      simp only [RufStartG, hi]
      exact ⟨false, [], [], ρ, .empty, List.Perm.nil, rfl⟩
    | some f =>
      cases f
      simp only [RufStartG, hi]
      exact ⟨false, [], [], ρ, .empty, List.Perm.nil, rfl⟩

/-- No software call head is reachable, for any binding, budget or runtime. -/
theorem call_sites : CallSitePflicht unit := by
  intro O H hh hf passes sp init hl a σ ρ hreach hsw
  obtain ⟨M, presented, t, hr, _, hk⟩ := hreach
  have hm : ReturnedHeads M := by
    induction hr with
    | start => exact returnedHeads_start sp init
    | schritt M M' u _ hs ih => exact returnedHeads_gx ih hs
  have hn := returnedHeads_no_call (M := mitSpeicher M presented) hm t
  rw [hn] at hk
  cases hk

/-- The actual runtime runs the sole declared start once and idles elsewhere. -/
def initial (t : Faden) :
    Σ f : decl.mitRuhe.Fn, Env decl.mitRuhe (decl.mitRuhe.params f) :=
  if t = 0 then ⟨some (), .nil⟩ else ⟨none, .nil⟩

theorem runtime : Laufzeit unit (speicherR memory) initial where
  lader := rfl
  start := by
    intro t
    by_cases ht : t = 0
    · right
      exact ⟨⟨(), .nil⟩, List.mem_cons_self, by rw [initial, if_pos ht]; rfl⟩
    · left
      exact if_neg ht
  einmal := by
    intro t u htu he
    by_cases ht : t = 0
    · have hu : u ≠ 0 := fun hu => htu (ht.trans hu.symm)
      simp only [initial, if_pos ht, if_neg hu] at he
      cases he
    · exact Or.inl (by simp only [initial, if_neg ht])

/-- The unchanged ZielFX conclusion is already false at the initial machine. -/
theorem start_post_fails :
    ¬ StartEndeG unit.P.mitRuhe (RufStartG unit.P.mitRuhe (speicherR memory) initial) := by
  intro h
  have hp := (h.1 0 rfl false [] [] .nil (.ende (.ret .empty List.Perm.nil)) .empty
    rfl ⟨List.Perm.nil, Or.inl rfl⟩).1
  exact Bool.false_ne_true hp

/-- The original counterexample retains its independent call-site, binding
    and cover duties; precisely the strengthened body duty now excludes it. -/
theorem counterexample_excluded :
    CallSitePflicht unit ∧ PostDeckt unit ∧ ForeignVertrag unit traceOracle ∧
      AxVertragOP (PreQ unit.P) unit.Q traceOracle ∧ ¬ NutzerPflichtA unit :=
  ⟨call_sites, post_cover, binding, conditional_summary, not_user⟩

end Gabbro.Grammatik.Zielsatz.CallSiteReplayBlocker

#print axioms Gabbro.Grammatik.Zielsatz.CallSiteReplayBlocker.counterexample_excluded
#print axioms Gabbro.Grammatik.Zielsatz.CallSiteReplayBlocker.good_user
