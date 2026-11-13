/- C08 replay blocker: conditional binding duties do not inhabit the oracle
   class quantified by the unchanged body obligations. An unused software item
   with false pre/post and false Q empties that class, admitting a returning
   body with false ensures. The proposed additive goal therefore cannot hold.
   This exhibit changes no goal, checker, semantics or assumption. -/
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
    decide

theorem post_cover : PostDeckt unit := by
  intro a hsw σ0 ρ σ1 v hp
  exact False.elim (Bool.false_ne_true hp)

theorem hardware [RootNativeFloat.Hardware] : HardwareAnnahmenHw traceOracle unit.Q :=
  ⟨traceOracle_gut, ⟨fun r => nomatch r, fun g => nomatch g⟩,
    (fun a hsw => absurd rfl hsw), inferInstance⟩

/-- All three body predicates are vacuous, even for this false body post.
    Start admission, locality and pointer refinement still hold separately. -/
theorem user : NutzerPflichtA unit where
  logik := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro passes f
      exact ⟨⟨fun O _ _ hQ => False.elim (no_global_summary O hQ),
        fun O _ _ hQ => False.elim (no_global_summary O hQ)⟩,
        fun O _ _ hQ => False.elim (no_global_summary O hQ),
        fun O _ _ hQ => False.elim (no_global_summary O hQ)⟩
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
  decide +kernel

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

/-- Exact proposed sibling-premise shape, kept local to the negative exhibit.
    The official goal must not acquire a proof of this false statement. -/
def ProposedGoal : Prop :=
  ∀ (C : PrueferX) (D : Deklaration) [DecidableEq D.Fn] (E : Einheit D)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob)),
    C.akzeptiert E fs.1 ls.1 cs.1 = true →
    NutzerPflichtA E →
    CallSitePflicht E →
    PostDeckt E →
    ∀ O : Orakel D, ForeignVertrag E O →
    HardwareAnnahmenHw O E.Q →
    ∀ (passes : Nat) (sp : Speicher D.mitRuhe)
      (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)),
      Laufzeit E sp init →
      ∀ (lebt0 : Faden → Bool) (K : FadenMaschine D.mitRuhe),
        FadenErreichbarX E.P.mitRuhe O.mitRuhe passes (GeteiltV E.P E.ws)
          (FadenStart E.P.mitRuhe sp init lebt0) K →
          ZielFX E.P.mitRuhe E.S.mitRuhe O.mitRuhe passes (GeteiltV E.P E.ws)
            (RufStartG E.P.mitRuhe sp init) (E.arenen.map (·.mitRuhe)) K

/-- All proposed premises coexist, but the initial return violates ZielFX.
    The native hardware contract is supplied, exactly as in positive witnesses. -/
theorem proposedGoal_false [RootNativeFloat.Hardware] : ¬ ProposedGoal := by
  intro h
  have hz := h akzeptiertX_pruefer decl unit ⟨[()], by intro f; cases f; exact List.mem_cons_self⟩
    ⟨[], fun L => nomatch L⟩ ⟨[], fun c => nomatch c⟩ checker user call_sites post_cover
    traceOracle binding hardware 0 (speicherR memory) initial runtime (fun _ => true)
    (FadenStart unit.P.mitRuhe (speicherR memory) initial (fun _ => true)) .start
  exact start_post_fails hz.g.startEnde

end Gabbro.Grammatik.Zielsatz.CallSiteReplayBlocker

#print axioms Gabbro.Grammatik.Zielsatz.CallSiteReplayBlocker.proposedGoal_false
