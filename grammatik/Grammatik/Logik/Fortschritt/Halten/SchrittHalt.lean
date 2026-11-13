/-
  File:      Grammatik/Logik/Fortschritt/Halten/SchrittHalt.lean
  Subject:   THE HOLD-BOUND CHECK ALONG EVERY RULE OF G: `schrittHalt` classifies every rule as in
             `schrittMerk` (FadenMerkmal): a head-local step carries `GRest.hR` to the new residue, a push
             carries it to the suspended caller, a pop resumes a caller with it. The thread invariant
             `HaltInvG` (every frame's residue passes the walker) then holds on every reachable machine of a
             program all of whose bodies pass it (`haltInvG_erreichbar`).
-/
module
public import Grammatik.Logik.Fortschritt.Halten.RestHalt
public import Grammatik.Nebenlaeufigkeit.Allgemein.FadenMerkmal.Teil1a
@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

set_option hygiene false in
/-- Case (A) of `schrittHalt`: a head-local step. -/
macro "kopfH" : tactic => `(tactic| (
  refine Or.inl ⟨by dsimp only; rw [rufUpdateG_self], fun ep hok => ?_⟩
  dsimp only; rw [rufUpdateG_self]
  rw [‹(M.faeden f).kopf.rest = _›] at hok
  dsimp only at hok ⊢
  simp only [GRest.hR, haltE, haltB, haltS, haltB_alsBlock, Bool.and_eq_true] at hok ⊢))

set_option hygiene false in
/-- Case (B) of `schrittHalt`: a push, the caller suspended with the rest of its residue. -/
macro "rufH" : tactic => `(tactic| (
  rw [‹(M.faeden f).kopf.rest = _›] at hok
  dsimp only at hok ⊢
  simp only [GRest.hR, haltE, haltB, haltS, Bool.and_eq_true] at hok ⊢
  simp_all))

set_option maxHeartbeats 2000000 in
/-- **Every rule of G, classified by what it does to the hold-bound predicate**: (A) a head-local step
    keeps the stack and carries `hR` to the new residue; (B) a push suspends the head as a caller frame
    carrying `hR`; (C) a pop resumes the caller, whose residue carried `hR`. Each case holds at every
    return-predicate price `ep`: a frame keeps the price its body was checked with. -/
theorem schrittHalt (h : D.Lock → Option Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool) (pa' : Nat)
    {P : Programm D} {O : Orakel D} {pa : Nat} {M M' : RufMaschineG D}
    {f : Faden} (hs : RufSchrittG P O pa M f M') :
    ((M'.faeden f).stapel = (M.faeden f).stapel ∧
      ∀ ep, (GRest.hR h ep c Z pa' (M.faeden f).kopf.rest.2.2.2.2 →
        GRest.hR h ep c Z pa' (M'.faeden f).kopf.rest.2.2.2.2)) ∨
    (∃ (g : D.Fn) (caller' : RufRahmenG D) (rho : Env D (D.params g)) (s0 : World D),
      (M'.faeden f).stapel = caller' :: (M.faeden f).stapel ∧
      (M'.faeden f).kopf = ⟨g, rho, s0, ⟨false, D.params g, Signatur.anfang D (D.signatur g),
        rho, .ende (P.rumpf g)⟩⟩ ∧
      ∀ ep, (GRest.hR h ep c Z pa' (M.faeden f).kopf.rest.2.2.2.2 →
        GRest.hR h ep c Z pa' caller'.rest.2.2.2.2)) ∨
    (∃ (caller : RufRahmenG D) (rst : List (RufRahmenG D)),
      (M.faeden f).stapel = caller :: rst ∧ (M'.faeden f).stapel = rst ∧
      ∀ ep, (GRest.hR h ep c Z pa' caller.rest.2.2.2.2 →
        GRest.hR h ep c Z pa' (M'.faeden f).kopf.rest.2.2.2.2)) := by
  cases hs with
  | g1 hs =>
    cases hs with
    | dannOnTagSome l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ τ b nutz hw =>
      kopfH
      have hh := haltB_armWahlG h ep c Z pa' arms (eval σ₁ v σ₁ ρ) hok.1.1
      rw [hw] at hh
      have h2 : haltB h ep c Z pa' b = true := hh
      simp_all
    | dannOnTagNone l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ b nutz hw =>
      kopfH
      have hh := haltB_armWahlG h ep c Z pa' arms (eval σ₁ v σ₁ ρ) hok.1.1
      rw [hw] at hh
      have h2 : haltB h ep c Z pa' b = true := hh
      simp_all
    | dannOnGrund l Γ Λ Λ' Λ'' n r arms rest k ρ hhead σ₁ hs₁ b hw =>
      kopfH
      have hh := haltB_grundWahlG h ep c Z pa' arms (eval σ₁ r σ₁ ρ) hok.1.1
      rw [hw] at hh
      simp_all
    | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho =>
      refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
        ⟨l, Γ, nach D g Λ, ρ, .ende rest⟩⟩, rho, s0,
        by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], fun ep hok => ?_⟩)
      rufH
    | rueck caller rst hpop =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self], fun ep hm => ?_⟩)
      dsimp only; rw [rufUpdateG_self]
      exact hm
    | _ =>
      kopfH
      all_goals simp_all [GRest.hR_weiterOpt]
  | g2 hs =>
    cases hs with
    | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead hΛ s0 hs0 rho =>
      refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
        ⟨l, Γ, nach D g Λ, ρ, .dann rest k⟩⟩, rho, s0,
        by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], fun ep hok => ?_⟩)
      rufH
    | _ =>
      kopfH
      all_goals simp_all [GRest.hR_weiterOpt]
  | g3 hs =>
    cases hs with
    | dannBindCall l Γ Λ Λ' Λ'' τ g args he hp hr rest k ρ hhead hΛ s0 hs0 rho =>
      refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
        ⟨l, Γ, nach D g Λ, ρ, .wartet rest k⟩⟩, rho, s0,
        by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], fun ep hok => ?_⟩)
      rufH
    | dannBindCallElse l Γ Λ Λ' Λ'' τ g args he hp hr err rest k ρ hhead hΛ s0 hs0 rho =>
      refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
        ⟨l, Γ, nach D g Λ, ρ, .wartetSonst (D.gruende g) err rest k⟩⟩, rho, s0,
        by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], fun ep hok => ?_⟩)
      rufH
    | dannCallInd l Γ Λ Λ' Λ'' n p args hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho =>
      refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
        ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .dann rest k⟩⟩, rho, s0,
        by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], fun ep hok => ?_⟩)
      rufH
    | rufCallInd l Γ Λ n p args hp hr rest ρ hhead hΛ s0 hs0 g hg hv rho =>
      refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
        ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .ende rest⟩⟩, rho, s0,
        by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], fun ep hok => ?_⟩)
      rufH
    | dannBindCallInd l Γ Λ Λ' Λ'' τ n p args he hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho =>
      refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
        ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .wartet rest k⟩⟩, rho, s0,
        by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], fun ep hok => ?_⟩)
      rufH
    | dannCallIndElse l Γ Λ Λ' Λ'' τ n p args he hp hr err rest k ρ hhead hΛ s0 hs0 g hg hv rho =>
      refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
        ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .wartetSonst (τ := τ) (D.sigNr n).gruende err .nil
          (.dann rest k)⟩⟩, rho, s0,
        by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], fun ep hok => ?_⟩)
      rufH
    | dannBindCallIndElse l Γ Λ Λ' Λ'' τ n p args he hp hr err rest k ρ hhead hΛ s0 hs0 g hg hv rho =>
      refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
        ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .wartetSonst (D.sigNr n).gruende err rest k⟩⟩, rho, s0,
        by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], fun ep hok => ?_⟩)
      rufH
    | rueckBind caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self], fun ep hm => ?_⟩)
      dsimp only; rw [rufUpdateG_self]; dsimp only
      rcases hcaller with hc | ⟨n, err, hc⟩ <;> rw [hc] at hm <;> dsimp only at hm ⊢ <;>
        simp only [GRest.hR] at hm ⊢ <;> simp_all
    | _ =>
      kopfH
      all_goals simp_all [GRest.hR_weiterOpt]
  | g4 hs =>
    cases hs with
    | rueckCons caller rst hpop =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self], fun ep hm => ?_⟩)
      dsimp only; rw [rufUpdateG_self]
      exact hm
    | dannRet l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self], fun ep hm => ?_⟩)
      dsimp only; rw [rufUpdateG_self]
      exact hm
    | dannRetBind lk Γk Λk Λk'' e hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc
        hcaller =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self], fun ep hm => ?_⟩)
      dsimp only; rw [rufUpdateG_self]; dsimp only
      rcases hcaller with hc | ⟨n, err, hc⟩ <;> rw [hc] at hm <;> dsimp only at hm ⊢ <;>
        simp only [GRest.hR] at hm ⊢ <;> simp_all
    | rueckConsBind lk Γk Λk e hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self], fun ep hm => ?_⟩)
      dsimp only; rw [rufUpdateG_self]; dsimp only
      rcases hcaller with hc | ⟨n, err, hc⟩ <;> rw [hc] at hm <;> dsimp only at hm ⊢ <;>
        simp only [GRest.hR] at hm ⊢ <;> simp_all
    | rueckGrund r hperm ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self], fun ep hm => ?_⟩)
      dsimp only; rw [rufUpdateG_self]; dsimp only
      rw [hcaller] at hm; dsimp only at hm ⊢
      simp only [GRest.hR, haltB_alsBlock] at hm ⊢
      exact ⟨hm.1, hm.2.2⟩
    | _ =>
      kopfH
      all_goals simp_all [GRest.hR_weiterOpt]
  | g5 hs =>
    cases hs with
    | rueckConsGrund _ _ r hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self], fun ep hm => ?_⟩)
      dsimp only; rw [rufUpdateG_self]; dsimp only
      rw [hcaller] at hm; dsimp only at hm ⊢
      simp only [GRest.hR, haltB_alsBlock] at hm ⊢
      exact ⟨hm.1, hm.2.2⟩
    | dannRetGrund _ _ r hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self], fun ep hm => ?_⟩)
      dsimp only; rw [rufUpdateG_self]; dsimp only
      rw [hcaller] at hm; dsimp only at hm ⊢
      simp only [GRest.hR, haltB_alsBlock] at hm ⊢
      exact ⟨hm.1, hm.2.2⟩
    | _ =>
      kopfH
      all_goals simp_all [GRest.hR_weiterOpt]
  | g6 hs =>
    cases hs with
    | _ =>
      kopfH
      all_goals simp_all [GRest.hR_weiterOpt]
  | g7 hs =>
    cases hs with
    | rueckFreigabeLetzte _ _ _ _ z hantwort
    | rueckScopedWertDirekt _ _ _ _ _ _ _ _ _ _ _ _ _ z hantwort
    | rueckScopedGrundDirekt _ _ _ _ _ _ _ _ _ z hantwort =>
      simp only [rufUpdateG_self]
      rcases rufAntwortG_hRcls h c Z pa' hantwort with ⟨h1, h3⟩ | ⟨cl, rst, h1, h2, h4⟩
      · exact Or.inl ⟨h1, fun ep hm => by rw [rufUpdateG_self]; exact h3 ep hm⟩
      · exact Or.inr (Or.inr ⟨cl, rst, h1, h2, fun ep hm => by rw [rufUpdateG_self]; exact h4 ep hm⟩)
    | _ =>
      kopfH
      all_goals simp_all [GRest.hR_weiterOpt]

/-! ## The thread invariant -/

/-- **Every frame's residue passes the hold-bound walker**, at the return-predicate price its body was
    checked with (existential per frame: a frame keeps its price for its whole lifetime). -/
def HaltInvG (h : D.Lock → Option Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool) (pa : Nat)
    (z : RufFadenG D) : Prop :=
  ∀ F ∈ z.kopf :: z.stapel, ∃ ep, GRest.hR h ep c Z pa F.rest.2.2.2.2

section Inv

variable (h : D.Lock → Option Nat) (E : D.Fn → Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool)
  {P : Programm D} {O : Orakel D} {pa : Nat}

/-- One step keeps the invariant: a pushed callee enters its whole body, which passes the walker at
    its own price `E g`. -/
theorem haltInvG_schritt (hP : ∀ g, haltE h (E g) c Z pa (P.rumpf g) = true) {M M' : RufMaschineG D}
    {u : Faden} (hs : RufSchrittG P O pa M u M') (hI : HaltInvG h c Z pa (M.faeden u)) :
    HaltInvG h c Z pa (M'.faeden u) := by
  rcases schrittHalt h c Z pa hs with ⟨hst, hk⟩ | ⟨g, cl, rho, s0, hst, hkopf, hc⟩ |
      ⟨cl, rst, hpop, hst, hc⟩
  · intro F hF
    rw [hst] at hF
    rcases List.mem_cons.mp hF with rfl | hF
    · obtain ⟨ep, hm⟩ := hI _ List.mem_cons_self
      exact ⟨ep, hk ep hm⟩
    · exact hI F (List.mem_cons_of_mem _ hF)
  · intro F hF
    rw [hst] at hF
    rcases List.mem_cons.mp hF with rfl | hF
    · rw [hkopf]; exact ⟨E g, hP g⟩
    · rcases List.mem_cons.mp hF with rfl | hF
      · obtain ⟨ep, hm⟩ := hI _ List.mem_cons_self
        exact ⟨ep, hc ep hm⟩
      · exact hI F (List.mem_cons_of_mem _ hF)
  · intro F hF
    rw [hst] at hF
    rcases List.mem_cons.mp hF with rfl | hF
    · obtain ⟨ep, hm⟩ := hI cl (by rw [hpop]; exact List.mem_cons_of_mem _ List.mem_cons_self)
      exact ⟨ep, hc ep hm⟩
    · exact hI F (by rw [hpop]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hF))

/-- The start machine satisfies the invariant: each thread runs one whole body. -/
theorem haltInvG_start (hP : ∀ g, haltE h (E g) c Z pa (P.rumpf g) = true) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (t : Faden) :
    HaltInvG h c Z pa ((RufStartG P sp init).faeden t) := by
  show HaltInvG h c Z pa (match init t with
    | ⟨g, rho⟩ => (⟨[], ⟨g, rho, sp.welt [], ⟨false, D.params g,
        Signatur.anfang D (D.signatur g), rho, .ende (P.rumpf g)⟩⟩, startSpur g,
        [RufEreignisF.eintritt g rho (sp.welt [])]⟩ : RufFadenG D))
  cases init t with
  | mk g rho =>
    intro F hF
    rcases List.mem_cons.mp hF with rfl | hF
    · exact ⟨E g, hP g⟩
    · exact absurd hF List.not_mem_nil

/-- **`HaltInvG` on every reachable machine** of a program all of whose bodies pass the walker. -/
theorem haltInvG_erreichbar (hP : ∀ g, haltE h (E g) c Z pa (P.rumpf g) = true) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) {M : RufMaschineG D}
    (hr : RufErreichbarG P O pa (RufStartG P sp init) M) : ∀ t, HaltInvG h c Z pa (M.faeden t) := by
  induction hr with
  | start => exact haltInvG_start h E c Z hP sp init
  | schritt M M' g _ hs ih =>
      intro t
      by_cases htg : t = g
      · subst htg
        exact haltInvG_schritt h E c Z hP hs (ih t)
      · rw [rufSchrittG_passt_anders P O pa M M' g t htg hs]
        exact ih t

end Inv

end Gabbro.Grammatik
