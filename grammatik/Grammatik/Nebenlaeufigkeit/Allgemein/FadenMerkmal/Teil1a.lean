module

public import Grammatik.Logik.Ruf.Umkehr.RufHaeltG
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG

public import Grammatik.Nebenlaeufigkeit.Allgemein.FadenMerkmal.Teil1
@[expose] public section


namespace Gabbro.Grammatik
variable {D : Deklaration}
set_option hygiene false in
/-! ## 3. Every rule, classified -/

/-- Case (A) of `schrittMerk`: a head-local step. -/
macro "kopfM" : tactic => `(tactic| (
  refine Or.inl ⟨by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self],
    fun A hok => ?_⟩
  dsimp only; rw [rufUpdateG_self]
  rw [‹(M.faeden f).kopf.rest = _›] at hok
  dsimp only at hok ⊢
  simp only [GRest.mR, mE, mB, mS, mB_alsBlock, Bool.and_eq_true] at hok ⊢))

set_option maxHeartbeats 2000000 in
/-- **Every rule of G, classified by what it does to the residue
    predicate**: (A) a head-local step keeps the stack and the function
    and carries `mR` to the new residue; (B) a push suspends the head as a
    caller frame carrying `mR`, and names a callee the old residue admitted;
    (C) a pop resumes the caller, whose residue carried `mR`. -/
theorem schrittMerk {P : Programm D} {O : Orakel D} {pa : Nat} {M M' : RufMaschineG D}
    {f : Faden} (hs : RufSchrittG P O pa M f M') :
    ((M'.faeden f).stapel = (M.faeden f).stapel ∧
      (M'.faeden f).kopf.f = (M.faeden f).kopf.f ∧
      ∀ A : Merkmal D, (M.faeden f).kopf.rest.2.2.2.2.mR A →
        (M'.faeden f).kopf.rest.2.2.2.2.mR A) ∨
    (∃ (g : D.Fn) (caller' : RufRahmenG D) (rho : Env D (D.params g)) (s0 : World D),
      (M'.faeden f).stapel = caller' :: (M.faeden f).stapel ∧
      caller'.f = (M.faeden f).kopf.f ∧
      (M'.faeden f).kopf = ⟨g, rho, s0, ⟨false, D.params g, Signatur.anfang D (D.signatur g),
        rho, .ende (P.rumpf g)⟩⟩ ∧
      ∀ A : Merkmal D, (M.faeden f).kopf.rest.2.2.2.2.mR A →
        RufZiel A g ∧ caller'.rest.2.2.2.2.mR A) ∨
    (∃ (caller : RufRahmenG D) (rst : List (RufRahmenG D)),
      (M.faeden f).stapel = caller :: rst ∧ (M'.faeden f).stapel = rst ∧
      (M'.faeden f).kopf.f = caller.f ∧
      ∀ A : Merkmal D, caller.rest.2.2.2.2.mR A → (M'.faeden f).kopf.rest.2.2.2.2.mR A) := by
  cases hs with
  | g1 hs =>
    cases hs with
    | dannOnTagSome l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ τ b nutz hw =>
      kopfM
      have h := mB_armWahlG A arms (eval σ₁ v σ₁ ρ) hok.1.1
      rw [hw] at h
      have h2 : mB A b = true := h
      simp_all
    | dannOnTagNone l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ b nutz hw =>
      kopfM
      have h := mB_armWahlG A arms (eval σ₁ v σ₁ ρ) hok.1.1
      rw [hw] at h
      have h2 : mB A b = true := h
      simp_all
    | dannOnGrund l Γ Λ Λ' Λ'' n r arms rest k ρ hhead σ₁ hs₁ b hw =>
      kopfM
      have h := mB_grundWahlG A arms (eval σ₁ r σ₁ ρ) hok.1.1
      rw [hw] at h
      simp_all
    | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho =>
      refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
        ⟨l, Γ, nach D g Λ, ρ, .ende rest⟩⟩, rho, s0,
        by dsimp only; rw [rufUpdateG_self], rfl,
        by dsimp only; rw [rufUpdateG_self], fun A hok => ?_⟩)
      rw [hhead] at hok
      dsimp only at hok ⊢
      simp only [GRest.mR, mE, mS, Bool.and_eq_true] at hok ⊢
      exact ⟨Or.inl hok.1, hok.2⟩
    | rueck caller rst hpop =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
        by dsimp only; rw [rufUpdateG_self], fun A => ?_⟩)
      dsimp only; rw [rufUpdateG_self]
      exact id
    | endeForm l Γ Λ e ρ hl hent hhead =>
      kopfM
      first
      | exact ⟨hok, fun L => (e.alsBlock.2.held_iff L).symm⟩
      | exact ⟨hok, fun L => (e.alsBlock.2.held_iff L).symm, trivial⟩
    | _ =>
      kopfM
      all_goals simp_all
  | g2 hs =>
    cases hs with
    | dannNarrowElse l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest k ρ hhead =>
      kopfM
      exact ⟨hok.1.1, abbruch_iff sonst rest, hok.2⟩
    | dannPruefFalsch l Γ Λ Λ' Λ'' c sonst rest k ρ hhead =>
      kopfM
      exact ⟨hok.1.1, abbruch_iff sonst rest, hok.2⟩
    | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead hΛ s0 hs0 rho =>
      refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
        ⟨l, Γ, nach D g Λ, ρ, .dann rest k⟩⟩, rho, s0,
        by dsimp only; rw [rufUpdateG_self], rfl,
        by dsimp only; rw [rufUpdateG_self], fun A hok => ?_⟩)
      rw [hhead] at hok
      dsimp only at hok ⊢
      simp only [GRest.mR, mB, mS, Bool.and_eq_true] at hok ⊢
      exact ⟨Or.inl hok.1.1, hok.1.2, hok.2⟩
    | _ =>
      kopfM
      all_goals simp_all
  | g3 hs =>
    cases hs with
    | dannBindCall l Γ Λ Λ' Λ'' τ g args he hp hr rest k ρ hhead hΛ s0 hs0 rho =>
      refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
        ⟨l, Γ, nach D g Λ, ρ, .wartet rest k⟩⟩, rho, s0,
        by dsimp only; rw [rufUpdateG_self], rfl,
        by dsimp only; rw [rufUpdateG_self], fun A hok => ?_⟩)
      rw [hhead] at hok
      dsimp only at hok ⊢
      simp only [GRest.mR, mB, Bool.and_eq_true] at hok ⊢
      exact ⟨Or.inl hok.1.1, hok.1.2, hok.2⟩
    | dannBindCallElse l Γ Λ Λ' Λ'' τ g args he hp hr err rest k ρ hhead hΛ s0 hs0 rho =>
      refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
        ⟨l, Γ, nach D g Λ, ρ, .wartetSonst (D.gruende g) err rest k⟩⟩, rho, s0,
        by dsimp only; rw [rufUpdateG_self], rfl,
        by dsimp only; rw [rufUpdateG_self], fun A hok => ?_⟩)
      rw [hhead] at hok
      dsimp only at hok ⊢
      simp only [GRest.mR, mB, Bool.and_eq_true] at hok ⊢
      exact ⟨Or.inl hok.1.1.1, hok.1.1.2, hok.1.2, hok.2⟩
    | dannCallInd l Γ Λ Λ' Λ'' n p args hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho =>
      refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
        ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .dann rest k⟩⟩, rho, s0,
        by dsimp only; rw [rufUpdateG_self], rfl,
        by dsimp only; rw [rufUpdateG_self], fun A hok => ?_⟩)
      rw [hhead] at hok
      dsimp only at hok ⊢
      simp only [GRest.mR, mB, mS, Bool.and_eq_true] at hok ⊢
      exact ⟨Or.inr ⟨_, hg, hok.1.1⟩, hok.1.2, hok.2⟩
    | rufCallInd l Γ Λ n p args hp hr rest ρ hhead hΛ s0 hs0 g hg hv rho =>
      refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
        ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .ende rest⟩⟩, rho, s0,
        by dsimp only; rw [rufUpdateG_self], rfl,
        by dsimp only; rw [rufUpdateG_self], fun A hok => ?_⟩)
      rw [hhead] at hok
      dsimp only at hok ⊢
      simp only [GRest.mR, mE, mS, Bool.and_eq_true] at hok ⊢
      exact ⟨Or.inr ⟨_, hg, hok.1⟩, hok.2⟩
    | dannBindCallInd l Γ Λ Λ' Λ'' τ n p args he hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho =>
      refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
        ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .wartet rest k⟩⟩, rho, s0,
        by dsimp only; rw [rufUpdateG_self], rfl,
        by dsimp only; rw [rufUpdateG_self], fun A hok => ?_⟩)
      rw [hhead] at hok
      dsimp only at hok ⊢
      simp only [GRest.mR, mB, Bool.and_eq_true] at hok ⊢
      exact ⟨Or.inr ⟨_, hg, hok.1.1⟩, hok.1.2, hok.2⟩
    | rueckBind caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
        by dsimp only; rw [rufUpdateG_self], fun A => ?_⟩)
      dsimp only; rw [rufUpdateG_self]; dsimp only
      rcases hcaller with hc | ⟨n, err, hc⟩ <;> rw [hc] <;> dsimp only <;>
        simp only [GRest.mR] <;> exact fun h => by simp_all
    | _ =>
      kopfM
      all_goals simp_all
  | g4 hs =>
    cases hs with
    | rueckCons caller rst hpop =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
        by dsimp only; rw [rufUpdateG_self], fun A => ?_⟩)
      dsimp only; rw [rufUpdateG_self]
      exact id
    | dannRet l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
        by dsimp only; rw [rufUpdateG_self], fun A => ?_⟩)
      dsimp only; rw [rufUpdateG_self]
      exact id
    | dannRetBind lk Γk Λk Λk'' e hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc
        hcaller =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
        by dsimp only; rw [rufUpdateG_self], fun A => ?_⟩)
      dsimp only; rw [rufUpdateG_self]; dsimp only
      rcases hcaller with hc | ⟨n, err, hc⟩ <;> rw [hc] <;> dsimp only <;>
        simp only [GRest.mR] <;> exact fun h => by simp_all
    | rueckConsBind lk Γk Λk e hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
        by dsimp only; rw [rufUpdateG_self], fun A => ?_⟩)
      dsimp only; rw [rufUpdateG_self]; dsimp only
      rcases hcaller with hc | ⟨n, err, hc⟩ <;> rw [hc] <;> dsimp only <;>
        simp only [GRest.mR] <;> exact fun h => by simp_all
    | rueckGrund r hperm ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
        by dsimp only; rw [rufUpdateG_self], fun A => ?_⟩)
      dsimp only; rw [rufUpdateG_self]; dsimp only
      rw [hcaller]; dsimp only
      simp only [GRest.mR, mB_alsBlock]
      exact fun h => ⟨h.1, abbruch_iff err restb, h.2.2⟩
    | _ =>
      kopfM
      all_goals simp_all
  | g5 hs =>
    cases hs with
    | dannGleitNarrowElse l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead =>
      kopfM
      exact ⟨hok.1.1, abbruch_iff sonst rest, hok.2⟩
    | dannRegLiesElseFalsch l Γ Λ Λ' r hk zusage sonst rest k ρ hhead =>
      kopfM
      exact ⟨hok.1.1, abbruch_iff sonst rest, hok.2⟩
    | rueckConsGrund r hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
        by dsimp only; rw [rufUpdateG_self], fun A => ?_⟩)
      dsimp only; rw [rufUpdateG_self]; dsimp only
      rw [hcaller]; dsimp only
      simp only [GRest.mR, mB_alsBlock]
      exact fun h => ⟨h.1, abbruch_iff err restb, h.2.2⟩
    | dannRetGrund r hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
        by dsimp only; rw [rufUpdateG_self], fun A => ?_⟩)
      dsimp only; rw [rufUpdateG_self]; dsimp only
      rw [hcaller]; dsimp only
      simp only [GRest.mR, mB_alsBlock]
      exact fun h => ⟨h.1, abbruch_iff err restb, h.2.2⟩
    | dannBindAxiomElseGrund l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest k ρ hhead σ₁ hs₁ σ₂ r hax
        neu hneu hΛ =>
      kopfM
      exact ⟨hok.1.1, abbruch_iff err rest, hok.2⟩
    | _ =>
      kopfM
      all_goals simp_all
  | g6 hs =>
    cases hs with
    | _ =>
      kopfM
      all_goals simp_all

/-! ## 4. The thread invariant -/

/-- **The thread invariant**: every frame runs a function in `Z`, and its
    residue carries the predicate at the feature set of its function. -/
def MerkInvG (Z : D.Fn → Prop) (A : D.Fn → Merkmal D) (z : RufFadenG D) : Prop :=
  ∀ F ∈ z.kopf :: z.stapel, Z F.f ∧ F.rest.2.2.2.2.mR (A F.f)

/-- **The closure of a feature assignment**: every function in `Z` has an
    admitted body, and every callee its features admit is in `Z`. -/
def MerkAbg (P : Programm D) (Z : D.Fn → Prop) (A : D.Fn → Merkmal D) : Prop :=
  ∀ f, Z f → mE (A f) (P.rumpf f) = true ∧ ∀ g, RufZiel (A f) g → Z g

section Inv

variable {P : Programm D} {O : Orakel D} {pa : Nat}

end Inv
end Gabbro.Grammatik
