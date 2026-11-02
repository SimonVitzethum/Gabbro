module
public import Grammatik.Logik.Vertraege.Locations.AntwortOrteBasis
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}
set_option hygiene false in
/-! ## 3. Every rule keeps the site bound -/

/-- A head-local step. -/
macro "kopfAnt" : tactic => `(tactic| (
  refine Or.inl ⟨by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩
  dsimp only; rw [rufUpdateG_self]
  rw [‹(M.faeden f).kopf.rest = _›] at hok
  dsimp only at hok ⊢
  simp only [GRest.aR, Endblock.ants, Block.ants, Stmt.ants, ants_alsBlock,
    List.all_append, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true,
    Bool.true_and] at hok ⊢))

set_option maxHeartbeats 4000000 in
/-- **Every rule of G, classified by what it does to the site bound** (the twin of
    `schrittOrte`): (A) a head-local step keeps the stack and the function and carries `aR`
    to the new residue; (B) a push suspends the head as a caller frame carrying `aR` and
    enters the callee's body; (C) a pop resumes the caller, whose residue carried `aR`. -/
theorem schrittAnt {P : Programm D} {O : Orakel D} {pa : Nat} {M M' : RufMaschineG D}
    {f : Faden} (C : D.Ax ⊕ D.Reg → Bool) (hs : RufSchrittG P O pa M f M') :
    ((M'.faeden f).stapel = (M.faeden f).stapel ∧
      ((M.faeden f).kopf.rest.2.2.2.2.aR C → (M'.faeden f).kopf.rest.2.2.2.2.aR C)) ∨
    (∃ (g : D.Fn) (caller' : RufRahmenG D) (rho : Env D (D.params g)) (s0 : World D),
      (M'.faeden f).stapel = caller' :: (M.faeden f).stapel ∧
      (M'.faeden f).kopf = ⟨g, rho, s0, ⟨false, D.params g, Signatur.anfang D (D.signatur g),
        rho, .ende (P.rumpf g)⟩⟩ ∧
      ((M.faeden f).kopf.rest.2.2.2.2.aR C → caller'.rest.2.2.2.2.aR C)) ∨
    (∃ (caller : RufRahmenG D) (rst : List (RufRahmenG D)),
      (M.faeden f).stapel = caller :: rst ∧ (M'.faeden f).stapel = rst ∧
      (caller.rest.2.2.2.2.aR C → (M'.faeden f).kopf.rest.2.2.2.2.aR C)) := by
  cases hs with
  | g1 hs =>
    cases hs with
    | dannOnTagSome l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ τ b nutz hw =>
      kopfAnt
      have h := ants_armWahlG C arms (eval σ₁ v σ₁ ρ) (by simp_all)
      rw [hw] at h
      have h2 : b.ants.all C = true := h
      simp_all
    | dannOnTagNone l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ b nutz hw =>
      kopfAnt
      have h := ants_armWahlG C arms (eval σ₁ v σ₁ ρ) (by simp_all)
      rw [hw] at h
      have h2 : b.ants.all C = true := h
      simp_all
    | dannOnGrund l Γ Λ Λ' Λ'' n r arms rest k ρ hhead σ₁ hs₁ b hw =>
      kopfAnt
      have h := ants_grundWahlG C arms (eval σ₁ r σ₁ ρ) (by simp_all)
      rw [hw] at h
      simp_all
    | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho =>
      refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
        ⟨l, Γ, nach D g Λ, ρ, .ende rest⟩⟩, rho, s0,
        by dsimp only; rw [rufUpdateG_self],
        by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
      rw [hhead] at hok
      dsimp only at hok ⊢
      simp only [GRest.aR, Endblock.ants, Stmt.ants, List.all_append, List.all_nil,
        Bool.true_and] at hok ⊢
      exact hok
    | rueck caller rst hpop =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self], ?_⟩)
      dsimp only; rw [rufUpdateG_self]
      exact id
    | _ =>
      kopfAnt
      all_goals simp_all
  | g2 hs =>
    cases hs with
    | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead hΛ s0 hs0 rho =>
      refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
        ⟨l, Γ, nach D g Λ, ρ, .dann rest k⟩⟩, rho, s0,
        by dsimp only; rw [rufUpdateG_self],
        by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
      rw [hhead] at hok
      dsimp only at hok ⊢
      simp only [GRest.aR, Block.ants, Stmt.ants, List.all_append, List.all_nil,
        Bool.true_and] at hok ⊢
      exact hok
    | _ =>
      kopfAnt
      all_goals simp_all
  | g3 hs =>
    cases hs with
    | dannBindCall l Γ Λ Λ' Λ'' τ g args he hp hr rest k ρ hhead hΛ s0 hs0 rho =>
      refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
        ⟨l, Γ, nach D g Λ, ρ, .wartet rest k⟩⟩, rho, s0,
        by dsimp only; rw [rufUpdateG_self],
        by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
      rw [hhead] at hok
      dsimp only at hok ⊢
      simp only [GRest.aR, Block.ants] at hok ⊢
      exact hok
    | dannBindCallElse l Γ Λ Λ' Λ'' τ g args he hp hr err rest k ρ hhead hΛ s0 hs0 rho =>
      refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
        ⟨l, Γ, nach D g Λ, ρ, .wartetSonst (D.gruende g) err rest k⟩⟩, rho, s0,
        by dsimp only; rw [rufUpdateG_self],
        by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
      rw [hhead] at hok
      dsimp only at hok ⊢
      simp only [GRest.aR, Block.ants, List.all_append, Bool.and_eq_true] at hok ⊢
      exact ⟨hok.1.1, hok.1.2, hok.2⟩
    | dannCallInd l Γ Λ Λ' Λ'' n p args hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho =>
      refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
        ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .dann rest k⟩⟩, rho, s0,
        by dsimp only; rw [rufUpdateG_self],
        by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
      rw [hhead] at hok
      dsimp only at hok ⊢
      simp only [GRest.aR, Block.ants, Stmt.ants, List.all_append, List.all_nil,
        Bool.true_and] at hok ⊢
      exact hok
    | rufCallInd l Γ Λ n p args hp hr rest ρ hhead hΛ s0 hs0 g hg hv rho =>
      refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
        ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .ende rest⟩⟩, rho, s0,
        by dsimp only; rw [rufUpdateG_self],
        by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
      rw [hhead] at hok
      dsimp only at hok ⊢
      simp only [GRest.aR, Endblock.ants, Stmt.ants, List.all_append, List.all_nil,
        Bool.true_and] at hok ⊢
      exact hok
    | dannBindCallInd l Γ Λ Λ' Λ'' τ n p args he hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho =>
      refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
        ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .wartet rest k⟩⟩, rho, s0,
        by dsimp only; rw [rufUpdateG_self],
        by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
      rw [hhead] at hok
      dsimp only at hok ⊢
      simp only [GRest.aR, Block.ants] at hok ⊢
      exact hok
    | rueckBind caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self], ?_⟩)
      dsimp only; rw [rufUpdateG_self]; dsimp only
      rcases hcaller with hc | ⟨n, err, hc⟩ <;> rw [hc] <;> dsimp only <;>
        simp only [GRest.aR] <;> exact fun h => by simp_all
    | _ =>
      kopfAnt
      all_goals simp_all
  | g4 hs =>
    cases hs with
    | rueckCons caller rst hpop =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self], ?_⟩)
      dsimp only; rw [rufUpdateG_self]
      exact id
    | dannRet l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self], ?_⟩)
      dsimp only; rw [rufUpdateG_self]
      exact id
    | dannRetBind lk Γk Λk Λk'' e hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc
        hcaller =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self], ?_⟩)
      dsimp only; rw [rufUpdateG_self]; dsimp only
      rcases hcaller with hc | ⟨n, err, hc⟩ <;> rw [hc] <;> dsimp only <;>
        simp only [GRest.aR] <;> exact fun h => by simp_all
    | rueckConsBind lk Γk Λk e hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self], ?_⟩)
      dsimp only; rw [rufUpdateG_self]; dsimp only
      rcases hcaller with hc | ⟨n, err, hc⟩ <;> rw [hc] <;> dsimp only <;>
        simp only [GRest.aR] <;> exact fun h => by simp_all
    | rueckGrund r hperm ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self], ?_⟩)
      dsimp only; rw [rufUpdateG_self]; dsimp only
      rw [hcaller]; dsimp only
      simp only [GRest.aR, ants_alsBlock]
      exact fun h => ⟨h.1, h.2.2⟩
    | _ =>
      kopfAnt
      all_goals simp_all
  | g5 hs =>
    cases hs with
    | rueckConsGrund r hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self], ?_⟩)
      dsimp only; rw [rufUpdateG_self]; dsimp only
      rw [hcaller]; dsimp only
      simp only [GRest.aR, ants_alsBlock]
      exact fun h => ⟨h.1, h.2.2⟩
    | dannRetGrund r hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self], ?_⟩)
      dsimp only; rw [rufUpdateG_self]; dsimp only
      rw [hcaller]; dsimp only
      simp only [GRest.aR, ants_alsBlock]
      exact fun h => ⟨h.1, h.2.2⟩
    | _ =>
      kopfAnt
      all_goals simp_all
  | g6 hs =>
    cases hs with
    | _ =>
      kopfAnt
      all_goals simp_all

/-! ## 4. The frame invariant -/

/-- **The site bound of a thread**: every frame's residue has its answer sites in `C`. -/
def AntInvG (C : D.Ax ⊕ D.Reg → Bool) (z : RufFadenG D) : Prop :=
  ∀ F ∈ z.kopf :: z.stapel, F.rest.2.2.2.2.aR C

section Inv

variable {P : Programm D} {O : Orakel D} {pa : Nat} {C : D.Ax ⊕ D.Reg → Bool}

theorem antInvG_schritt (hB : ∀ g, (P.rumpf g).ants.all C = true) {M M' : RufMaschineG D}
    {f : Faden} (hs : RufSchrittG P O pa M f M') (h : AntInvG C (M.faeden f)) :
    AntInvG C (M'.faeden f) := by
  have hk := h _ List.mem_cons_self
  rcases schrittAnt C hs with ⟨hst, hR⟩ | ⟨g, caller', rho, s0, hst, hkopf, hR⟩ |
      ⟨caller, rst, hpop, hst, hR⟩
  · intro F hF
    rcases List.mem_cons.mp hF with rfl | hF
    · exact hR hk
    · rw [hst] at hF
      exact h F (List.mem_cons_of_mem _ hF)
  · have hc := hR hk
    intro F hF
    rw [hst, hkopf] at hF
    rcases List.mem_cons.mp hF with rfl | hF
    · exact hB g
    · rcases List.mem_cons.mp hF with rfl | hF
      · exact hc
      · exact h F (List.mem_cons_of_mem _ hF)
  · have hc := h caller (by rw [hpop]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    intro F hF
    rcases List.mem_cons.mp hF with rfl | hF
    · exact hR hc
    · rw [hst] at hF
      exact h F (by rw [hpop]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hF))

/-- **The site bound on every reachable machine**, when every body meets it: a frame enters
    with its function's body, and G continues only with sub-blocks of it. -/
theorem antInvG_erreichbar (hB : ∀ g, (P.rumpf g).ants.all C = true) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    {M : RufMaschineG D} (hr : RufErreichbarG P O pa (RufStartG P sp init) M) :
    ∀ t, AntInvG C (M.faeden t) := by
  induction hr with
  | start =>
      intro t F hF
      have e : (RufStartG P sp init).faeden t =
          ⟨[], ⟨(init t).1, (init t).2, sp.welt [], ⟨false, D.params (init t).1,
            Signatur.anfang D (D.signatur (init t).1), (init t).2, .ende (P.rumpf (init t).1)⟩⟩,
            startSpur (init t).1, [RufEreignisF.eintritt (init t).1 (init t).2 (sp.welt [])]⟩ := by
        show (match init t with
          | ⟨g, rho⟩ => (⟨[], ⟨g, rho, sp.welt [], ⟨false, D.params g,
              Signatur.anfang D (D.signatur g), rho, .ende (P.rumpf g)⟩⟩, startSpur g,
              [RufEreignisF.eintritt g rho (sp.welt [])]⟩ : RufFadenG D)) = _
        cases init t
        rfl
      rw [e] at hF
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
      subst hF
      exact hB _
  | schritt M M' u _ hs ih =>
      intro t
      by_cases htu : t = u
      · subst htu
        exact antInvG_schritt hB hs (ih t)
      · rw [rufSchrittG_fremd hs t htu]
        exact ih t

/-- **The head of a reachable thread, under the checker's site bound**: every block the head
    residue still runs has only admissible answer sites (`StelleOk`). -/
theorem kopf_ants (hB : ∀ g, ∀ x ∈ (P.rumpf g).ants, StelleOk D x) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    {M : RufMaschineG D} (hr : RufErreichbarG P O pa (RufStartG P sp init) M) (t : Faden) :
    (M.faeden t).kopf.rest.2.2.2.2.aR (stelleC D) :=
  antInvG_erreichbar (fun g => List.all_eq_true.mpr fun x hx => stelleC_iff.mpr (hB g x hx))
    sp init hr t _ List.mem_cons_self

end Inv

#print axioms Gabbro.Grammatik.schrittAnt
#print axioms Gabbro.Grammatik.antInvG_erreichbar
#print axioms Gabbro.Grammatik.kopf_ants

end Gabbro.Grammatik
