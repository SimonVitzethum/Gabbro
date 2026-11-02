module

public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T4

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- Every rule keeps the invariant of the acting thread. The pops are the
    point: a verbatim pop resumes a caller that does not wait (`hnw`), so
    the resumed head is clean; a binding pop resumes the waiting caller's
    continuation as a clean `dann` residue. -/
theorem rufSchrittG_sauber_acting {P : Programm D} {O : Orakel D} {passes : Nat}
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG P O passes M f M')
    (h : RufFadenSauberG (M.faeden f)) : RufFadenSauberG (M'.faeden f) := by
  obtain ⟨hk, hst⟩ := h
  have hpopS : ∀ (caller : RufRahmenG D) (rst : List (RufRahmenG D)),
      (M.faeden f).stapel = caller :: rst →
      caller.rest.2.2.2.2.stapelSauber = true ∧
        ∀ r ∈ rst, r.rest.2.2.2.2.stapelSauber = true := by
    intro caller rst hpop
    rw [hpop] at hst
    exact ⟨hst caller List.mem_cons_self, fun r hr => hst r (List.mem_cons_of_mem _ hr)⟩
  cases hs with
  | g1 hs =>
    cases hs with
    | rueck caller rst hpop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnw =>
      obtain ⟨hc, hr⟩ := hpopS caller rst hpop
      simp only [rufUpdateG_self]
      exact ⟨GRest.stapelSauber_sauber hnw hc, hr⟩
    | _ =>
      simp only [rufUpdateG_self]
      rw [‹(M.faeden f).kopf.rest = _›] at hk
      simp only [GRest.sauber] at hk
      refine ⟨?_, ?_⟩
      · simp only [GRest.sauber]
        try exact hk
      · first
        | exact hst
        | (intro r hr
           rcases List.mem_cons.1 hr with hr | hr
           · subst hr
             simp only [GRest.sauber, GRest.stapelSauber]
             try exact hk
           · exact hst r hr)
  | g2 hs =>
    cases hs with
    | _ =>
      simp only [rufUpdateG_self]
      rw [‹(M.faeden f).kopf.rest = _›] at hk
      simp only [GRest.sauber] at hk
      refine ⟨?_, ?_⟩
      · simp only [GRest.sauber]
        try exact hk
      · first
        | exact hst
        | (intro r hr
           rcases List.mem_cons.1 hr with hr | hr
           · subst hr
             simp only [GRest.sauber, GRest.stapelSauber]
             try exact hk
           · exact hst r hr)
  | g3 hs =>
    cases hs with
    | rueckBind caller rst hpop _ _ _ _ _ restb k _ hcaller =>
      obtain ⟨hc, hr⟩ := hpopS caller rst hpop
      simp only [rufUpdateG_self]
      refine ⟨?_, hr⟩
      rcases hcaller with hcaller | ⟨_, _, hcaller⟩ <;> rw [hcaller] at hc <;>
        simpa [GRest.sauber, GRest.stapelSauber] using hc
    | _ =>
      simp only [rufUpdateG_self]
      rw [‹(M.faeden f).kopf.rest = _›] at hk
      simp only [GRest.sauber] at hk
      refine ⟨?_, ?_⟩
      · simp only [GRest.sauber]
        try exact hk
      · first
        | exact hst
        | (intro r hr
           rcases List.mem_cons.1 hr with hr | hr
           · subst hr
             simp only [GRest.sauber, GRest.stapelSauber]
             try exact hk
           · exact hst r hr)
  | g4 hs =>
    cases hs with
    | rueckCons caller rst hpop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnw =>
      obtain ⟨hc, hr⟩ := hpopS caller rst hpop
      simp only [rufUpdateG_self]
      exact ⟨GRest.stapelSauber_sauber hnw hc, hr⟩
    | dannRet _ _ _ _ _ _ _ _ _ _ caller rst hpop _ _ _ _ _ _ _ _ _ _ _ _ _ hnw =>
      obtain ⟨hc, hr⟩ := hpopS caller rst hpop
      simp only [rufUpdateG_self]
      exact ⟨GRest.stapelSauber_sauber hnw hc, hr⟩
    | dannRetBind _ _ _ _ _ _ _ _ _ _ caller rst hpop _ _ _ _ _ restb k _ hcaller =>
      obtain ⟨hc, hr⟩ := hpopS caller rst hpop
      simp only [rufUpdateG_self]
      refine ⟨?_, hr⟩
      rcases hcaller with hcaller | ⟨_, _, hcaller⟩ <;> rw [hcaller] at hc <;>
        simpa [GRest.sauber, GRest.stapelSauber] using hc
    | rueckConsBind _ _ _ _ _ _ _ _ caller rst hpop _ _ _ _ _ restb k _ hcaller =>
      obtain ⟨hc, hr⟩ := hpopS caller rst hpop
      simp only [rufUpdateG_self]
      refine ⟨?_, hr⟩
      rcases hcaller with hcaller | ⟨_, _, hcaller⟩ <;> rw [hcaller] at hc <;>
        simpa [GRest.sauber, GRest.stapelSauber] using hc
    | rueckGrund _ _ _ _ caller rst hpop _ _ _ _ _ _ _ _ _ _ hcaller =>
      obtain ⟨hc, hr⟩ := hpopS caller rst hpop
      simp only [rufUpdateG_self]
      rw [hcaller] at hc
      exact ⟨by simpa [GRest.sauber, GRest.stapelSauber] using hc, hr⟩
    | _ =>
      simp only [rufUpdateG_self]
      rw [‹(M.faeden f).kopf.rest = _›] at hk
      simp only [GRest.sauber] at hk
      refine ⟨?_, ?_⟩
      · simp only [GRest.sauber]
        try exact hk
      · first
        | exact hst
        | (intro r hr
           rcases List.mem_cons.1 hr with hr | hr
           · subst hr
             simp only [GRest.sauber, GRest.stapelSauber]
             try exact hk
           · exact hst r hr)
  | g5 hs =>
    cases hs with
    | rueckConsGrund _ _ _ _ _ caller rst hpop _ _ _ _ _ _ _ _ _ _ hcaller =>
      obtain ⟨hc, hr⟩ := hpopS caller rst hpop
      simp only [rufUpdateG_self]
      rw [hcaller] at hc
      exact ⟨by simpa [GRest.sauber, GRest.stapelSauber] using hc, hr⟩
    | dannRetGrund _ _ _ _ _ _ caller rst hpop _ _ _ _ _ _ _ _ _ _ hcaller =>
      obtain ⟨hc, hr⟩ := hpopS caller rst hpop
      simp only [rufUpdateG_self]
      rw [hcaller] at hc
      exact ⟨by simpa [GRest.sauber, GRest.stapelSauber] using hc, hr⟩
    | _ =>
      simp only [rufUpdateG_self]
      rw [‹(M.faeden f).kopf.rest = _›] at hk
      simp only [GRest.sauber] at hk
      refine ⟨?_, ?_⟩
      · simp only [GRest.sauber]
        try exact hk
      · first
        | exact hst
        | (intro r hr
           rcases List.mem_cons.1 hr with hr | hr
           · subst hr
             simp only [GRest.sauber, GRest.stapelSauber]
             try exact hk
           · exact hst r hr)
  | g6 hs =>
    cases hs with
    | _ =>
      simp only [rufUpdateG_self]
      rw [‹(M.faeden f).kopf.rest = _›] at hk
      simp only [GRest.sauber] at hk
      refine ⟨?_, ?_⟩
      · simp only [GRest.sauber]
        try exact hk
      · first
        | exact hst
        | (intro r hr
           rcases List.mem_cons.1 hr with hr | hr
           · subst hr
             simp only [GRest.sauber, GRest.stapelSauber]
             try exact hk
           · exact hst r hr)

/-- Every step keeps the invariant at every thread. -/
theorem rufSchrittG_sauber {P : Programm D} {O : Orakel D} {passes : Nat}
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG P O passes M f M')
    (h : ∀ g, RufFadenSauberG (M.faeden g)) : ∀ g, RufFadenSauberG (M'.faeden g) := by
  intro g
  by_cases hg : g = f
  · subst hg
    exact rufSchrittG_sauber_acting hs (h g)
  · rw [rufSchrittG_passt_anders P O passes M M' f g hg hs]
    exact h g

/-- The start machine satisfies the invariant: empty stacks, `ende` heads. -/
theorem rufStartG_sauber (P : Programm D) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) :
    ∀ g, RufFadenSauberG ((RufStartG P sp init).faeden g) := by
  intro g
  refine ⟨rfl, ?_⟩
  intro r hr
  exact absurd hr List.not_mem_nil

/-- **No reachable head waits.** In every machine reachable from the start,
    no thread's head residue is a waiting node -- the deadlock the verbatim
    pops caused (a caller restored at `wartet …`, where no rule fires) can
    no longer arise. -/
theorem rufG_nie_wartend (P : Programm D) (O : Orakel D) (passes : Nat) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (M : RufMaschineG D)
    (h : RufErreichbarG P O passes (RufStartG P sp init) M) (f : Faden) :
    (M.faeden f).kopf.wartend = false := by
  have hinv : ∀ g, RufFadenSauberG (M.faeden g) := by
    induction h with
    | start => exact rufStartG_sauber P sp init
    | schritt M M' g _ hs ih => exact rufSchrittG_sauber hs ih
  exact (hinv f).kopf_wartend


end Gabbro.Grammatik
