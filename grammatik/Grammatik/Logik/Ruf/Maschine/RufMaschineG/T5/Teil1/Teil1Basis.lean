module

public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T4

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- Continuing past an optional result keeps a clean continuation clean. -/
theorem GRest.weiterOpt_sauber {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (e : Option Ty) (k : GRest D V l Γ Λ') :
    (GRest.weiterOpt (Λ := Λ) e k).sauber = k.sauber := by
  cases e <;> simp only [GRest.weiterOpt, GRest.sauber] <;> rfl

/-- Resuming a clean-or-waiting caller creates a clean head. -/
theorem antwortRestG_sauber (g : D.Fn)
    (a : ErgVal D (vertragVon D g).erg ⊕ Fin (vertragVon D g).gruende)
    {V : Vertrag D}
    (c c' : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D V l Γ Λ)
    (h : antwortRestG g a c = some c') (hc : c.2.2.2.2.stapelSauber = true) :
    c'.2.2.2.2.sauber = true := by
  obtain ⟨l, Γ, Λ, ρ, r⟩ := c
  cases a <;> cases r <;>
    simp_all [antwortRestG, GRest.stapelSauber, GRest.sauber]
  all_goals split at h <;> simp_all [GRest.sauber]

/-- Cleanup and either answer channel preserve the no-waiting-head invariant. -/
theorem rufAntwortG_sauber {z z' : RufFadenG D} {vor σ : World D}
    {a : ErgVal D (vertragVon D z.kopf.f).erg ⊕ Fin (vertragVon D z.kopf.f).gruende}
    (h : rufAntwortG z vor σ a = some z') (hz : RufFadenSauberG z) : RufFadenSauberG z' := by
  cases hs : z.stapel with
  | nil =>
      simp only [rufAntwortG, hs, Option.some.injEq] at h
      subst z'
      exact ⟨rfl, fun _ hm => List.not_mem_nil hm |>.elim⟩
  | cons c st =>
      have hc := hz.2 c (by rw [hs]; exact List.mem_cons_self)
      have ht : ∀ F ∈ st, F.rest.2.2.2.2.stapelSauber = true :=
        fun F hF => hz.2 F (by rw [hs]; exact List.mem_cons_of_mem _ hF)
      simp only [rufAntwortG, hs] at h
      cases hr : antwortRestG z.kopf.f a c.rest with
      | none => simp [hr] at h
      | some rest =>
          simp [hr] at h
          subst z'
          exact ⟨antwortRestG_sauber z.kopf.f a c.rest rest hr hc, ht⟩

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
    | rueckConsGrund =>
      rename_i ρ caller rst l Γ Λ Λ' τ n err restb k ρc hcaller g rho s0 rg hn r hperm restk hh hpop hΛ hfg hrho hs0 hrg
      obtain ⟨hc, hr⟩ := hpopS caller rst hpop
      simp only [rufUpdateG_self]
      rw [hcaller] at hc
      exact ⟨by simpa [GRest.sauber, GRest.stapelSauber] using hc, hr⟩
    | dannRetGrund =>
      rename_i ρ caller rst l Γ Λ Λ' τ n err restb k ρc hcaller g rho s0 rg hn r hperm restk kk hh hpop hΛ hfg hrho hs0 hrg
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
        first
        | exact hk
        | (rw [GRest.weiterOpt_sauber]; exact hk)
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
  | g7 hs =>
    cases hs with
    | rueckFreigabeLetzte _ _ _ _ z hantwort
    | rueckScopedWertDirekt _ _ _ _ _ _ _ _ _ _ _ _ _ z hantwort
    | rueckScopedGrundDirekt _ _ _ _ _ _ _ _ _ z hantwort =>
      simp only [rufUpdateG_self]
      exact rufAntwortG_sauber hantwort ⟨hk, hst⟩
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
