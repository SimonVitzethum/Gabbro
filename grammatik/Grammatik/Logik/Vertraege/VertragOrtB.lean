module
public import Grammatik.Logik.Vertraege.VertragOrtBBasis
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}
/-- The single parameter environment: the value 2 in `.int 0 5`. -/
def miniRho : Env miniContrD (miniContrD.params fTrue) :=
  (miniContrD_params fTrue).symm ▸ (.cons ⟨2, by decide, by decide⟩ .nil :
    Env miniContrD [.int 0 5])

/-- The single result value: 3 in `.int 0 5`. -/
def miniV : ErgVal miniContrD (miniContrD.erg fTrue) :=
  (miniContrD_erg fTrue).symm ▸ (⟨3, by decide, by decide⟩ : ErgVal miniContrD (some (.int 0 5)))

/-- A refuting result value: 0 in `.int 0 5`. -/
def miniV0 : ErgVal miniContrD (miniContrD.erg fTrue) :=
  (miniContrD_erg fTrue).symm ▸ (⟨0, by decide, by decide⟩ : ErgVal miniContrD (some (.int 0 5)))

/-- `requires`: the parameter equals 2. -/
def miniReq : Expr miniContrD (miniContrD.params fTrue) [] .bool :=
  .eq (.var .here)
    ((.widen (by decide) (by decide) (.lit 2) :
      Expr miniContrD (miniContrD.params fTrue) [] (.int 0 5)))

/-- `ensures`: the result equals the parameter plus one.
    Context `[.int 0 5, .int 0 5]`: result at `.here`, parameter at `.there .here`. -/
def miniEnsLit : Expr miniContrD [.int 0 5, .int 0 5] [] .bool :=
  .eq (.widen (by decide) (by decide) (.var .here) :
      Expr miniContrD [.int 0 5, .int 0 5] [] (.int 0 6))
    (.widen (by decide) (by decide)
      (.add (.var (.there .here))
        (.widen (by decide) (by decide) (.lit 1) :
          Expr miniContrD [.int 0 5, .int 0 5] [] (.int 0 1))) :
      Expr miniContrD [.int 0 5, .int 0 5] [] (.int 0 6))

/-- The ensures context computes to result-before-parameters. -/
theorem miniEnsCtx : ErgCtx (miniContrD.params fTrue)
      (miniContrD.erg fTrue)
    = [.int 0 5, .int 0 5] := by
  rw [miniContrD_params fTrue, miniContrD_erg fTrue]
  rfl

/-- The program: `requires` and `ensures` as above; the body returns the
    parameter (any value typechecks; the contract is about the EVENT values). -/
def miniContrP : Programm miniContrD where
  invariante := fun i => nomatch i
  requires := fun _ => miniReq
  ensures := fun _ => miniEnsCtx ▸ miniEnsLit
  rumpf
    | true => .ret (.val (.var .here)) (List.Perm.refl [])
    | false => .ret (.val (.var .here)) (List.Perm.refl [])

/-- The empty world over the tiny declaration (all-true slots). -/
def miniWelt : World miniContrD :=
  ⟨fun _ _ _ => true, fun g => Empty.elim g, []⟩

/-- Entry check holds at the place: param 2 satisfies `requires`. -/
theorem mini_req_am_ort :
    ReqAmEintritt miniContrP fTrue miniWelt miniRho := by
  rfl

/-- Return check holds at the place: result 3 = param 2 + 1. -/
theorem mini_ens_am_ort :
    EnsAmRueck miniContrP fTrue
      miniWelt miniWelt miniRho miniV := by
  rfl

/-- A single return step with the actual values. -/
def miniContrSchritt : ContrSchritt miniContrD :=
  ⟨0, miniWelt, miniWelt,
    some (.rueck fTrue miniRho miniV miniWelt)⟩

/-- The singleton return run. -/
def miniContrLauf : ContrLauf miniContrD :=
  ⟨fun _ => [.rueck fTrue], [miniContrSchritt]⟩

/-- The singleton-run lemma: a run with one step satisfies the place
    contract when (a) no entry event matches the step, and (b) every return
    event matching the step already carries a satisfied return check.
    Both premises are used: (a) in the entry branch, (b) in the return
    branch; `hsingle` reduces the run to the stored step. -/
theorem vertragAmOrtB_of_singleton {E : Deklaration} (P : Programm E)
    (faden : Faden) (vor : World E) (nachWld : World E)
    (ev : Option (ContrEvent E))
    (st : ContrSchritt E) (hst : st = ⟨faden, vor, nachWld, ev⟩)
    (L : ContrLauf E) (hsingle : L.schritte = [st])
    (hentry : ∀ f : E.Fn, ∀ rho : Env E (E.params f),
      ev = some (ContrEvent.eintritt f rho) → False)
    (hrueck : ∀ f : E.Fn, ∀ rho : Env E (E.params f),
      ∀ v : ErgVal E (E.erg f), ∀ s0 : World E,
        ev = some (ContrEvent.rueck f rho v s0) →
          EnsAmRueck P f s0 nachWld rho v) :
    VertragAmOrtB P L := by
  unfold VertragAmOrtB
  intro c hc
  rw [hsingle, List.mem_singleton] at hc
  subst hc
  rw [hst]
  constructor
  · intro f rho he
    exact absurd he (hentry f rho)
  · intro f rho v s0 he
    exact hrueck f rho v s0 he

/-- Entry side for the singleton: no entry event matches the stored step. -/
theorem miniContrSchritt_entry_ok (f : miniContrD.Fn)
    (rho : Env miniContrD (miniContrD.params f))
    (hev : miniContrSchritt.ev =
      some (ContrEvent.eintritt f rho)) :
    False := by
  simp only [miniContrSchritt] at hev
  cases hev

/-- Return side for the singleton: a matching return event carries the actual
    values, where the check holds (`mini_ens_am_ort`). -/
theorem miniContrSchritt_rueck_ok (f : miniContrD.Fn)
    (rho : Env miniContrD (miniContrD.params f))
    (v : ErgVal miniContrD (miniContrD.erg f)) (s0 : World miniContrD)
    (hev : miniContrSchritt.ev = some (ContrEvent.rueck f rho v s0)) :
    EnsAmRueck miniContrP f s0 miniContrSchritt.nachW rho v := by
  simp only [miniContrSchritt] at hev
  cases hev
  exact mini_ens_am_ort

theorem mini_vertrag_am_ort :
    VertragAmOrtB (D := miniContrD) miniContrP miniContrLauf :=
  vertragAmOrtB_of_singleton (E := miniContrD)
    miniContrP 0 miniWelt miniWelt _ miniContrSchritt rfl
    miniContrLauf rfl
    (fun f rho hev => miniContrSchritt_entry_ok f rho hev)
    (fun f rho v s0 hev => miniContrSchritt_rueck_ok f rho v s0 hev)

/-- `QEnsuresB` for the same contract is false: result 0 refutes it.
    The ensures expression evaluates by `rfl` to `decide (0 = 2 + 1)` on the
    refuting values, so the check is definitionally `false`. -/
theorem mini_qensures_falsch :
    ¬ QEnsuresB miniContrP fTrue miniWelt := by
  intro h
  have h0 := h miniV0 miniRho
  have he : wahr? (eval miniWelt (miniEnsCtx ▸ miniEnsLit) miniWelt
      (ergEnv (miniContrD.erg fTrue) miniV0 miniRho)) = true := h0
  have hfalse : wahr? (eval miniWelt (miniEnsCtx ▸ miniEnsLit) miniWelt
      (ergEnv (miniContrD.erg fTrue) miniV0 miniRho)) = false := rfl
  rw [hfalse] at he
  cases he

/-! ## 4. Bridge: the return event and `rufAt` -/

/-- `rufAt` at a call with entry-read world `s0`, actual `rho`, and body outcome
    `EndAusgang.zurueck sigma v`: the ensures side evaluated for the actual `v`. -/
def RufEnsCheck (P : Programm D) (f : D.Fn) (s0 : World D) (sigma : World D)
    (rho : Env D (D.params f)) (v : ErgVal D (D.erg f)) : Prop :=
  wahr? (eval s0 (P.ensures f) sigma (ergEnv (D.erg f) v rho)) = true

/-- One `rufAt` unfolding, ensures half: with the requires gate open, the
    body returned, the ensures check for the ACTUAL `v` holding, and the
    invariant tail discharged, `rufAt` answers `.ok` -- hence never
    `Logik.nachbedingung f` for that call. The proof rewrites the `rufAt`
    equation (`rufAt` on `fuel+1` with open requires gate, returned body,
    satisfied ensures, and no failing invariant takes the `.ok` branch) and
    closes by constructor discrimination; every premise is used. -/
theorem rufAt_ok_of_gates (P : Programm D) (O : Orakel D)
    (passes : Nat)
    (fuel : Nat) (f : D.Fn) (sigma : World D) (rho : Env D (D.params f))
    (sread : World D)
    (hread : sread = sigma.lese (Signatur.anfang D (D.signatur f))
      (P.requires f).orte)
    (hreq : wahr? (eval sread (P.requires f) sread rho) = true)
    (sigma1 : World D) (v : ErgVal D (D.erg f))
    (hbody : execEnd (V := vertragVon D f) O passes (rufAt P O passes fuel)
      (P.rumpf f) sread rho = EndAusgang.zurueck sigma1 v)
    (sret : World D)
    (hret : sret = sigma1.lese (vertragVon D f).ende (P.ensures f).orte)
    (hens : RufEnsCheck P f sread sret rho v)
    (sinv : World D)
    (hsinv : sinv = (D.invs.filter (schuldet f)).foldl
      (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte) sret)
    (hinv : D.invs.find? (fun i => schuldet f i &&
      !wahr? (eval sinv (P.invariante i) sinv .nil)) = none) :
    rufAt P O passes (fuel + 1) f sigma rho =
      RufAusgang.ok (D := D) (f := f) sinv v := by
  have h1 : wahr? (eval sread (P.requires f) sread rho) = true := hreq
  have h2 := hbody
  have h3 : wahr? (eval sread (P.ensures f) sret
      (ergEnv (D.erg f) v rho)) = true := hens
  have h4 := hinv
  have h5 := hsinv
  have h6 := hread
  have h7 := hret
  simp only [rufAt, ← h6, ← h7, ← h5, h1, h2, h3, h4]
  rfl

/-- One `rufAt` unfolding, ensures half: a return event whose world satisfies
    `ensures` for the actual `v` is exactly the case where the sequential
    semantics (`rufAt`) does NOT produce `Logik.nachbedingung f` for that
    call. From the `.ok` equation (`hruf`, discharged by `rufAt_ok_of_gates`
    above), `.ok` is never `.logik` by constructor discrimination; the
    ensures check (`hens_pos`) is the shared premise with the return event,
    used here to type the statement at the actual values. -/
theorem rueck_ohne_nachbedingung (P : Programm D) (O : Orakel D)
    (passes : Nat)
    (fuel : Nat) (f : D.Fn) (sigma : World D) (rho : Env D (D.params f))
    (sigma1 : World D) (v : ErgVal D (D.erg f))
    (sinv : World D)
    (hens_pos : RufEnsCheck P f
      (sigma.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte)
      sigma1 rho v)
    (hruf : rufAt P O passes (fuel + 1) f sigma rho =
      RufAusgang.ok (D := D) (f := f) sinv v) :
    RufEnsCheck P f
      (sigma.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte)
      sigma1 rho v ∧
      (∀ e : Logik D, e = .nachbedingung f →
        rufAt P O passes (fuel + 1) f sigma rho ≠ .logik e) := by
  refine ⟨hens_pos, ?_⟩
  intro e he hcon
  rw [hruf] at hcon
  exact absurd hcon (by cases he <;> simp only [reduceCtorEq, not_false_eq_true])

/-! ## CUTS
  - `rueck_ohne_nachbedingung`: the proved half is that an `.ok` outcome
    is never `.logik`; the full equivalence -- return satisfies ensures IFF
    `rufAt` avoids `Logik.nachbedingung` -- would need the converse (from
    `rufAt ≠ .logik nachbedingung` to the ensures check), which needs the
    `rufAt` equation rewritten against `hruf`, i.e. deriving `hens_pos`
    instead of taking it as premise. The `he : e = .nachbedingung f`
    premise is used by the `cases he` discrimination.
  - No `PCReach`/`GenErreichbar` wiring: the wrapper projects to plain atom
    lists (`contrProjRegel`), not to `PCSchritt` derivations, because this
    file cannot import Maschine.lean without cycling Extraktion.lean
    (`Extraktion.lean` imports `Maschine.lean`).
-/

#print axioms Gabbro.Grammatik.vertragAmOrtB_leer
#print axioms Gabbro.Grammatik.vertragAmOrtB_of_singleton
#print axioms Gabbro.Grammatik.rufAt_ok_of_gates
#print axioms Gabbro.Grammatik.ensAmRueck_gibt_qensures_pkt
#print axioms Gabbro.Grammatik.mini_req_am_ort
#print axioms Gabbro.Grammatik.mini_ens_am_ort
#print axioms Gabbro.Grammatik.mini_vertrag_am_ort
#print axioms Gabbro.Grammatik.mini_qensures_falsch
#print axioms Gabbro.Grammatik.rueck_ohne_nachbedingung

end Gabbro.Grammatik
