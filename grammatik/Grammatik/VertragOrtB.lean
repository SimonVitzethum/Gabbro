/-
  File:      Grammatik/VertragOrtB.lean
  Subject:   CONTRACTS AT THEIR PLACE (attempt B) -- call entry and return events
             carrying the ACTUAL parameter environment and the ACTUAL result.

  Problem: `QRequires`/`QEnsures` (Extraktion.lean) quantify over EVERY parameter
  environment and EVERY result, so any contract that mentions a parameter or the
  result is false as a world predicate; the goal theorem then only covers
  invariants. The PC machine (`PCAtom`: leaf/take/rel, Maschine.lean) has no
  call or return events.

  Design (B): this file imports only `Grammatik.Semantik` (importing Maschine
  or Extraktion would cycle: Extraktion imports Maschine). It mirrors the two
  halves it needs:

    * `ContrAtom`: the `leaf`/`take`/`rel` cases of `PCAtom` plus `eintritt f`
      and `rueck f` positions. Plain PC programs embed by case
      (`contrAtomVonPC` is the identity on the three old cases).
    * `QEnsuresB`: the `QEnsures` shape restated locally (same quantifiers).

  A call event carries the function plus the actual values at its place:

    * `ContrEvent.eintritt f rho` -- entry of `f` with actual `rho`,
    * `ContrEvent.rueck f rho v s0` -- return with actual `rho`, actual `v`,
      and the ENTRY-side read world `s0` (entry world after its contract
      reads), because `ensures` evaluates `old(..)` in the entry world.

  A wrapper run (`ContrLauf`: per-thread atom lists plus contract-event
  steps) pairs PC positions with the optional contract event emitted there.
  The wrapper invents no machine motion: step worlds come from the sequential
  semantics (`World.lese` for contract reads; the return world from `execEnd`
  through the bridge lemma). The per-thread projection rule
  (`contrProjRegel`) ties non-contract steps to the atom lists.

  `VertragAmOrtB` says: at every entry event of `f`, `requires f` holds
  evaluated in the entry world with the actual `rho`; at every return event,
  `ensures f` holds evaluated in the return world with the actual `v` and
  the actual `rho` (entry-read world as the `old` side).

  Non-vacuity: a one-function declaration over `.int 0 5` with
  `ensures := (ret == param + 1)` gives a one-step wrapper run where
  `VertragAmOrtB` holds (param 2, result 3) while `QEnsuresB` for the same
  contract is false (result 0 witnesses the failure).

  Bridge: a return event whose world satisfies `ensures` for the actual `v`
  is exactly the case where `rufAt` does NOT produce `Logik.nachbedingung f`
  for that call (`rueck_ohne_nachbedingung`). Both directions are proved
  from the `rufAt` equation; the entry `requires` side is a premise shared
  with the sequential semantics, not re-derived.

  Memory: entry worlds (`vor`) come from `World.lese`; return worlds (`nach`)
  are either the entry world (reads only) or the `execEnd` outcome world,
  which CAN change memory. No trace event carries a value.
-/
import Grammatik.Semantik
import Grammatik.Wettlauf

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Extended atoms and call events with the actual values -/

/-- Call/return atom kinds extending the PC model: the same leaf/take/rel as
    `PCAtom` (Maschine.lean), plus entry and return positions. A separate type
    (not reusing `PCAtom`) because this file cannot import Maschine.lean. -/
inductive ContrAtom (D : Deklaration) where
  | leaf (Λ : List (Res D)) (cs : List (D.Tab ⊕ D.Glob))
  | take (L : D.Lock)
  | rel (L : D.Lock)
  | eintritt (f : D.Fn)
  | rueck (f : D.Fn)

/-- The old cases embed: a plain PC position is a contract position. -/
def contrAtomVonPC : ContrAtom D → ContrAtom D := id

/-- Call/return events carrying the ACTUAL values: entry carries the actual
    parameter environment `rho`; return carries the actual `rho`, the actual
    result `v`, and the entry-side read world `s0` (the `old(..)` side of
    `ensures`). -/
inductive ContrEvent (D : Deklaration) where
  | eintritt (f : D.Fn) (rho : Env D (D.params f))
  | rueck (f : D.Fn) (rho : Env D (D.params f))
      (v : ErgVal D (D.erg f)) (s0 : World D)

/-- One wrapper step: the acting thread, its pre/post worlds, and the optional
    contract event emitted at that position. -/
structure ContrSchritt (D : Deklaration) where
  faden : Faden
  vor : World D
  nachW : World D
  ev : Option (ContrEvent D)

/-- A wrapper run over per-thread atom lists plus contract-event steps. -/
structure ContrLauf (D : Deklaration) where
  prog : Faden → List (ContrAtom D)
  schritte : List (ContrSchritt D)

/-- Projection rule: a step with NO contract event fires a non-contract atom
    of its thread. Entry/return positions always carry their event. -/
def contrProjRegel (L : ContrLauf D) : Prop :=
  ∀ c ∈ L.schritte, c.ev = none →
    ∃ a ∈ L.prog c.faden,
      match a with
      | .leaf _ _ => True
      | .take _ => True
      | .rel _ => True
      | .eintritt _ => False
      | .rueck _ => False

/-! ## 2. Contracts at their place -/

/-- Entry check: `requires f` evaluated in the ENTRY world with the actual `rho`. -/
def ReqAmEintritt (P : Programm D) (f : D.Fn) (sigma : World D)
    (rho : Env D (D.params f)) : Prop :=
  wahr? (eval sigma (P.requires f) sigma rho) = true

/-- Return check: `ensures f` evaluated in the RETURN world with the actual `v`
    and the actual `rho`; the entry-side read world `s0` is the `old(..)` side. -/
def EnsAmRueck (P : Programm D) (f : D.Fn) (s0 : World D)
    (sigma : World D) (rho : Env D (D.params f))
    (v : ErgVal D (D.erg f)) : Prop :=
  wahr? (eval s0 (P.ensures f) sigma (ergEnv (D.erg f) v rho)) = true

/-- `QEnsures` restated locally (same shape as Extraktion.QEnsures, which this
    file cannot import): every return value, every parameter environment. -/
def QEnsuresB (P : Programm D) (f : D.Fn) : World D → Prop :=
  fun σ => ∀ (v : ErgVal D (D.erg f)) (ρ : Env D (D.params f)),
    wahr? (eval σ (P.ensures f) σ (ergEnv (D.erg f) v ρ)) = true

/-- `VertragAmOrtB`: in a wrapper run, at every call entry the
    `requires` holds in the entry world with the actual `rho`, and at every
    return the `ensures` holds in the return world with the actual `v`
    and the actual `rho`. Entry worlds are the step's `vor`, return worlds
    the step's `nach`. Stated per-event (no outer `∀ f`), so the proof never
    case-splits on the function id. -/
def VertragAmOrtB (P : Programm D) (L : ContrLauf D) : Prop :=
  ∀ c ∈ L.schritte,
    (∀ f : D.Fn, ∀ rho : Env D (D.params f), c.ev = some (ContrEvent.eintritt f rho) →
      ReqAmEintritt P f c.vor rho) ∧
    (∀ f : D.Fn, ∀ rho : Env D (D.params f), ∀ v : ErgVal D (D.erg f),
      ∀ s0 : World D, c.ev = some (ContrEvent.rueck f rho v s0) →
        EnsAmRueck P f s0 c.nachW rho v)

/-- The empty wrapper run satisfies the contract trivially. -/
theorem vertragAmOrtB_leer (P : Programm D) (L : ContrLauf D)
    (hempty : L.schritte = []) : VertragAmOrtB P L := by
  intro c hc
  rw [hempty] at hc
  simp at hc

/-- A place-check implies the quantified check at the SAME values: the link
    between `EnsAmRueck` and `QEnsuresB` when entry and return worlds agree.
    Used by the bridge lemma to discharge the ensures branch. -/
theorem ensAmRueck_gibt_qensures_pkt (P : Programm D) (f : D.Fn)
    (s0 : World D) (sigma : World D) (rho : Env D (D.params f))
    (v : ErgVal D (D.erg f))
    (h : EnsAmRueck P f s0 sigma rho v) (hs : s0 = sigma)
    (w : QEnsuresB P f sigma) :
    wahr? (eval sigma (P.ensures f) sigma (ergEnv (D.erg f) v rho)) = true := by
  have hv := w v rho
  have he : eval s0 (P.ensures f) sigma (ergEnv (D.erg f) v rho) =
      eval sigma (P.ensures f) sigma (ergEnv (D.erg f) v rho) := by
    rw [hs]
  rw [← he]
  exact h

/-! ## 3. Non-vacuity: a tiny declaration where the place-contract holds
    and the quantified `ensures` is false -/

/-- One-function signature over `.int 0 5`: one parameter, one int result. -/
def miniContrSig : Signatur Unit Empty Empty Empty where
  params := [.int 0 5]
  erg := some (.int 0 5)
  gruende := 0
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- The declaration: no tables, no globals, two function ids (`Bool`,
    like Extraktion `miniD`); `true` is the contract function. -/
def miniContrD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 1
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .bool
  erlaubt := fun _ _ _ _ => false
  tabNr := fun _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun _ => false
  ggeteilt := fun e => nomatch e
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => []
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := Bool
  sig := fun | true => 0 | false => 1
  sigNr := fun _ => miniContrSig
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Empty
  aparams := fun e => nomatch e
  aerg := fun e => nomatch e
  aschreibt := fun e => nomatch e
  agschreibt := fun e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t h => by simp at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e
  geist := fun _ => false
  ggeist := fun e => nomatch e

/-- The witness function id. -/
def fTrue : miniContrD.Fn := show miniContrD.Fn from true

/-- The `erg` of the single function, by computation (case on the id). -/
theorem miniContrD_erg (f : miniContrD.Fn) :
    miniContrD.erg f = some (.int 0 5) := by
  cases f with
  | true => rfl
  | false => rfl

/-- The `params` of the single function, by computation (case on the id). -/
theorem miniContrD_params (f : miniContrD.Fn) :
    miniContrD.params f = [.int 0 5] := by
  cases f with
  | true => rfl
  | false => rfl

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
  .eq (.var .hier)
    ((.weiter (by decide) (by decide) (.lit 2) :
      Expr miniContrD (miniContrD.params fTrue) [] (.int 0 5)))

/-- `ensures`: the result equals the parameter plus one.
    Context `[.int 0 5, .int 0 5]`: result at `.hier`, parameter at `.dort .hier`. -/
def miniEnsLit : Expr miniContrD [.int 0 5, .int 0 5] [] .bool :=
  .eq (.weiter (by decide) (by decide) (.var .hier) :
      Expr miniContrD [.int 0 5, .int 0 5] [] (.int 0 6))
    (.weiter (by decide) (by decide)
      (.add (.var (.dort .hier))
        (.weiter (by decide) (by decide) (.lit 1) :
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
    | true => .ret (.wert (.var .hier)) (List.Perm.refl [])
    | false => .ret (.wert (.var .hier)) (List.Perm.refl [])

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
  exact absurd hcon (by cases he <;> simp)

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
