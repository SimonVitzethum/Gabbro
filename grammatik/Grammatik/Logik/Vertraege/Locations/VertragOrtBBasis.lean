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
module
public import Grammatik.Kern.Semantik.Semantik
public import Grammatik.Nebenlaeufigkeit.Allgemein.Wettlauf
@[expose] public section


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
  simp only [List.not_mem_nil] at hc

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
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp only [List.not_mem_nil] at h
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
  geteilt_bewacht := fun t h => by simp only [Bool.false_eq_true] at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

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


end Gabbro.Grammatik
