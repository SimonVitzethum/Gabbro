/-
  File:      Grammatik/X86/CostSummary.lean
  Subject:   CHECKED COST-SUMMARY SCHEMA (lane 347, organisation plan C3).

  Reviewed direction: cost-summary schema (`kostenSummeOk` Bool,
  `expandBound`, `targetWork` skeleton, per-site attempt bounds, waiting
  exclusions needing exact source correspondence); `budget_simulation`
  stated OPEN, never derived by re-summing. Closes FLOAT-ZEIT §8.1
  framework. Reviewer: lane 385.

  Dependencies (reused, not redefined): `Budget.lean` (`Op.cost`,
  `totalCost`), `KostenG` (`kostenTiefF`), canonical `X86.Typen`
  (`Befehl`, `Register`), the `eD`/`eP` fixture for the joint witness.

  Policy: source steps, machine work and cycles are never conflated.
  Profile: ESSENTIAL schema; cycle bounds DEFERRED (no cycle claim here).
-/
import Grammatik.Budget
import Grammatik.KostenG
import Grammatik.X86.Typen
import Grammatik.ZielOrtEinfadenZeuge

namespace Gabbro.Grammatik.X86

/-- Source step classes the backend summary prices, one per class. -/
inductive StepClass where
  | leaf | branch | lockOp | callOp | traverse | retryTry
  | foreverPass | floatOp | fenceOp | spillOp | casAttempt
  deriving DecidableEq, Repr

/-- Every priced class, for the uniform maximum. -/
def alleKlassen : List StepClass :=
  [.leaf, .branch, .lockOp, .callOp, .traverse, .retryTry,
   .foreverPass, .floatOp, .fenceOp, .spillOp, .casAttempt]

/-- Skeleton machine-work count: retired target instructions of a segment.
    Spill/fence forms are not in the pilot `Befehl`; their counts live in
    the summary (`spillCount`/`fenceCount`), never hidden here. -/
def targetWork (xs : List Befehl) : Nat := xs.length

/-- Waiting kinds the summary may exclude from `targetWork`. A CAS-spin
    loop has NO source-level non-firing counterpart, so it is never
    excludable (refused by `kostenSummeOk`). -/
inductive WaitKind where
  | lockWait | awaitWait | casSpin
  deriving DecidableEq, Repr

/-- One waiting exclusion: machine waiting excluded from `targetWork`
    ONLY with exact source correspondence, proved per site in the
    certificate and carried here as checked data. -/
structure Exclusion where
  kind : WaitKind
  sourceCorresponds : Bool
  deriving DecidableEq, Repr

/-- The backend-emitted cost summary: per-class maxima of validated
    target instructions per source step, the spill/fence counts actually
    used, the per-site retry attempt bound (`none` = unbounded, claims
    no work bound for `retryTry`), and the waiting exclusions. -/
structure CostSummary where
  expand : StepClass → Option Nat
  spillCount : Nat
  fenceCount : Nat
  retryBound : Option Nat
  exclusions : List Exclusion

/-- Validator admission Bool (profile admission, not a hardware fault):
    an unbounded retry site behind a constant bound is refused, an
    exclusion without source correspondence is refused, and a CAS-spin
    exclusion is refused unconditionally. -/
def kostenSummeOk (s : CostSummary) : Bool :=
  retryOk s && exclOk s
where
  retryOk (s : CostSummary) : Bool :=
    match s.retryBound with
    | none => s.expand .retryTry == none
    | some _ => true
  exclOk (s : CostSummary) : Bool :=
    s.exclusions.all (fun e => e.sourceCorresponds) &&
      !(s.exclusions.any (fun e => e.kind == .casSpin))

/-- Uniform maximum over the priced classes: `none` if any class claims
    no bound. Future ISA forms extend `alleKlassen`, never a second
    maximum beside this one. -/
def alleMaxAux : List StepClass → CostSummary → Option Nat
  | [], _ => some 0
  | c :: cs, s =>
    match s.expand c with
    | none => none
    | some b =>
      match alleMaxAux cs s with
      | none => none
      | some m => some (Nat.max b m)

/-- The uniform per-step maximum of a summary. -/
def alleMax (s : CostSummary) : Option Nat := alleMaxAux alleKlassen s

/-- Expansion bound: the summary bounds lowered MACHINE work via the
    validated expansion over the source budget `src` (a `kostenTiefF`
    value at the use site), not source steps by re-summing. `none`
    while any class is unbounded. Spill/fence counts are added in full:
    no wait is hidden, no cost excluded. -/
def expandBound (s : CostSummary) (src : Nat) : Option Nat :=
  match alleMax s with
  | none => none
  | some m => some (src * m + s.spillCount + s.fenceCount)

/-- Declared-op reading of one class maximum: each expanded target
    instruction accounts one declared `Op` (premise P1 style of
    `Budget.lean`), tying the schema to `totalCost`. -/
def klassenKosten (s : CostSummary) (c : StepClass) : List Op :=
  List.replicate ((s.expand c).getD 0) ⟨1⟩

/-- One declared op per expanded instruction sums to the count. -/
theorem totalCost_replicate_one (n : Nat) :
    totalCost (List.replicate n (Op.mk 1)) = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ, totalCost_cons] at *
    omega

/-- The declared-op reading of a class maximum totals to that maximum. -/
theorem klassenKosten_total (s : CostSummary) (c : StepClass) :
    totalCost (klassenKosten s c) = (s.expand c).getD 0 := by
  unfold klassenKosten
  exact totalCost_replicate_one _

/-- Machine work adds over concatenated segments. -/
theorem targetWork_add (l1 l2 : List Befehl) :
    targetWork (l1 ++ l2) = targetWork l1 + targetWork l2 := by
  unfold targetWork
  exact List.length_append

/-- REFUSAL 1: an unbounded-retry site behind a constant bound is refused:
    with no proved attempt bound, no finite work bound may be claimed for
    `retryTry` (a CAS retry is unbounded; `keinKernHalt`-style waiting
    needs named assumptions, never a constant). -/
theorem kostenSummeOk_verweigert_unbegrenzt (s : CostSummary) (k : Nat)
    (hRetry : s.retryBound = none)
    (hExpand : s.expand .retryTry = some k) :
    kostenSummeOk s = false := by
  unfold kostenSummeOk kostenSummeOk.retryOk kostenSummeOk.exclOk
  rw [hRetry, hExpand]
  simp

/-- REFUSAL 2: a waiting exclusion without exact source correspondence is
    refused: machine waiting counts as excluded ONLY where it corresponds
    exactly to source-level non-firing. -/
theorem kostenSummeOk_verweigert_ohneQuelle (s : CostSummary) (e : Exclusion)
    (hm : e ∈ s.exclusions)
    (hq : e.sourceCorresponds = false) :
    kostenSummeOk s = false := by
  have hAll : s.exclusions.all (fun e => e.sourceCorresponds) = false := by
    apply eq_false_of_ne_true
    intro h
    rw [List.all_eq_true] at h
    have htrue := h e hm
    rw [hq] at htrue
    exact Bool.false_ne_true htrue
  unfold kostenSummeOk kostenSummeOk.exclOk
  rw [hAll]
  simp

/-- REFUSAL 3: a CAS-spin exclusion is refused unconditionally: a
    lowering-introduced spin has NO source counterpart, so every attempt
    counts in full (hence the attempt bound, never an exclusion). -/
theorem kostenSummeOk_verweigert_spin (s : CostSummary) (e : Exclusion)
    (hm : e ∈ s.exclusions)
    (hSpin : e.kind = .casSpin) :
    kostenSummeOk s = false := by
  have hAny : s.exclusions.any (fun e => e.kind == .casSpin) = true := by
    rw [List.any_eq_true]
    exact ⟨e, hm, by simp [hSpin]⟩
  unfold kostenSummeOk kostenSummeOk.exclOk
  rw [hAny]
  simp

/-- A fully bounded class list has a uniform maximum. -/
theorem alleMaxAux_gilt (s : CostSummary) (cs : List StepClass)
    (h : ∀ c ∈ cs, (s.expand c).isSome = true) :
    ∃ m, alleMaxAux cs s = some m := by
  induction cs with
  | nil => exact ⟨0, rfl⟩
  | cons hd tl ih =>
    have hhd : (s.expand hd).isSome = true :=
      h hd (List.mem_cons.mpr (Or.inl rfl))
    have htl : ∀ c ∈ tl, (s.expand c).isSome = true :=
      fun c hm => h c (List.mem_cons.mpr (Or.inr hm))
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hhd
    obtain ⟨m, hm⟩ := ih htl
    rw [alleMaxAux, hb, hm]
    exact ⟨_, rfl⟩

/-- A summary bounded at every class has a uniform maximum. -/
theorem alleMax_gilt (s : CostSummary)
    (h : ∀ c, (s.expand c).isSome = true) :
    ∃ m, alleMax s = some m := by
  unfold alleMax
  apply alleMaxAux_gilt
  intro c _
  exact h c

/-- A fully bounded summary yields a machine-work bound over ANY source
    budget `src` -- in particular over a `kostenTiefF` value. Admission
    (`kostenSummeOk`) gates USE of the bound in the soundness schema
    (OPEN below); existence needs boundedness alone. This is a work bound
    only: relating it to source-budget exhaustion (`budget_simulation`)
    is the separate OPEN obligation below. -/
theorem expandBound_gilt (s : CostSummary) (src : Nat)
    (hAlle : ∀ c, (s.expand c).isSome = true) :
    ∃ k, expandBound s src = some k := by
  obtain ⟨m, hm⟩ := alleMax_gilt s hAlle
  unfold expandBound
  rw [hm]
  exact ⟨_, rfl⟩

/-- The expansion keeps every counted cost: spill and fence counts are
    added in full beside the scaled maximum -- no wait hidden, no cost
    forged away. -/
theorem expandBound_keinVerlust (s : CostSummary) (src m : Nat)
    (h : alleMax s = some m) :
    expandBound s src = some (src * m + s.spillCount + s.fenceCount) := by
  unfold expandBound
  rw [h]

/-! ## OPEN: budget simulation (FLOAT-ZEIT §8.1).

    Relating machine work to the model's `passes`-budget consumption --
    so that budget exhaustion on the machine simulates the source
    `budget` stop -- is a SEPARATE open obligation. Re-summing the
    expansion over `kostenTiefF` proves a work bound, never a
    runtime/stop claim: the machine has no `passes` counter. The schema
    below states the obligation shape over an admitted summary; no
    theorem here inhabits it, and none is derived from `expandBound`. -/

/-- OPEN obligation schema: for an admitted summary, the machine-work
    count of a corresponding segment within source budget `src` is
    covered by the expansion -- pending the refinement relation
    instance (decoder + per-access bridge + layout, owned by the
    decoder/bridge lanes). STATED, never derived by re-summing. -/
def budgetSimulationOffen (s : CostSummary) (src : Nat)
    (xseg : List Befehl) : Prop :=
  kostenSummeOk s = true ∧
    ∃ k, expandBound s src = some k ∧ targetWork xseg ≤ k

/-! ## Counted expansion of one source step class.

    The `leaf` class: the `konto[0] := 5` write of `eSetze` expands to at
    most 3 validated target instructions (materialise, move, store), with
    honest spill/fence counts of zero -- the counted expansion below uses
    no spill slot and no fence form. Any future spill/fence form adds to
    these counts, never hides behind them. -/

/-- Concrete admitted summary for the leaf class. -/
def blattSummary : CostSummary where
  expand
    | .leaf => some 3
    | .retryTry => some 5
    | _ => some 2
  spillCount := 0
  fenceCount := 0
  retryBound := some 4
  exclusions := []

/-- Counted expansion of one `leaf` source step: 3 retired instructions. -/
def blattExpansion : List Befehl :=
  [.movImm64 .rax 5, .movReg64 .rcx .rax, .store64 .rdi .rcx 0]

/-- The concrete summary is admitted by the validator Bool. -/
theorem blattSummary_ok : kostenSummeOk blattSummary = true := by
  decide

/-- The concrete summary bounds every class. -/
theorem blattSummary_beschraenkt (c : StepClass) :
    (blattSummary.expand c).isSome = true := by
  cases c <;> rfl

/-- The counted expansion retires exactly 3 instructions. -/
theorem blattExpansion_zaehlt : targetWork blattExpansion = 3 := rfl

/-- The counted expansion fits its class maximum. -/
theorem blattExpansion_imRahmen :
    targetWork blattExpansion ≤ (blattSummary.expand .leaf).getD 0 := by
  decide

/-- The declared-op reading of the leaf maximum totals to 3. -/
theorem blattKosten_drei :
    totalCost (klassenKosten blattSummary .leaf) = 3 := by
  have h := klassenKosten_total blattSummary .leaf
  simp only [blattSummary] at h
  exact h

/-- The concrete summary over unit source budget bounds work by 5
    (uniform maximum 5 at `retryTry`, no spill/fence to add). -/
theorem blattSummary_schranke : expandBound blattSummary 1 = some 5 := by
  decide

/-! ## Joint witness on a non-degenerate source program.

    The fixture program `eP` writes table `konto` (`eSetze`, proved by
    `rfl` below); the reached run carries the entry world with slot `5`
    against a start of `0` -- a real memory-changing run, not an empty
    one. Jointly with it: the admitted summary, the counted 3-instruction
    leaf expansion inside its class maximum, and a machine-work bound
    over the canonical source budget `kostenTiefF`. -/

/-- JOINT WITNESS: counted leaf expansion with honest spill/fence counts
    on a memory-changing reached run of a table-writing program. -/
theorem kostenExpansion_zeuge :
    ∃ (M : RufMaschineG eD) (rho : Env eD (eD.params ePruefe))
      (w0 : World eD),
    RufErreichbarG eP eO 0 (RufStartG eP eSp eInit) M ∧
    (eSp.slots () 0 ()).n = 0 ∧
    (eD.signatur eSetze).schreibt () = true ∧
    RufEreignisF.eintritt ePruefe rho w0 ∈ (M.faeden 0).log ∧
    ReqAmEintritt eP ePruefe w0 rho ∧
    (w0.slots () 0 ()).n = 5 ∧
    kostenSummeOk blattSummary = true ∧
    targetWork blattExpansion = 3 ∧
    targetWork blattExpansion ≤ (blattSummary.expand .leaf).getD 0 ∧
    ∃ k, expandBound blattSummary
      (kostenTiefF eP (fun a : eD.Ax => nomatch a) 0 1 eSetze) = some k := by
  obtain ⟨M, hr, h0, rho, w0, hm, hreq, h5⟩ := ziel_ort_einfaden_zeuge
  exact ⟨M, rho, w0, hr, h0, rfl, hm, hreq, h5,
    blattSummary_ok, blattExpansion_zaehlt, blattExpansion_imRahmen,
    expandBound_gilt _ _ blattSummary_beschraenkt⟩

/- CUTS:
   - No refinement relation instance: `XCorr` (decoder + per-access
     bridge + layout) is owned by the decoder/bridge lanes and OPEN
     here; `budgetSimulationOffen` is STATED over admitted summaries
     and never derived by re-summing `expandBound`.
   - No per-form maxima proofs: `expand` values are backend-declared
     maxima checked by the `kostenSummeOk` Bool, not proved
     correspondences; the counted `blattExpansion` exhibits one class
     maximum, it does not lower the source step.
   - No per-site exclusion proofs: `sourceCorresponds` is carried data;
     the validator refuses `false` and `casSpin` (proved above), the
     positive correspondence per site is phase-B work.
   - No cycle bounds: `targetWork` counts retired instructions;
     hardware timing needs named assumptions plus the proved work
     transfer (FLOAT-ZEIT §8.2), DEFERRED here.
   - No new `Befehl` evaluation: the one target semantics
     (`Ausfuehrung.schritt` over the 14 pilot forms) is reused untouched;
     future ISA forms extend `alleKlassen` and the pilot `Befehl`, never
     a duplicated evaluator in this file.
   - No checker change: no source admission is tightened to ease proof;
     everything is over the real source budget (`kostenTiefF`) and the
     real target vocabulary (`Befehl`).
-/

#print axioms totalCost_replicate_one
#print axioms klassenKosten_total
#print axioms targetWork_add
#print axioms kostenSummeOk_verweigert_unbegrenzt
#print axioms kostenSummeOk_verweigert_ohneQuelle
#print axioms kostenSummeOk_verweigert_spin
#print axioms alleMaxAux_gilt
#print axioms alleMax_gilt
#print axioms expandBound_gilt
#print axioms expandBound_keinVerlust
#print axioms blattSummary_ok
#print axioms blattSummary_beschraenkt
#print axioms blattExpansion_zaehlt
#print axioms blattExpansion_imRahmen
#print axioms blattKosten_drei
#print axioms blattSummary_schranke
#print axioms kostenExpansion_zeuge

end Gabbro.Grammatik.X86
