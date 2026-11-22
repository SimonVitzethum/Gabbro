module

public import Stage0.Senke.Bild.EmittedZiel
public import Grammatik.Zielsatz.Atomar.BeweisAtomar.Fremd
public import Grammatik.Speichermodell.Adressen.Bereich
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Stage0.Senke

variable {src : String} {K : Nat} {options : Profil.Options}

/-- The unit judged for an image with explicit concurrent roots. Its
    initial world, entry arguments and ordered root arguments are the
    ones serialized by the production emitter. -/
def Emitted.goalUnit (output : Emitted src K options) (Q : AxEns (declOf output.compiled.unit)) :
    Einheit (declOf output.compiled.unit) :=
  OldSource.einheitDer output.compiled.unit output.compiled.program Q output.sp0
    output.compiled.main output.args output.starts [] output.compiled.checkedDeclarations.val

theorem Emitted.goalUnit_starts (output : Emitted src K options)
    (Q : AxEns (declOf output.compiled.unit)) :
    (output.goalUnit Q).starts = ⟨output.compiled.main, output.args⟩ :: output.starts := rfl

private theorem Emitted.goal_invariants_with_sources (output : Emitted src K options)
    (Q : AxEns (declOf output.compiled.unit)) (sources : Option (Vertraege.Pruefer.AxiomSources Q)) :
    let E := { output.goalUnit Q with axiomSources := sources }
    invariantenGeprueftB E output.fsA.1 output.lsA.1 = true := by
  intro E
  have checked : CheckedInitialInvariants E output.lsA.1 := by
    have initial := output.initialInvariants
    unfold CheckedInitialInvariants at initial ⊢
    refine ⟨initial.1, ?_⟩
    simpa only [E, initialUnit, Emitted.goalUnit, OldSource.einheitDer, OldSource.einheitVon,
      Emitted.lsA, Emitted.sp0] using initial.2
  apply checked.goal_verdict
  have accepted := OldSource.accepts_program _ _ _ output.compiled.accepted
    output.compiled.checkedDeclarations.property
  simp only [AkzeptiertX, Invarianten.Pruefer.invariantVCB, Bool.and_eq_true] at accepted
  exact accepted.2.1

/-- The invariant branch of the model's unit verdict follows from the
    compiler's writer check and the emitter's check on the serialized memory. -/
theorem Emitted.goal_invariants (output : Emitted src K options)
    (Q : AxEns (declOf output.compiled.unit)) :
    invariantenGeprueftB (output.goalUnit Q) output.fsA.1 output.lsA.1 = true :=
  output.goal_invariants_with_sources Q (output.goalUnit Q).axiomSources

/-- With an empty axiom family, the compiler supplies both branches of the
    goal checker's verdict on the declared initial state. -/
theorem Emitted.goal_axiomFree (output : Emitted src K options)
    (Q : AxEns (declOf output.compiled.unit)) (empty : output.compiled.unit.axs.length = 0) :
    unitStartGeprueftB (output.goalUnit Q) output.fsA.1 output.lsA.1 = true := by
  refine Bool.and_eq_true_iff.mpr ⟨output.goal_invariants Q, ?_⟩
  have only : Q = axWahr (declOf output.compiled.unit) := by
    funext a
    exact False.elim ((Nat.not_lt_zero a.val) (empty ▸ a.isLt))
  subst Q
  exact output.axiomFreeLogic empty

/-- The current unit export omits axiom source expressions for nonempty
    families. For such a unit, the complete goal checker always refuses,
    independently of the proposed summary. -/
theorem Emitted.goalUnit_refuses_nonempty_axioms (output : Emitted src K options)
    (Q : AxEns (declOf output.compiled.unit)) (nonempty : output.compiled.unit.axs.length ≠ 0) :
    akzeptiertX_pruefer.akzeptiert (output.goalUnit Q) output.fsA.1 output.lsA.1 output.csA.1 = false := by
  let E := output.goalUnit Q
  have missing : E.axiomSources = none := by
    change Gabbro.Grammatik.Parser.Cover.Differenz.leereAxQuellen output.compiled.unit Q = none
    simp only [Gabbro.Grammatik.Parser.Cover.Differenz.leereAxQuellen, dite_eq_right nonempty]
  have noLogic : nutzerPflichtGeprueftB E output.fsA.1 output.lsA.1 = false := by
    cases verdict : nutzerPflichtGeprueftB E output.fsA.1 output.lsA.1 with
    | false => rfl
    | true =>
      obtain ⟨certificate, checked⟩ := (nutzerPflichtGeprueftB_iff E output.fsA.1 output.lsA.1 {}).mp verdict
      unfold checkUnitLogic at checked
      split at checked
      · simp only [missing, bind, Except.bind] at checked
        split at checked
        · cases checked
        · split at checked
          · cases checked
          · split at checked <;> cases checked
      · cases checked
  rw [akzeptiertX_pruefer_eq, show nutzerPflichtGeprueftB (output.goalUnit Q) output.fsA.1 output.lsA.1 =
    false from noLogic, Bool.and_false]

/-- The checked foreign-logic result includes the exact source program,
    initial memory and serialized starts. Its logic result and the production
    program gate together give the full model checker's verdict. -/
theorem Emitted.foreign_goal_checker (output : Emitted src K options)
    {checked : output.CheckedForeign}
    (_produced : output.foreignLogic = .ok checked) :
    let E := withForeignSummary (output.goalUnit (axWahr _)) checked.summary
    akzeptiertX_pruefer.akzeptiert E output.fsA.1 output.lsA.1 output.csA.1 = true := by
  let u := output.compiled.unit
  letI : DecidableEq (declOf u).Fn := inferInstanceAs (DecidableEq (Fin u.fns.length))
  letI : DecidableEq (declOf u).Ax := inferInstanceAs (DecidableEq (Fin u.axs.length))
  let E := withForeignSummary (output.goalUnit (axWahr _)) checked.summary
  change akzeptiertX_pruefer.akzeptiert E output.fsA.1 output.lsA.1 output.csA.1 = true
  rw [akzeptiertX_pruefer_eq]
  have roots : E.ws = OldSource.judgedRoots u output.compiled.main :=
    OldSource.einheitDer_ws u output.compiled.main output.args output.starts []
      (output.startPlan.exact_roots _) (OldSource.gestartet_leer _ output.compiled.hostedStarts.noDynamicRoots)
  rw [roots]
  have program := OldSource.accepts_program u _ _ output.compiled.accepted
    output.compiled.checkedDeclarations.property
  have invariant : invariantenGeprueftB E output.fsA.1 output.lsA.1 = true :=
    output.goal_invariants_with_sources checked.summary.predicates (some checked.summary.sources)
  exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
    ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨program, besitzB_leer rfl⟩,
      Kernzelle.akkuStartB_leer E⟩, invariant⟩, checked.verdict⟩

/-- The precise logical start associated with the image. Missing thread
    positions are filled by the model's canonical idle thread. -/
abbrev Emitted.goalStart (output : Emitted src K options)
    (Q : AxEns (declOf output.compiled.unit)) (live : Faden → Bool) :
    FadenMaschine (declOf output.compiled.unit).mitRuhe :=
  FadenStart (output.goalUnit Q).P.mitRuhe (speicherR (output.goalUnit Q).sp0)
    (initRuhe (output.goalUnit Q).starts) live

/-- The logical machine after all declared startup threads have been
    launched. Its live positions are precisely the serialized starts. -/
abbrev Emitted.bootStart (output : Emitted src K options) (Q : AxEns (declOf output.compiled.unit)) :
    FadenMaschine (declOf output.compiled.unit).mitRuhe :=
  output.goalStart Q (fun i => decide (i < (output.goalUnit Q).starts.length))

theorem Emitted.bootStart_live (output : Emitted src K options)
    (Q : AxEns (declOf output.compiled.unit)) (i : Faden) :
    (output.bootStart Q).lebt i = true ↔ i < (output.goalUnit Q).starts.length :=
  Iff.of_eq decide_eq_true_eq

/-- The logical boot state after starting the first `count` roots.
    The entry has rank zero. Each clone adds a rank-one child and
    advances the spawn clock without moving the initial G frames. -/
def Emitted.bootActivation (output : Emitted src K options)
    (Q : AxEns (declOf output.compiled.unit)) (count : Nat) :
    FadenMaschine (declOf output.compiled.unit).mitRuhe :=
  { output.goalStart Q (fun i => decide (i ≤ min count output.starts.length)) with
    rang := fun i => if 0 < i ∧ i ≤ min count output.starts.length then 1 else 0
    uhr := count }

theorem Emitted.bootActivation_step (output : Emitted src K options)
    (Q : AxEns (declOf output.compiled.unit)) (O : Orakel (declOf output.compiled.unit))
    {count : Nat} (declared : count < output.starts.length) :
    FadenSchrittX (output.goalUnit Q).P.mitRuhe O.mitRuhe output.image.passes
      (GeteiltV (D := declOf output.compiled.unit) (output.goalUnit Q).P (output.goalUnit Q).ws)
      (output.bootActivation Q count) (output.bootActivation Q (count + 1)) := by
  have oldBound := Nat.min_eq_left (Nat.le_of_lt declared)
  have newBound := Nat.min_eq_left (Nat.succ_le_of_lt declared)
  have parent : (output.bootActivation Q count).lebt 0 = true := by
    exact decide_eq_true (Nat.zero_le _)
  have child : (output.bootActivation Q count).lebt (count + 1) = false := by
    change decide (count + 1 ≤ min count output.starts.length) = false
    rw [oldBound]
    exact decide_eq_false (Nat.not_succ_le_self _)
  have liveUpdate : (fun i => if i = count + 1 then true else (output.bootActivation Q count).lebt i) =
      (output.bootActivation Q (count + 1)).lebt := by
    funext i
    change (if i = count + 1 then true else decide (i ≤ min count output.starts.length)) =
      decide (i ≤ min (count + 1) output.starts.length)
    rw [oldBound, newBound]
    by_cases here : i = count + 1
    · subst i
      simp only [decide_eq_true (Nat.le_refl _), ite_true]
    · rw [ite_eq_right here]
      have same : (i ≤ count) = (i ≤ count + 1) := propext (by omega)
      simp only [same]
  have rankUpdate : (fun i => if i = count + 1 then (output.bootActivation Q count).rang 0 + 1
      else (output.bootActivation Q count).rang i) = (output.bootActivation Q (count + 1)).rang := by
    funext i
    change (if i = count + 1 then (if 0 < (0 : Nat) ∧ 0 ≤ min count output.starts.length then 1 else 0) + 1
      else if 0 < i ∧ i ≤ min count output.starts.length then 1 else 0) =
      if 0 < i ∧ i ≤ min (count + 1) output.starts.length then 1 else 0
    rw [oldBound, newBound]
    by_cases here : i = count + 1
    · subst i
      simp only [ite_eq_left rfl, Nat.lt_irrefl, false_and, ite_false, Nat.zero_add,
        Nat.succ_pos, Nat.le_refl, and_self, ite_true]
    · rw [ite_eq_right here]
      have same : (0 < i ∧ i ≤ count) = (0 < i ∧ i ≤ count + 1) := propext (by omega)
      simp only [same]
  have stepped := FadenSchrittX.kind
    (P := (output.goalUnit Q).P.mitRuhe) (O := O.mitRuhe) (passes := output.image.passes)
    (Tg := GeteiltV (D := declOf output.compiled.unit) (output.goalUnit Q).P (output.goalUnit Q).ws)
    (output.bootActivation Q count) 0 (count + 1) parent rfl child
  rw [liveUpdate, rankUpdate] at stepped
  exact stepped

/-- Every prefix of the declared startup pool is reachable from the
    single live entry. No undeclared position is needed in the proof. -/
theorem Emitted.bootActivation_reached (output : Emitted src K options)
    (Q : AxEns (declOf output.compiled.unit)) (O : Orakel (declOf output.compiled.unit))
    {count : Nat} (declared : count ≤ output.starts.length) :
    FadenErreichbarX (output.goalUnit Q).P.mitRuhe O.mitRuhe output.image.passes
      (GeteiltV (D := declOf output.compiled.unit) (output.goalUnit Q).P (output.goalUnit Q).ws)
      (output.goalStart Q (fun i => decide (i ≤ 0))) (output.bootActivation Q count) := by
  induction count with
  | zero =>
    have initial : output.bootActivation Q 0 = output.goalStart Q (fun i => decide (i ≤ 0)) := by
      have rank : (fun i : Nat => if 0 < i ∧ i ≤ 0 then 1 else 0) = fun _ => 0 := by
        funext i
        exact ite_eq_right (by omega)
      simp only [Emitted.bootActivation, Emitted.goalStart, FadenStart, Nat.zero_min, rank]
    rw [initial]
    exact .start
  | succ count ih =>
    exact .schritt _ _ (ih (by omega)) (output.bootActivation_step Q O (by omega))

/-- Specialize the original goal theorem to the canonical program, start
    memory, arguments and pass limit of the emitted image. The compiler's
    success supplies structural acceptance. The checked unit verdict
    supplies the user duty, and A4 follows from canonical initialization. -/
theorem Emitted.zielsatz (output : Emitted src K options)
    (Q : AxEns (declOf output.compiled.unit))
    (_certifiable : OldSource.zertifizierbar output.compiled.unit = true)
    (checked : nutzerPflichtGeprueftB (output.goalUnit Q) output.fsA.1 output.lsA.1 = true)
    (callSites : CallSitePflicht (output.goalUnit Q)) (posts : PostDeckt (output.goalUnit Q))
    (O : Orakel (declOf output.compiled.unit)) (binding : ForeignVertrag (output.goalUnit Q) O)
    (hardware : HardwareAnnahmenHw O Q)
    {live : Faden → Bool} {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    (reached : FadenErreichbarX (output.goalUnit Q).P.mitRuhe O.mitRuhe output.image.passes
      (GeteiltV (D := declOf output.compiled.unit) (output.goalUnit Q).P (output.goalUnit Q).ws)
      (output.goalStart Q live) state) :
    let E := output.goalUnit Q
    ZielFX E.P.mitRuhe E.S.mitRuhe O.mitRuhe output.image.passes
      (GeteiltV (D := declOf output.compiled.unit) E.P E.ws)
      (RufStartG E.P.mitRuhe (speicherR E.sp0) (initRuhe E.starts)) (E.arenen.map (·.mitRuhe)) state := by
  have start : unitStartGeprueftB (output.goalUnit Q) output.fsA.1 output.lsA.1 = true :=
    Bool.and_eq_true_iff.mpr ⟨output.goal_invariants Q, checked⟩
  have verdict := output.goal_checker_concurrent Q start
  have duties : NutzerPflichtA (output.goalUnit Q) :=
    nutzerPflicht_of_geprueft output.fsA.2 output.lsA.2 checked
  exact gabbro_ziel akzeptiertX_pruefer _ (output.goalUnit Q) output.fsA output.lsA output.csA
    verdict duties callSites posts O binding hardware output.image.passes _ _
    (laufzeit_initRuhe (output.goalUnit Q)) live state reached

private theorem Emitted.axiomFree_zielsatz_from (output : Emitted src K options)
    (Q : AxEns (declOf output.compiled.unit)) (empty : output.compiled.unit.axs.length = 0)
    (certifiable : OldSource.zertifizierbar output.compiled.unit = true)
    (O : Orakel (declOf output.compiled.unit)) (hardware : HardwareAnnahmenHw O Q)
    {live : Faden → Bool} {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    (reached : FadenErreichbarX (output.goalUnit Q).P.mitRuhe O.mitRuhe output.image.passes
      (GeteiltV (D := declOf output.compiled.unit) (output.goalUnit Q).P (output.goalUnit Q).ws)
      (output.goalStart Q live) state) :
    let E := output.goalUnit Q
    ZielFX E.P.mitRuhe E.S.mitRuhe O.mitRuhe output.image.passes
      (GeteiltV (D := declOf output.compiled.unit) E.P E.ws)
      (RufStartG E.P.mitRuhe (speicherR E.sp0) (initRuhe E.starts)) (E.arenen.map (·.mitRuhe)) state := by
  have absent (a : (declOf output.compiled.unit).Ax) :
      (declOf output.compiled.unit).axHerkunft a ≠ some AxOrigin.software :=
    False.elim ((Nat.not_lt_zero a.val) (empty ▸ a.isLt))
  exact output.zielsatz Q certifiable
    (Bool.and_eq_true_iff.mp (output.goal_axiomFree Q empty)).2
    (callSitePflicht_ohne _ absent) (postDeckt_ohne _ absent) O (foreignVertrag_ohne _ O absent) hardware reached

/-- Axiom-free production images carry the program-logic and start verdict
    into the goal theorem. All foreign obligations have an empty domain. -/
theorem Emitted.zielsatz_axiomFree (output : Emitted src K options)
    (Q : AxEns (declOf output.compiled.unit)) (empty : output.compiled.unit.axs.length = 0)
    (certifiable : OldSource.zertifizierbar output.compiled.unit = true)
    (O : Orakel (declOf output.compiled.unit)) (hardware : HardwareAnnahmenHw O Q)
    {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    (reached : FadenErreichbarX (output.goalUnit Q).P.mitRuhe O.mitRuhe output.image.passes
      (GeteiltV (D := declOf output.compiled.unit) (output.goalUnit Q).P (output.goalUnit Q).ws)
      (output.bootStart Q) state) :
    let E := output.goalUnit Q
    ZielFX E.P.mitRuhe E.S.mitRuhe O.mitRuhe output.image.passes
      (GeteiltV (D := declOf output.compiled.unit) E.P E.ws)
      (RufStartG E.P.mitRuhe (speicherR E.sp0) (initRuhe E.starts)) (E.arenen.map (·.mitRuhe)) state :=
  output.axiomFree_zielsatz_from Q empty certifiable O hardware reached

/-- The goal holds while the declared roots are activated in order, from
    the single live entry, including their actual spawn clock and ranks. -/
theorem Emitted.bootActivation_zielsatz (output : Emitted src K options)
    (Q : AxEns (declOf output.compiled.unit)) (empty : output.compiled.unit.axs.length = 0)
    (certifiable : OldSource.zertifizierbar output.compiled.unit = true)
    (O : Orakel (declOf output.compiled.unit)) (hardware : HardwareAnnahmenHw O Q)
    {count : Nat} (declared : count ≤ output.starts.length) :
    let E := output.goalUnit Q
    ZielFX E.P.mitRuhe E.S.mitRuhe O.mitRuhe output.image.passes
      (GeteiltV (D := declOf output.compiled.unit) E.P E.ws)
      (RufStartG E.P.mitRuhe (speicherR E.sp0) (initRuhe E.starts)) (E.arenen.map (·.mitRuhe))
      (output.bootActivation Q count) :=
  output.axiomFree_zielsatz_from Q empty certifiable O hardware (output.bootActivation_reached Q O declared)

/-- Successful CLI payload production identifies the exact certified
    output, also under the automatic stack-reserve policy. -/
theorem irBild_eq_output {output : Emitted src K options} {bytes : List Runner.B}
    (built : emit src K options = .ok output) (payload : irBild src K options = .ok bytes) :
    output.bytes = bytes := by
  rw [irBild, built] at payload
  exact Except.ok.inj payload

/-- The image's entry and every serialized root occupy the same ordered
    positions in the canonical logical start, even for duplicate functions. -/
theorem Emitted.goalStart_argument (output : Emitted src K options)
    (Q : AxEns (declOf output.compiled.unit)) (i : Faden)
    (start : Σ f : (declOf output.compiled.unit).Fn,
      Env (declOf output.compiled.unit) ((declOf output.compiled.unit).params f))
    (atPosition : (⟨output.compiled.main, output.args⟩ :: output.starts)[i]? = some start) :
    initRuhe (output.goalUnit Q).starts i = ⟨some start.1, envR start.2⟩ := by
  simp only [initRuhe, output.goalUnit_starts, atPosition]

/-- A live boot position starts with the G frame of its exact declared
    root and arguments, in the same memory as every other boot position. -/
theorem Emitted.bootStart_frame (output : Emitted src K options)
    (Q : AxEns (declOf output.compiled.unit)) (i : Faden)
    (start : Σ f : (declOf output.compiled.unit).Fn,
      Env (declOf output.compiled.unit) ((declOf output.compiled.unit).params f))
    (atPosition : (⟨output.compiled.main, output.args⟩ :: output.starts)[i]? = some start) :
    (output.bootStart Q).lebt i = true ∧ (output.bootStart Q).wartet i = [] ∧
      (output.bootStart Q).m.faeden i =
        (RufStartG (output.goalUnit Q).P.mitRuhe (speicherR (output.goalUnit Q).sp0)
          (fun _ => ⟨some start.1, envR start.2⟩)).faeden i := by
  have inside := (List.getElem?_eq_some_iff.mp atPosition).1
  have live := (output.bootStart_live Q i).mpr (by rw [output.goalUnit_starts Q]; exact inside)
  refine ⟨live, rfl, ?_⟩
  let frame (entry : Σ f : (declOf output.compiled.unit).mitRuhe.Fn,
      Env (declOf output.compiled.unit).mitRuhe ((declOf output.compiled.unit).mitRuhe.params f)) :=
    (RufStartG (output.goalUnit Q).P.mitRuhe (speicherR (output.goalUnit Q).sp0) (fun _ => entry)).faeden i
  change frame (initRuhe (output.goalUnit Q).starts i) = frame ⟨some start.1, envR start.2⟩
  exact congrArg frame (output.goalStart_argument Q i start atPosition)

/-- The concrete builder bounds every typed cell and separates its bytes
    from other cells. This is a property of the relocated image's layout. -/
theorem Emitted.layout_checked (output : Emitted src K options) :
    LayIn output.image.Y ∧ LayDis output.image.Y ∧ LaySync output.image.Y := by
  obtain ⟨_, _, _, layout, _⟩ :=
    bild_lage output.emission output.funktionen_voll
      (fun base bound => layU_in output.compiled.unit output.tor base bound)
      (fun base => layU_dis output.compiled.unit output.tor base)
      (fun base => by simp only [layU]; omega)
      (fun base => layU_sync output.compiled.unit output.tor base)
  exact ⟨layout.hlay, layout.hdis, layout.hsync⟩

/-- Each relocated function address fetches the exact output of lowering
    that function in the emitted program and fits in a signed IR immediate. -/
theorem Emitted.relocated_function_code [Runner.IR.Kern] (output : Emitted src K options) {memory : Runner.Mem}
    (loaded : BytesAt memory codeBase (output.image.code.flatMap encII))
    (fn : (declOf output.compiled.unit).Fn) :
    ∃ code top, lowFun output.image.passes output.compiled.program output.image.A output.image.Y fn =
      some (code, top) ∧
      Runner.IR.CodeAt memory (BitVec.ofNat 64 (output.image.A fn)) code ∧
      output.image.A fn + 16 * code.length ≤ output.image.fp0 ∧ output.image.A fn < 2 ^ 31 := by
  obtain ⟨functions, body, spawnSites, layout, serialized, _, _, _⟩ :=
    bild_lage output.emission output.funktionen_voll
      (fun base bound => layU_in output.compiled.unit output.tor base bound)
      (fun base => layU_dis output.compiled.unit output.tor base)
      (fun base => by simp only [layU]; omega)
      (fun base => layU_sync output.compiled.unit output.tor base)
  let header := spawnC (startScratch output.compiled.main) spawnSites ++
    startC output.image.A output.compiled.main output.image.depth 231 true ++
    rootsC output.image.A output.image.depth (output.starts.map (·.1))
  have exactBytes : BytesAt memory codeBase ((header ++ body).flatMap encII) :=
    serialized ▸ loaded
  obtain ⟨lowered, addresses, _⟩ := bild_code (C := fun g => ((functions[g.val]?).map (·.1)).getD [])
    (fun _ => rfl) layout.hbody (by rw [show header.length = _ from layout.head]; exact layout.hfp)
    (by rw [show header.length = _ from layout.head]; exact layout.haddr)
    layout.hlen layout.hlow layout.hpos layout.hops exactBytes
  obtain ⟨top, produced, _⟩ := lowered fn
  obtain ⟨code, extent⟩ := addresses fn
  have fits := layout.hfit
  exact ⟨_, top, produced, code, extent, by omega⟩

/-- Physical base of the table's complete, consecutive columns. -/
def InitialLayout.tableBase {u : UProg} (L : Lay (declOf u)) (t : (declOf u).Tab) : Nat :=
  L.lo + globEnd (List.finRange u.globs.length) 0 (globSz u) (fun g => wordAlign (globAlign u g)) +
    (((List.finRange u.tabs.length).map (tabSz u)).take t.val).sum

/-- Every byte of a represented cell is in its actual table, accounting
    for the field's own stride and for all preceding columns. -/
theorem InitialLayout.cell_in_table {u : UProg} {L : Lay (declOf u)} (layout : InitialLayout u L)
    (t : (declOf u).Tab) (f : (declOf u).Feld t) (index : Nat)
    (bounded : (index : Int) < L.count t) :
    InitialLayout.tableBase L t ≤ L.elem t f index ∧
      L.elem t f index + 8 * valueWords ((declOf u).typ t f) ≤ InitialLayout.tableBase L t + tabSz u t := by
  have own := colSz_ge u t f index ((layout.count t) ▸ bounded)
  have column := take_sum_add ((List.finRange (fieldCount u t)).map (colSz u t)) f.val
    (by simpa only [List.length_map, List.length_finRange] using f.isLt)
  simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk] at column
  change (((List.finRange (fieldCount u t)).map (colSz u t)).take f.val).sum +
    colSz u t f ≤ tabSz u t at column
  rw [Lay.elem, layout.columns]
  unfold InitialLayout.tableBase
  omega

/-- The extent leg on the actual column layout. On a closed table,
    reachability supplies the physical index bound on its own. -/
theorem Emitted.changedCell_in_image (output : Emitted src K options)
    (Q : AxEns (declOf output.compiled.unit)) (O : Orakel (declOf output.compiled.unit))
    (foreignConfined : ImBereichO O.mitRuhe)
    {live : Faden → Bool} {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    (reached : FadenErreichbarX (output.goalUnit Q).P.mitRuhe O.mitRuhe output.image.passes
      (GeteiltV (D := declOf output.compiled.unit) (output.goalUnit Q).P (output.goalUnit Q).ws)
      (output.goalStart Q live) state)
    (t : (declOf output.compiled.unit).Tab) (k : Int) (f : (declOf output.compiled.unit).Feld t)
    (changed : state.m.speicher.slots t k f ≠ (speicherR (output.goalUnit Q).sp0).slots t k f) :
    ImBereich (declOf output.compiled.unit) t k ∧
      (k < (declOf output.compiled.unit).count t →
        ∀ address, output.image.Y.elem t f k.toNat ≤ address →
          address < output.image.Y.elem t f k.toNat + 8 * valueWords ((declOf output.compiled.unit).typ t f) →
          InitialLayout.tableBase output.image.Y t ≤ address ∧
            address < InitialLayout.tableBase output.image.Y t + tabSz output.compiled.unit t) := by
  have outside := rufErreichbarGX_aussen (fun _ shared => by
    obtain ⟨_, impossible, _⟩ := shared.1.1
    cases impossible) foreignConfined (fadenErreichbarX_GX reached)
  have inExtent : ImBereich (declOf output.compiled.unit) t k :=
    Classical.byContradiction fun notIn => changed (outside t k f notIn)
  refine ⟨inExtent, ?_⟩
  intro bounded address lower upper
  have layout := initialLayout_bild output.emission
  have actual : (k.toNat : Int) < output.image.Y.count t := by
    rw [layout.count]
    have nonnegative := inExtent.1
    omega
  obtain ⟨base, last⟩ := InitialLayout.cell_in_table layout t f k.toNat actual
  exact ⟨Nat.le_trans base lower, Nat.lt_of_lt_of_le upper last⟩

/-- The row layout cannot name the exact column addresses and sizes for
    two fields at two indices. The contradiction is in the row stride,
    independently of relocation or of the particular table values. -/
theorem column_addresses_exclude_row_layout {D : Deklaration} (L : Lay D)
    (row : AdressLayout D) (valid : LayoutOk row)
    (t : D.Tab) (f other : D.Feld t) (distinct : f ≠ other)
    (first : row.adresse t 0 f = L.elem t f 0)
    (second : row.adresse t 1 f = L.elem t f 1)
    (size : row.groesse t f = 8 * valueWords (D.typ t f))
    (otherNonempty : 0 < row.groesse t other) : False := by
  have stride : row.breite t = row.groesse t f := by
    simp [AdressLayout.adresse, Lay.elem] at first second
    omega
  have room := valid.feld t f
  have otherRoom := valid.feld t other
  rcases valid.felder t f other distinct with left | right <;> omega

end Gabbro.Stage0
