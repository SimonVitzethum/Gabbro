module
public import Stage0.Frontend.Elaboration
public import Grammatik.Parser.Elab.UebersetzeAllg3.Guest.Connection
public import Stage0.Frontend.ExpansionGate
public import Stage0.Frontend.Constants.ArrayConstants
public import Stage0.Frontend.Initializers
public import Stage0.Frontend.Measures
public import Stage0.Senke.Ausdruck.Old.Source
@[expose] public section


namespace Gabbro.Stage0
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
  Gabbro.Grammatik.Parser.Cover.Differenz

/-- The actual source-to-G endpoint. Canonical expansion consumes lexically scoped declarations
    and certified source scopes. The existing old(global) bridge and full checker remain mandatory. -/
structure Compiled (text : String) (options : Profil.Options := {}) where
  source : Frontend.Source text options
  unit : UProg
  main : (declOf unit).Fn
  program : Programm (declOf unit)
  /-- The exact canonical expansion and the member list selected by the metadata gate. -/
  expanded : List SItemTief
  requirements : List (STyp × String)
  gateMembers : List SItemTief
  gateExpansion : Gabbro.Grammatik.Parser.Modules.prepare
    (pre108 source.prepared.elaborierbar) = .ok (expanded, requirements)
  elaborated : ((Frontend.elabWithScopes
    (pre108 source.prepared.elaborierbar)
    source.scopes.values source.scopes.types source.scopes.functions
    (Frontend.tableWithEmpty source.scopes.values source.scopes.types)).bind (Profil.selectUnit options)).map
      (fun u => {u with exportGate := Konst.checkSourceMetadata gateMembers}) = .ok unit
  entry : fnIdx unit.fns (Profil.entryName options) = .ok main
  lowered : ∃ raw fs, lowerAllg unit = .ok (raw, fs) ∧
    OldSource.restore (pre108 source.prepared.elaborierbar) unit raw = .ok program
  accepted : OldSource.accepts unit program = .ok true
  arrayConstants : ∀ item ∈ uMembers (pre108 source.prepared.elaborierbar), Frontend.ArrayMeaning unit source.scopes item
  initializerExports : Frontend.checkInitializers (uMembers (pre108 source.prepared.elaborierbar)) unit = .ok ()
  constantExports : Konst.checkSourceConstants (uMembers (pre108 source.prepared.elaborierbar)) = .ok ()
  /-- The selected original or expanded members pass the complete C17 check:
      original runtime metadata, certified const substitution and residual metadata. -/
  gateChecked :
    (gateMembers = uMembers expanded ∧ Konst.checkSourceMetadata gateMembers = .ok ()) ∨
    (gateMembers = uMembers (pre108 source.prepared.elaborierbar) ∧
      Konst.checkSourceMetadata gateMembers = .ok ())
  metadata : unit.exportGate = Konst.checkSourceMetadata gateMembers
  /-- The exact source-derived measure, checked by generic lowering at entry parameters/resources. -/
  measures : {exported : Measures.Export unit // Measures.lowerMeasures unit = .ok exported} :=
    Measures.checkedExport unit (by
      obtain ⟨raw, fs, lowered, _⟩ := lowered
      obtain ⟨exported, origin, _⟩ := Measures.lowerAllg_measures unit raw fs lowered
      exact ⟨exported, origin⟩)
  /-- Cycle lengths are checked on the final program, after old-state restoration. -/
  measureLengths : Measures.cycleLengths unit program measures.val.mass = true :=
    Frontend.compiled_measure_lengths (pre108 source.prepared.elaborierbar) unit program
      measures.val measures.property lowered

/-- The remainder of compilation once the expansion-aware gate has accepted.
    The shared elaborator expands declared checks and their producer/probe/gate functions;
    profile selection then adds the selected C16 consumer and driver to that unit.
    `gateChecked` is the checked original-or-expanded disjunct for this unit. -/
def compileChecked (source : Frontend.Source text options)
    (hc : Konst.checkSourceConstants (uMembers (pre108 source.prepared.elaborierbar)) = .ok ())
    (expanded : List SItemTief) (requirements : List (STyp × String))
    (hp : Gabbro.Grammatik.Parser.Modules.prepare (pre108 source.prepared.elaborierbar) =
      .ok (expanded, requirements))
    (gateMembers : List SItemTief)
    (gateChecked :
      (gateMembers = uMembers expanded ∧ Konst.checkSourceMetadata gateMembers = .ok ()) ∨
      (gateMembers = uMembers (pre108 source.prepared.elaborierbar) ∧
        Konst.checkSourceMetadata gateMembers = .ok ())) :
    Except String (Compiled text options) := do
  let declarations := pre108 source.prepared.elaborierbar
  match he : (Frontend.elabWithScopes declarations
      source.scopes.values source.scopes.types source.scopes.functions
      (Frontend.tableWithEmpty source.scopes.values source.scopes.types)).bind (Profil.selectUnit options) with
  | .error e => throw e
  | .ok candidate => do
    let unit := {candidate with exportGate := Konst.checkSourceMetadata gateMembers}
    have elaborated : ((Frontend.elabWithScopes declarations
        source.scopes.values source.scopes.types source.scopes.functions
        (Frontend.tableWithEmpty source.scopes.values source.scopes.types)).bind (Profil.selectUnit options)).map
          (fun u => {u with exportGate := Konst.checkSourceMetadata gateMembers}) = .ok unit := by
      rw [he]
      rfl
    have metadata : unit.exportGate = Konst.checkSourceMetadata gateMembers := rfl
    match hi : Frontend.checkInitializers (uMembers declarations) unit with
    | .error error => throw error
    | .ok () => do
      let arrays ← Frontend.checkArrays unit source.scopes (uMembers declarations)
      match hm : fnIdx unit.fns (Profil.entryName options) with
      | .error e => throw e
      | .ok main =>
        match hl : lowerAllg unit with
        | .error e => throw e
        | .ok (raw, fs) =>
          match hr : OldSource.restore declarations unit raw with
          | .error e => throw e
          | .ok program =>
            match ha : OldSource.accepts unit program with
            | .error e => throw e
            | .ok false => throw "refused by the checker (AkzeptiertX)"
            | .ok true => pure { source, unit, main, program, elaborated,
                entry := hm, lowered := ⟨raw, fs, hl, hr⟩, accepted := ha,
                arrayConstants := arrays.down, initializerExports := hi,
                constantExports := hc, expanded, requirements, gateMembers,
                gateExpansion := hp, gateChecked, metadata }

/-- Compilation preserves original constant admission and checks both metadata sides.
    Expansion-consumed headers prefer the expanded side; ordinary units prefer the original.
    A failed preferred check can only fall back to the same complete C17 check on the other side. -/
def compile (text : String) (options : Profil.Options := {}) : Except String (Compiled text options) := do
  let source ← Frontend.source text options
  let declarations := pre108 source.prepared.elaborierbar
  let members := uMembers declarations
  match hc : Konst.checkSourceConstants members with
  | .error error => throw error
  | .ok () => do
    match hp : Gabbro.Grammatik.Parser.Modules.prepare declarations with
    | .error error => throw error
    | .ok (expanded, requirements) =>
      if members.any Frontend.expansionHeader then
        match hx : Konst.checkSourceMetadata (uMembers expanded) with
        | .ok () => compileChecked source hc expanded requirements hp (uMembers expanded)
            (Or.inl ⟨rfl, hx⟩)
        | .error expandedError =>
          match ho : Konst.checkSourceMetadata members with
          | .ok () => compileChecked source hc expanded requirements hp members (Or.inr ⟨rfl, ho⟩)
          | .error _ => throw expandedError
      else
        match ho : Konst.checkSourceMetadata members with
        | .ok () => compileChecked source hc expanded requirements hp members (Or.inr ⟨rfl, ho⟩)
        | .error originalError =>
          match hx : Konst.checkSourceMetadata (uMembers expanded) with
          | .ok () => compileChecked source hc expanded requirements hp (uMembers expanded)
              (Or.inl ⟨rfl, hx⟩)
          | .error _ => throw originalError

/-- The actual source program keeps all declared table/global carriers and their exact read bound. -/
theorem Compiled.invariants {text : String} {options : Profil.Options} (result : Compiled text options)
    (i : Fin result.unit.invs.length) :
    (declOf result.unit).traeger i = invTraeger result.unit i ∧
      ∀ c ∈ (result.program.invariante i).orte, c ∈ (declOf result.unit).traeger i := by
  obtain ⟨raw, fs, lowered, restored⟩ := result.lowered
  have same := OldSource.restore_invariante _ result.unit raw result.program restored
  rw [same]
  exact lowerAllg_traeger result.unit raw fs lowered i

/-- Postcondition restoration retains every exported C08 pre/postcondition. -/
theorem Compiled.foreign_contracts {text : String} {options : Profil.Options}
    (result : Compiled text options) (a : (declOf result.unit).Ax) :
    lowerAxContract result.unit a = .ok (result.program.axVertrag a) := by
  obtain ⟨raw, fs, lowered, restored⟩ := result.lowered
  rw [OldSource.restore_axVertrag _ result.unit raw result.program restored]
  exact lowerAllg_axVertrag result.unit raw fs lowered a

/-- The exact source descriptor list reaches production admission after all
    restoration. Its length and per-descriptor verdict remain observable. -/
theorem Compiled.guest_descriptors {text : String} {options : Profil.Options}
    (result : Compiled text options) :
    ∃ guests, sourceGuests result.unit = .ok guests ∧
      guests.length = result.unit.guests.length ∧
      ∀ guest ∈ guests, guest.admittedB = true :=
  OldSource.accepts_guests result.unit result.program result.accepted

/-- Original-source scalar and function semantics, a unique acyclic alias namespace with a
    certified declaration permutation, and the identical
    UProg/declOf/lowerAllg endpoint of the actual compiler. Supplied scopes are not arbitrary premises:
    they are derived from the original declarations by Source.scopes and the canonical evaluators. -/
def CanonicalSourceProgram {text : String} {options : Profil.Options} (result : Compiled text options) : Prop :=
    let declarations := pre108 result.source.prepared.elaborierbar
    let original := uMembers declarations
    let scope := result.source.scopes
    Profil.runnerCompatible options ∧
    result.source.prepared.selected = Gabbro.Grammatik.Parser.Auswahl.waehleL options.mode result.source.items ∧
    lex text = .ok result.source.tokens ∧
    parseTopTief result.source.tokens = .ok result.source.items ∧
    Oeffentlich.huelleZu result.source.prepared.elaborierbar = true ∧
    (scope.aliasConstants = uConstsRech (uKonstFns original) original [] ∨ scope.aliasConstants = scope.values) ∧
    Frontend.AliasAcyclic original ∧
    (Frontend.aliasNames original).Nodup ∧
    Frontend.ConstantAcyclic original ∧
    (Frontend.constantNames original).Nodup ∧
    scope.scalarOrder.Perm original ∧
    scope.aliasOrder.Perm original ∧
    scope.declared = scope.aliasOrder.foldl (Frontend.aliasStep scope.aliasConstants) [] ∧
    (∀ item ∈ original, Frontend.AliasMeaning scope.types item) ∧
    scope.functions = Frontend.constantFunctions scope.functionTypes original ∧
    (∀ fn ∈ scope.functions, ∃ item ∈ original, Frontend.FunctionMeaning scope.functionTypes item fn) ∧
    (∀ names item table,
      Frontend.tableWithEmpty scope.values scope.types names item = .ok table →
      uTabelle scope.values scope.types names item = .ok table ∨
        Frontend.EmptyTableMeaning scope.values item table) ∧
    Frontend.ScopeStable scope ∧
    Frontend.typedConstants scope.declared scope.functions scope.scalarOrder [] = some scope.values ∧
    (∀ item ∈ original, Frontend.ConstantMeaning scope.types scope.functions scope.values item) ∧
    Frontend.checkInitializers original result.unit = .ok () ∧
    Konst.checkSourceConstants original = .ok () ∧
    Frontend.compileTimeSafe original = true ∧
    ((Frontend.elabWithScopes declarations scope.values scope.types scope.functions
      (Frontend.tableWithEmpty scope.values scope.types)).bind (Profil.selectUnit options)).map
        (fun u => {u with exportGate := Konst.checkSourceMetadata result.gateMembers}) = .ok result.unit ∧
    (∃ raw fs, lowerAllg result.unit = .ok (raw, fs) ∧
      OldSource.restore declarations result.unit raw = .ok result.program) ∧
    OldSource.accepts result.unit result.program = .ok true ∧
    (∀ item ∈ original, Frontend.ArrayMeaning result.unit scope item) ∧
    (∃ expanded requirements, Gabbro.Grammatik.Parser.Modules.prepare declarations =
      .ok (expanded, requirements) ∧
      ((result.gateMembers = uMembers expanded ∧
          Konst.checkSourceMetadata result.gateMembers = .ok ()) ∨
        (result.gateMembers = original ∧ Konst.checkSourceMetadata result.gateMembers = .ok ()))) ∧
    result.unit.exportGate = Konst.checkSourceMetadata result.gateMembers ∧
    Measures.lowerMeasures result.unit = .ok result.measures.val ∧
    (∀ f, Measures.SourceTuple result.unit f (result.measures.val.mass f)) ∧
    Measures.cycleLengths result.unit result.program result.measures.val.mass = true ∧
    (∀ i : Fin result.unit.invs.length,
      (declOf result.unit).traeger i = invTraeger result.unit i ∧
      ∀ c ∈ (result.program.invariante i).orte, c ∈ (declOf result.unit).traeger i) ∧
    Gabbro.Grammatik.Parser.ProfilBindung.bindungB result.source.prepared.bindung = true ∧
    Gabbro.Stage0.Profil.abschnittFehler result.source.prepared.selected = none

theorem compile_source_program (text : String) {options : Profil.Options} (result : Compiled text options) :
    CanonicalSourceProgram result := by
  exact ⟨result.source.prepared.compatible, result.source.prepared.selection, result.source.lexed, result.source.parsed, result.source.visibility, result.source.scopes.aliasOrigin, result.source.aliasDependencies.1, result.source.aliasDependencies.2, result.source.constantDependencies.1, result.source.constantDependencies.2, result.source.scopes.scalarPermutation, result.source.scopes.aliasPermutation, result.source.scopes.aliases, result.source.aliasMeanings, result.source.scopes.functionOrigin, result.source.scopes.functionMeaning, Frontend.tableWithEmpty_sound _ _, result.source.derived.stable,
    result.source.scopes.scalarValues, result.source.constantMeanings, result.initializerExports, result.constantExports, result.source.compileTime, result.elaborated, result.lowered,
    result.accepted, result.arrayConstants,
    ⟨result.expanded, result.requirements, result.gateExpansion, result.gateChecked⟩,
    result.metadata, result.measures.property,
    result.measures.val.source, result.measureLengths, result.invariants,
    result.source.prepared.bindungOk, result.source.prepared.abschnittFrei⟩

/-- Gate acceptance ties the selected metadata side to the stored canonical expansion.
    Each side retains the complete certified C17 substitution and runtime checks. -/
theorem Compiled.expansion_gate {text : String} {options : Profil.Options}
    (result : Compiled text options) :
    Frontend.checkExpansionGate (pre108 result.source.prepared.elaborierbar) =
      .ok (result.expanded, result.requirements) ∨
    Konst.checkSourceMetadata (uMembers (pre108 result.source.prepared.elaborierbar)) = .ok () := by
  cases result.gateChecked with
  | inl checked =>
    obtain ⟨selected, accepted⟩ := checked
    rw [selected] at accepted
    exact Or.inl (by
      unfold Frontend.checkExpansionGate
      rw [result.gateExpansion, accepted]
      rfl)
  | inr checked =>
    obtain ⟨selected, accepted⟩ := checked
    rw [selected] at accepted
    exact Or.inr accepted

/-- The image is built for exactly the checked profile binding. -/
theorem Compiled.profile_binding {text : String} {options : Profil.Options} (result : Compiled text options) :
    Gabbro.Grammatik.Parser.ProfilBindung.bindungB result.source.prepared.bindung = true :=
  result.source.prepared.bindungOk

/-- The compiled unit carries no named sections into the flat image. -/
theorem Compiled.sections_free {text : String} {options : Profil.Options} (result : Compiled text options) :
    Gabbro.Stage0.Profil.abschnittFehler result.source.prepared.selected = none :=
  result.source.prepared.abschnittFrei

/-- The optional termination certificate uses the final compiled program and its exact source
    measure. The user supplies the existing duty; ordinary compilation and depth fuel are unchanged. -/
theorem Compiled.termination {text : String} {options : Profil.Options} (result : Compiled text options)
    (E : Zielsatz.Einheit (declOf result.unit)) (program : E.P = result.program)
    (duty : Measures.Obligations result.unit E result.measures.val)
    (C : Zielsatz.PrueferX) (ls : Zielsatz.Aufzaehlung (declOf result.unit).Lock)
    (cs : Zielsatz.Aufzaehlung ((declOf result.unit).Tab ⊕ (declOf result.unit).Glob))
    (accepted : C.akzeptiert E (List.finRange result.unit.fns.length) ls.1 cs.1 = true)
    (user : Zielsatz.NutzerPflichtA E) (passes : Nat) (O : Orakel (declOf result.unit))
    (hardware : Zielsatz.HardwareAnnahmen O E.Q)
    (sp : Speicher (declOf result.unit).mitRuhe)
    (init : Faden → Σ f : (declOf result.unit).mitRuhe.Fn,
      Env (declOf result.unit).mitRuhe ((declOf result.unit).mitRuhe.params f))
    (runtime : Zielsatz.Laufzeit E sp init) (alive : Faden → Bool)
    (run : FadenLaufX E.P.mitRuhe O.mitRuhe passes (Zielsatz.GeteiltV E.P E.ws))
    (initial : run.K 0 = FadenStart E.P.mitRuhe sp init alive) (thread : Faden) :
    (∃ N, ∀ j, N ≤ j → run.akt j ≠ some thread) ∧
      ((∀ w, (init thread).1 = some w →
          klasse E.P (List.finRange result.unit.fns.length) result.measures.val.mass.hat w = .endet) →
        ∀ j, ¬ Zielsatz.HaltBenannt O.mitRuhe passes (run.K j).m .budget thread) := by
  have lengths : Measures.cycleLengths result.unit E.P result.measures.val.mass = true := by
    rw [program]
    exact result.measureLengths
  exact Measures.source_termination result.unit E result.measures.val result.measures.property
    lengths duty C ls cs accepted user passes O hardware sp init runtime alive run initial thread

/-- Every function the compiled unit generated for a transition declaration is in the lowered
    G program and carries its expansion certificate there (the program before the old(global)
    restoration, which replaces only `ensures`; a generated function has no `old` clause, so
    the restoration keeps its `ensures`). The call theorems of the certificate relate every
    successful call of it to the declaration's full pre/post relation and frame; no generated
    function is emitted without this certificate because `lowerAllg` refuses its name otherwise. -/
theorem compile_transitions_certified {text : String} {options : Profil.Options}
    (result : Compiled text options) :
    ∃ raw fs, lowerAllg result.unit = .ok (raw, fs) ∧
      OldSource.restore (pre108 result.source.prepared.elaborierbar) result.unit raw = .ok result.program ∧
      ∀ c : Fin result.unit.fns.length, (fnAt result.unit c).name.startsWith "#transition#" = true →
        ∃ (state : UZustand) (tr : UTransition), transitionOfFn result.unit c = some (state, tr) ∧
          (Nonempty (TransitionExpansion raw c) ∨ Nonempty (TransitionShiftExpansion raw c)) := by
  obtain ⟨raw, fs, hl, hr⟩ := result.lowered
  exact ⟨raw, fs, hl, hr, fun c hname => lowerAllg_transition_certified result.unit raw fs hl c hname⟩

end Gabbro.Stage0
