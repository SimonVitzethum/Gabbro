module

public import Grammatik.Logik.Vertraege.Pruefer.Compiler
public import Grammatik.Logik.Vertraege.Pruefer.Control.Entry

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.VC
open Invarianten.Pruefer Invarianten.Frag.Symbolic Symbolic

variable {D : Deklaration} {S : SperrInv D} {program : Programm D}

/-- Obligations at all exits, preserving inherited errors explicitly. -/
def EndPost (program : Programm D) (f : D.Fn) (old : World D)
    (locals : Env D (D.params f)) (allowed : Logik D → Prop) :
    EndAusgang (vertragVon D f) false (D.params f) → Prop
  | .zurueck next value => EnsAmRueck program f old next locals value ∧ InvAmRueck program f next
  | .why next _ => InvAmRueck program f next
  | .leave _ _ _ | .next _ _ _ => False
  | .logik error => allowed error
  | .hardware _ => True

def CheckedEnvironment (policy : CallObligation program) (f : D.Fn)
    (locals : Env D (D.params f)) : Prop :=
  ∀ (runtime : Runtime program (fun _ => []) S) world allowed,
    HandlerSafe policy runtime allowed → ReqAmEintritt program f world locals →
      runtime.wpE (program.rumpf f) (EndPost program f world locals allowed) world locals

def CheckedExecution (policy : CallObligation program) (f : D.Fn) : Prop :=
  ∀ locals, CheckedEnvironment (S := S) policy f locals

/-- Return expressions use symbolic results and the frozen entry parameters. -/
def contractGoals (program : Programm D) (f : D.Fn)
    (symbols : SymEnv D Nat (D.params f)) (bounded : symbols.Bounded next)
    (invariants : InvariantFormula program (D.invs.filter (schuldet f)))
    (snapshot : Option (Snapshot.Region D next) := none) :
    Symbolic.Goals (program := program) (S := S) (entryContext symbols bounded snapshot) (vertragVon D f) (D.params f) where
  normal := .truth _
  escape := .truth _
  again := .truth _
  returned := {
    holds := fun item _ world result =>
      EnsAmRueck program f item.1 world item.2 (envResult (D.erg f) result) ∧ InvAmRueck program f world
    encode := fun more larger returned rb => do
      let post ← translateSnapshot (Snapshot.regionNames snapshot) (Snapshot.regionStart snapshot)
        (program.ensures f) (withResult (D.erg f) returned symbols)
      return {
        formula := .and post.payload (renameProp Sum.inl (quoteQF invariants.formula))
        sound := fun valuation item present _ world valid actual realized => by
          have entry := (symbols.realizes_world item.2 valuation item.1 world).mp
            (entryContext_locals symbols bounded snapshot valuation item present)
          have combined := withResult_realizes (D.erg f) returned symbols valuation world actual item.2 realized entry
          have ensures := (post.bool_iff valuation item.1 world _
            (entryContext_memory symbols bounded snapshot valuation item present) combined).mpr valid.1
          constructor
          · unfold EnsAmRueck
            exact ensures
          · have inv := (quoteQF_denote invariants.formula (assignment world)).mp
              ((renameProp_denote Sum.inl (fun _ _ same => Sum.inl.inj same) _ _).mp valid.2)
            exact fun name member owed => (invariants.correct world).mp inv name (List.mem_filter.mpr ⟨member, owed⟩) } }
  reason := .ofFormula _ invariants.formula

theorem contractGoals_sound (program : Programm D) (f : D.Fn)
    (symbols : SymEnv D Nat (D.params f)) (bounded : symbols.Bounded next)
    (invariants : InvariantFormula program (D.invs.filter (schuldet f)))
    (snapshot : Option (Snapshot.Region D next)) (item : Entry D (D.params f))
    (runtime : Runtime program (fun _ => []) S) (allowed : Logik D → Prop)
    (outcome : EndAusgang (vertragVon D f) false (D.params f))
    (valid : (contractGoals program f symbols bounded invariants snapshot).endHolds item runtime allowed outcome) :
    EndPost program f item.1 item.2 allowed outcome := by
  cases outcome with
  | zurueck world value =>
      change EnsAmRueck program f item.1 world item.2
        (envResult (D.erg f) (ergEnv (D.erg f) value .nil)) ∧ InvAmRueck program f world at valid
      exact ⟨(congrArg (EnsAmRueck program f item.1 world item.2)
        (envResult_ergEnv (D.erg f) value)).mp valid.1, valid.2⟩
  | why world reason =>
      exact fun name member owed => (invariants.correct world).mp valid name (List.mem_filter.mpr ⟨member, owed⟩)
  | leave h _ _ => cases h
  | next h _ _ => cases h
  | logik _ => exact valid
  | hardware _ => trivial

def entryVC (symbols : SymEnv D Nat Γ) (precondition : LProp (Key D Nat)) (postcondition : LProp (Key D Nat)) : LProp (Key D Nat) :=
  let body := .imp (environmentBounds symbols) (.imp precondition postcondition)
  .imp (memoryFacts body) body

/-- One open symbolic VC; no integer input or result is decoded into cases. -/
def checkEnvironmentAt (program : Programm D) (S : SperrInv D)
    (symbols : SymEnv D Nat (D.params f)) (bounded : symbols.Bounded next)
    (snapshot : Option (Snapshot.Region D next))
    (policy : CallPolicy program (entryContext symbols bounded snapshot))
    (sources : LockSources S) (budget : VCBudget) (hint : Option (QF (Observation D)))
    (invariants : InvariantFormula program (D.invs.filter (schuldet f))) :
    Except Frag.Refusal (PLift (∀ valuation item, (entryContext symbols bounded snapshot).holds valuation item →
      ∀ (runtime : Runtime program (fun _ => []) S) allowed,
      HandlerSafe (policy.semantic item) runtime allowed → ReqAmEintritt program f item.1 item.2 →
      runtime.wpE (program.rumpf f) (EndPost program f item.1 item.2 allowed) item.1 item.2)) := do
  let requires ← Invarianten.Frag.Symbolic.translate (program.requires f) symbols
  let compiled ← ending policy (lockFormula S sources) budget hint budget.depth
    (program.rumpf f) symbols bounded (contractGoals program f symbols bounded invariants snapshot)
  let guarded := match snapshot with
    | none => compiled.formula
    | some region => .imp (Snapshot.equations region.start region.names) compiled.formula
  let body : LProp (Key D Nat) := .imp (environmentBounds symbols) (.imp requires.payload guarded)
  let matrix := entryVC symbols requires.payload guarded
  if accepted : decideB (close (lower matrix)) (close_closed (lower matrix)) = true then
    return ⟨fun valuation item present runtime allowed safe entry => by
      have realized := entryContext_locals symbols bounded snapshot valuation item present
      have valid := (lower_denote matrix (values valuation item.1)).mp
        (close_sound (lower matrix) accepted (values valuation item.1))
      have facts := memoryFacts_sound body valuation item.1
      have ready := valid facts (environmentBounds_sound symbols valuation item.1 item.2 realized)
        ((requires.bool_iff valuation item.1 item.2 realized).mp entry)
      have compiledReady : compiled.formula.denote (values valuation item.1) := by
        cases snapshot with
        | none => exact ready
        | some region => exact ready ((Snapshot.equations_denote region.names region.start valuation item.1).mpr present.2)
      exact contractGoals_sound program f symbols bounded invariants snapshot item runtime allowed _
        (compiled.sound valuation item present runtime item.1 compiledReady item.2 realized allowed safe)⟩
  else .error (.unsupported ("outside the decidable fragment: contract VC abstraction cannot establish the postcondition or a call obligation" ++
    match D.params f with | [] => "; parameters = []" | _ => ""))

/-- Allocate entry keys once, before compiling the actual body. The no-snapshot
    case is the empty instance of the same production compiler and VC gate. -/
def checkEnvironment (program : Programm D) (S : SperrInv D)
    (symbols : SymEnv D Nat (D.params f)) (bounded : symbols.Bounded next)
    (policy : CallPolicy program (entryContext symbols bounded))
    (sources : LockSources S) (budget : VCBudget) (hint : Option (QF (Observation D)))
    (invariants : InvariantFormula program (D.invs.filter (schuldet f))) :
    Except Frag.Refusal (PLift (∀ valuation item, symbols.Realizes valuation item.1 item.2 →
      ∀ (runtime : Runtime program (fun _ => []) S) allowed,
      HandlerSafe (policy.semantic item) runtime allowed → ReqAmEintritt program f item.1 item.2 →
      runtime.wpE (program.rumpf f) (EndPost program f item.1 item.2 allowed) item.1 item.2)) := do
  let plan ← snapshotPlan (program.ensures f)
  match plan with
  | none => checkEnvironmentAt program S symbols bounded none policy sources budget hint invariants
  | some names => do
      let more := next + names.length
      have larger : next ≤ more := Nat.le_add_right _ _
      let region : Snapshot.Region D more := ⟨next, names, Nat.le_refl _⟩
      let futureBounded := symbols.bounded_mono bounded larger
      let futureContext := entryContext symbols futureBounded (some region)
      let futurePolicy := policy.refine larger futureContext (fun _ _ present => present.1)
      let checked ← checkEnvironmentAt program S symbols futureBounded (some region)
        futurePolicy sources budget hint invariants
      return ⟨fun valuation item realized runtime allowed safe required => by
        let chosen := Snapshot.extend next names valuation item.1
        have agree : ∀ key, key < next → valuation key = chosen key := fun key before =>
          (Snapshot.extend_preserves names next valuation item.1 key (Or.inl before)).symm
        have current := (symbols.realizes_congr next bounded valuation chosen agree item.1 item.1 item.2).mp realized
        exact checked.down chosen item ⟨current, Snapshot.extend_realizes names next valuation item.1⟩
          runtime allowed safe required⟩

/-- Finite Boolean/capability templates cover every actual typed parameter
    environment; integer parameters each occupy one immutable observation. -/
def checkExecution (program : Programm D) (S : SperrInv D)
    (sources : LockSources S) (budget : VCBudget) (hint : Option (QF (Observation D))) (f : D.Fn) :
    Except Frag.Refusal (PLift (CheckedExecution (S := S) (requiresObligation program) f)) := do
  let _ ← snapshotPlan (program.ensures f)
  let invariants ← invariantFormula program (D.invs.filter (schuldet f))
  let domain ← parameters (D := D) budget.expansion 0 (D.params f)
  if argumentSpecializations budget.specializations (D.params f) *
      endSpecializations program (uniformPost program f) budget.expansion budget.specializations
        (program.rumpf f) > budget.specializations then
    .error (.unsupported "contract VC specialization product exceeds the work budget")
  else pure ()
  let checked ← collect domain.templates.attach _ (fun entry =>
    checkEnvironment program S entry.val (domain.bounded entry.val entry.property)
      (requiresPolicy program _) sources budget hint invariants)
  return ⟨fun locals runtime world allowed safe required => by
    obtain ⟨symbols, member, valuation, realized, _⟩ := domain.cover world locals (fun _ => 0)
    exact (checked.down ⟨symbols, member⟩ (List.mem_attach _ _)) valuation (world, locals) realized
      runtime allowed safe required⟩

end Gabbro.Grammatik.Vertraege.Pruefer
