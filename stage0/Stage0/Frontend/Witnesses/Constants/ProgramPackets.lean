module
public import Stage0.Frontend.Witnesses.Constants.Compilation
public import Stage0.Frontend.Constants.ArrayConstants
public import Stage0.Senke.Ausdruck.Old.Source

@[expose] public section
namespace Gabbro.Stage0.Frontend.ConstPhases
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- Choose complete canonical triples after success is fixed, before the assembler projects them. -/
def Functions.of_success {unit : UProg}
    (produced : ∀ f : Fin unit.fns.length, (lowerFnAt unit f).toOption.isSome = true)
    (noInvariants : unit.invs = [])
    (noMeasures : ∀ f : Fin unit.fns.length, (fnAt unit f).decreases = none)
    (contracts : contractGate unit = true) : Functions unit where
  values := fun f => (lowerFnAt unit f).toOption.get (produced f)
  equations := fun f => Gabbro.Grammatik.except_ok_get (produced f)
  noInvariants := noInvariants
  noMeasures := noMeasures
  contracts := contracts

/-- Success of each actual item composes through the existing dependent array-check fold. -/
theorem checked_array_items {original : List SItemTief}
    (u : UProg) (scope : Frontend.Scopes original) :
    ∀ items : List SItemTief,
      (∀ item ∈ items, (Frontend.checkArrayItem u scope item).toOption.isSome = true) →
      (Frontend.checkArrays u scope items).toOption.isSome = true := by
  intro items
  induction items with
  | nil => intro _; rfl
  | cons item rest ih =>
    intro each
    have head := Gabbro.Grammatik.except_ok_get (each item (List.mem_cons_self))
    have tail := Gabbro.Grammatik.except_ok_get
      (ih (fun entry member => each entry (List.mem_cons_of_mem item member)))
    rw [Frontend.checkArrays, head, tail]
    rfl

/-- The existing dependent collector retains a family whose readers already return that family. -/
theorem collect_values (n : Nat) :
    ∀ (T : Fin n → Type) (values : (i : Fin n) → T i),
      OldSource.collect n T (fun i => .ok (values i)) = .ok values := by
  induction n with
  | zero =>
    intro T values
    apply congrArg (fun result : (i : Fin 0) → T i => Except.ok (ε := String) result)
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    intro T values
    rewrite [OldSource.collect, ih]
    apply congrArg (fun result : (i : Fin (n + 1)) → T i => Except.ok (ε := String) result)
    funext i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j; rfl

/-- Replay restoration symbolically when the actual expanded posts contain no entry reads. -/
theorem restore_entry_free (items expanded : List SItemTief)
    (requirements : List (STyp × String)) (unit : UProg) (program : Programm (declOf unit))
    (expansion : expandU items = .ok (expanded, requirements))
    (entryFree : ∀ f : Fin unit.fns.length,
      (OldSource.clauses expanded (fnAt unit f).name).any OldSource.hasEntry = false) :
    OldSource.restore items unit program = .ok program := by
  have readers : OldSource.atFunction expanded unit program =
      (fun f => .ok (program.ensures f)) := by
    funext f
    unfold OldSource.atFunction
    dsimp only
    erw [entryFree f]
    rfl
  unfold OldSource.restore
  rewrite [expansion]
  dsimp only [bind, Except.bind]
  erw [readers, collect_values]
  rfl

/-- Check the actual function results before choosing the assembler's invariant
    and interface fields. The chosen fields remain exactly those of Functions.program. -/
theorem accepts_function_results {unit : UProg} (functions : Functions unit)
    (checked : ∀ (invariants : ∀ i : Fin unit.invs.length, InvTy unit i)
      (pointers : ∀ n, CallContract (declOf unit) ((declOf unit).sigNr n))
      (foreigns : ∀ a, CallContract (declOf unit) ((declOf unit).asignatur a)),
      OldSource.accepts unit
        (progOfFn unit (fun f => (functions.values f).1)
          (fun f => (functions.values f).2.1) (fun f => (functions.values f).2.2)
          invariants pointers foreigns) = .ok true) :
    OldSource.accepts unit functions.program = .ok true := by
  unfold Functions.program
  exact checked _ _ _

end Gabbro.Stage0.Frontend.ConstPhases
