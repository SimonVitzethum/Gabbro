module
public import Stage0.SourceWitness
public import Grammatik.Parser.Elab.UebersetzePipeline
import Grammatik.Kern.Taktik.KernelRfl
import Grammatik.Logik.Vertraege.Pruefer.Witness.Refusal
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
@[expose] public section

namespace Gabbro.Stage0.TransitionContractWitness
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-- The actual scoped frontend output, before any dependent program getters. -/
def sourceData (source : String) : Except String (List SItemTief × UProg) := do
  let parsed ← Frontend.source source {}
  let declarations := pre108 parsed.prepared.elaborierbar
  let unit ← (Frontend.elabWithScopes declarations
    parsed.scopes.values parsed.scopes.types parsed.scopes.functions
    (Frontend.tableWithEmpty parsed.scopes.values parsed.scopes.types)
    (widths := parsed.scopes.widths)).bind (Profil.selectUnit {})
  return (declarations, unit)

/-- Recover the actual source contracts before the rejecting admission step. -/
def sourceModel (source : String) : Except String (Σ u : UProg, Programm (declOf u)) := do
  let input ← sourceData source
  let (raw, _) ← lowerAllg input.2
  let program ← OldSource.restore input.1 input.2 raw
  return ⟨input.2, program⟩

/-- Successful lowering/restoration retains the actual frontend unit. -/
theorem sourceModel_unit (source : String) (input : List SItemTief × UProg)
    (output : Σ u : UProg, Programm (declOf u))
    (parsed : sourceData source = .ok input)
    (emitted : sourceModel source = .ok output) : output.1 = input.2 := by
  unfold sourceModel at emitted
  rw [parsed] at emitted
  dsimp only [bind, Except.bind] at emitted
  cases lowered : lowerAllg input.2 with
  | error cause => simp only [lowered, bind, Except.bind, reduceCtorEq] at emitted
  | ok pair =>
    rcases pair with ⟨raw, functions⟩
    simp only [lowered, bind, Except.bind] at emitted
    cases restored : OldSource.restore input.1 input.2 raw with
    | error cause => simp only [restored, bind, Except.bind, reduceCtorEq] at emitted
    | ok program =>
      simp only [restored, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at emitted
      exact (congrArg Sigma.fst emitted).symm

/-- A refused actual contract gate blocks unchanged production admission. -/
private theorem checker_refused_of_contracts (unit : UProg) (program : Programm (declOf unit))
    (mainIndex : (declOf unit).Fn)
    (contracts : Vertraege.Pruefer.KontrakteGeprueftB program
      (Cover.Differenz.sperrFamilie unit) (List.finRange unit.fns.length)
      (Cover.Differenz.sperrQuellen unit) = false) :
    OldSource.accepts unit program mainIndex ≠ .ok true := by
  intro accepted
  unfold OldSource.accepts at accepted
  split at accepted
  · cases accepted
  · cases guests : sourceGuests unit with
    | error cause => simp only [guests, bind, Except.bind, reduceCtorEq] at accepted
    | ok items =>
      simp only [guests, bind, Except.bind] at accepted
      have gate := (Vertraege.Pruefer.contractVerdict_true_iff _ _ _ _ _).mp accepted
      simp only [Zielsatz.AkzeptiertX, Invarianten.Pruefer.invariantVCB,
        contracts, Bool.and_false, Bool.false_eq_true] at gate

namespace Data

def transition (ordered : Bool) : UTransition where
  name := if ordered then "cycle" else "a"
  writes := if ordered then
    [{ place := .slot "T" "s" (.lit 0), source := .lit 0, target := .lit 1 },
     { place := .slot "T" "s" (.lit 1), source := .lit 0, target := .tab "T" "s" (.lit 0) }]
    else [{ place := .slot "T" "s" (.param "#transitionIndex"), source := .lit 0, target := .lit 1 }]
  clause := .and .tru .tru
  held := []
  puts := ["T"]
  gputs := []
  primitive := false

def transitionFunction (ordered : Bool) : UFn where
  name := if ordered then "#transition#S#cycle" else "#transition#S#a"
  params := if ordered then
    [("#index0", .int 0 1), ("#source0", .int 0 2), ("#target0", .int 0 2),
     ("#index1", .int 0 1), ("#source1", .int 0 2), ("#target1", .int 0 2)]
    else [("#index0", .int 0 1)]
  kinds := if ordered then [.index 0, .int, .int, .index 0, .int, .int] else [.index 0]
  res := none
  held := []
  puts := ["T"]
  gives := if ordered then
    [.cmp "==" (.tab "T" "s" (.param "#index0")) (.param "#target0"),
     .cmp "==" (.tab "T" "s" (.param "#index1")) (.param "#target1")]
    else [.cmp "==" (.tab "T" "s" (.param "#index0")) (.lit 1)]
  needs := if ordered then
    [.and .tru .tru,
     .cmp "==" (.param "#index0") (.lit 0),
     .cmp "==" (.param "#source0") (.lit 0),
     .cmp "==" (.param "#target0") (.lit 1),
     .cmp "==" (.param "#index1") (.lit 1),
     .cmp "==" (.param "#source1") (.lit 0),
     .cmp "==" (.param "#target1") (.tab "T" "s" (.lit 0)),
     .cmp "==" (.tab "T" "s" (.param "#index0")) (.param "#source0"),
     .cmp "==" (.tab "T" "s" (.param "#index1")) (.param "#source1")]
    else [.and .tru .tru, .cmp "==" (.tab "T" "s" (.param "#index0")) (.lit 0)]
  body := if ordered then
    [.assignTab "T" "s" (.param "#index0") (.param "#target0"),
     .assignTab "T" "s" (.param "#index1") (.param "#target1")]
    else [.shiftTab "T" "s" (.param "#index0") "S" 0 1]
  ret := .empty

def sourceUnit (ordered : Bool) : UProg where
  tabs := [{ name := "T", count := 2, cols := [("s", 0, 2)], breiten := [("s", 32)] }]
  locks := []
  fns :=
    [{ name := "main", params := [], kinds := [], res := some (0, 100), held := [],
       puts := ["T"], gives := [],
       body := [.call (if ordered then "#transition#S#cycle" else "#transition#S#a")
         (if ordered then [.val (.lit 0), .val (.lit 0), .val (.lit 1), .val (.lit 1),
           .val (.lit 0), .val (.tab "T" "s" (.lit 0))] else [.val (.lit 0)])],
       ret := .val (.lit 23) }, transitionFunction ordered]
  zustaende := [{ name := "S", stufen := (if ordered then [] else ["Idle", "Busy"]), paare := (if ordered then [] else [(0, 1)]), transitions := [transition ordered] }]
  regiert := [("T", "s", "S")]

end Data

def text : String :=
  "module transition_probe { table T count 2 { slot { s : u32 in 0 .. 2, } } state S { transition a { s : Idle -> Busy } requires true effects { writes T.slots } } impl fn main() -> u64 in 0 .. 100 effects { writes T.slots } { transition T.slots[0].s : Idle -> Busy; return 23; } }"

def candidate : Except String (Emitted text 64) := emit text 64


theorem candidate_refused : candidate.toOption.isSome = false := by
  kernel_rfl


theorem model_present : (sourceModel text).toOption.isSome = true := by kernel_rfl
def model : Σ u : UProg, Programm (declOf u) := (sourceModel text).toOption.get model_present
theorem data_present : (sourceData text).toOption.isSome = true := by kernel_rfl
def input : List SItemTief × UProg := (sourceData text).toOption.get data_present
def unit : UProg := { Data.sourceUnit false with merk := input.2.merk }
theorem data_unit : input.2 = unit := by kernel_rfl


theorem model_unit : model.1 = unit :=
  (sourceModel_unit text input model (except_ok_get data_present) (except_ok_get model_present)).trans data_unit

def program : Programm (declOf unit) := model_unit ▸ model.2
def mainIndex : Fin unit.fns.length := ⟨0, by decide +kernel⟩
def transitionIndex : Fin unit.fns.length := ⟨1, by decide +kernel⟩


attribute [local irreducible] unit

theorem field_types (table : (declOf unit).Tab) (field : (declOf unit).Feld table) :
    (declOf unit).typ table field = .int 0 2 := by
  have checked : (List.finRange unit.tabs.length).all (fun t =>
      (List.finRange (fieldCount unit t)).all (fun f =>
        decide ((declOf unit).typ t f = .int 0 2))) = true := by kernel_rfl
  exact of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp checked table (List.mem_finRange _)) field (List.mem_finRange _))

theorem globals_empty : unit.globs = [] := by kernel_rfl

theorem main_params : (declOf unit).params mainIndex = [] := by kernel_rfl

theorem transition_params : (declOf unit).params transitionIndex = [.int 0 1] := by
  kernel_rfl

def mainArguments : Env (declOf unit) ((declOf unit).params mainIndex) :=
  main_params.symm ▸ Env.nil

def busyWorld : World (declOf unit) where
  slots := fun table index field =>
    (field_types table field).symm ▸
      (show Wert (declOf unit) (.int 0 2) from ⟨1, by decide, by decide⟩)
  globs := fun g => Fin.elim0 (Fin.cast (congrArg List.length globals_empty) g)
  spur := []

def transitionArguments : Env (declOf unit) ((declOf unit).params transitionIndex) :=
  transition_params.symm ▸ .cons (τ := .int 0 1) ⟨0, by decide, by decide⟩ .nil

/-- The caller admits Busy=1, while its real transition callee requires Idle=0. -/

theorem counterexample_zeuge : ReqAmEintritt program mainIndex busyWorld mainArguments ∧
    ¬ ReqAmEintritt program transitionIndex busyWorld transitionArguments := by
  constructor
  · unfold ReqAmEintritt
    kernel_rfl
  · have blocked : wahr? (eval busyWorld (program.requires transitionIndex)
        busyWorld transitionArguments) = false := by kernel_rfl
    intro accepted
    unfold ReqAmEintritt at accepted
    rw [blocked] at accepted
    cases accepted


/-- Both producer premises hold jointly on two real source functions. -/
theorem sourceModel_unit_zeuge : sourceData text = .ok input ∧
    (sourceModel text).toOption.isSome = true ∧ model.1 = input.2 ∧
    input.2.fns.length = 2 := by
  refine ⟨except_ok_get data_present, model_present,
    sourceModel_unit text input model (except_ok_get data_present) (except_ok_get model_present), ?_⟩
  rw [data_unit]
  kernel_rfl

namespace Ordered

def text : String :=
  "module ordered_transition_probe { table T count 2 { slot { s : u32 in 0 .. 2, } } state S { transition cycle { T.slots[0].s : 0 -> 1, T.slots[1].s : 0 -> T.slots[0].s } requires true effects { writes T.slots } } impl fn main() -> u64 in 0 .. 100 effects { writes T.slots } { cycle(); return 23; } }"

theorem model_present : (sourceModel text).toOption.isSome = true := by kernel_rfl
def model : Σ u : UProg, Programm (declOf u) := (sourceModel text).toOption.get model_present
theorem data_present : (sourceData text).toOption.isSome = true := by kernel_rfl
def input : List SItemTief × UProg := (sourceData text).toOption.get data_present
def unit : UProg := { Data.sourceUnit true with merk := input.2.merk }
theorem data_unit : input.2 = unit := by kernel_rfl


-- Retain the source's original cache together with the exact data fields.
theorem model_unit : model.1 = unit :=
  (sourceModel_unit text input model (except_ok_get data_present) (except_ok_get model_present)).trans data_unit

def program : Programm (declOf unit) := model_unit ▸ model.2
def mainIndex : Fin unit.fns.length := ⟨0, by decide +kernel⟩
def transitionIndex : Fin unit.fns.length := ⟨1, by decide +kernel⟩

attribute [local irreducible] unit

theorem field_types (table : (declOf unit).Tab) (field : (declOf unit).Feld table) :
    (declOf unit).typ table field = .int 0 2 := by
  have checked : (List.finRange unit.tabs.length).all (fun t =>
      (List.finRange (fieldCount unit t)).all (fun f =>
        decide ((declOf unit).typ t f = .int 0 2))) = true := by kernel_rfl
  exact of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp checked table (List.mem_finRange _)) field (List.mem_finRange _))

theorem globals_empty : unit.globs = [] := by kernel_rfl

theorem main_params : (declOf unit).params mainIndex = [] := by kernel_rfl

theorem transition_params : (declOf unit).params transitionIndex = [.int 0 1, .int 0 2, .int 0 2, .int 0 1, .int 0 2, .int 0 2] := by
  kernel_rfl

def mainArguments : Env (declOf unit) ((declOf unit).params mainIndex) :=
  main_params.symm ▸ Env.nil

def busyWorld : World (declOf unit) where
  slots := fun table index field =>
    (field_types table field).symm ▸
      (show Wert (declOf unit) (.int 0 2) from ⟨if index = 0 then 0 else 1, by split <;> decide, by split <;> decide⟩)
  globs := fun g => Fin.elim0 (Fin.cast (congrArg List.length globals_empty) g)
  spur := []

def transitionArguments : Env (declOf unit) ((declOf unit).params transitionIndex) :=
  transition_params.symm ▸ .cons (τ := .int 0 1) ⟨0, by decide, by decide⟩
    (.cons (τ := .int 0 2) ⟨0, by decide, by decide⟩
      (.cons (τ := .int 0 2) ⟨1, by decide, by decide⟩
        (.cons (τ := .int 0 1) ⟨1, by decide, by decide⟩
          (.cons (τ := .int 0 2) ⟨0, by decide, by decide⟩
            (.cons (τ := .int 0 2) ⟨0, by decide, by decide⟩ .nil)))))

/-- Outside the decidable fragment: the complete transition parameter product. -/
theorem function_fragment_refusal :
    (Vertraege.Pruefer.checkFunction program (Cover.Differenz.sperrFamilie unit)
      (Cover.Differenz.sperrQuellen unit) {} none transitionIndex).map (fun _ => ()) =
      .error (.unsupported "writer parameter product exceeds the VC expansion budget") := by
  kernel_rfl

attribute [local irreducible] program Vertraege.Pruefer.checkFunction Invarianten.Pruefer.collect

/-- One refused real member blocks the actual unchanged contract collector. -/
theorem contracts_refused : Vertraege.Pruefer.KontrakteGeprueftB program
    (Cover.Differenz.sperrFamilie unit) (List.finRange unit.fns.length)
    (Cover.Differenz.sperrQuellen unit) = false := by
  have rejected : (Vertraege.Pruefer.checkFunction program (Cover.Differenz.sperrFamilie unit)
      (Cover.Differenz.sperrQuellen unit) {} none transitionIndex).toOption.isSome = false := by
    have reason := function_fragment_refusal
    cases h : Vertraege.Pruefer.checkFunction program (Cover.Differenz.sperrFamilie unit)
        (Cover.Differenz.sperrQuellen unit) {} none transitionIndex with
    | error cause => rfl
    | ok checked => simp only [h, Except.map, reduceCtorEq] at reason
  change (Invarianten.Pruefer.collect (List.finRange unit.fns.length)
    (Vertraege.Pruefer.ContractDuties program (Cover.Differenz.sperrFamilie unit))
    (fun f => Vertraege.Pruefer.checkFunction program (Cover.Differenz.sperrFamilie unit)
      (Cover.Differenz.sperrQuellen unit) {} none f)).toOption.isSome = false
  cases result : Invarianten.Pruefer.collect (List.finRange unit.fns.length)
      (Vertraege.Pruefer.ContractDuties program (Cover.Differenz.sperrFamilie unit))
      (fun f => Vertraege.Pruefer.checkFunction program (Cover.Differenz.sperrFamilie unit)
        (Cover.Differenz.sperrQuellen unit) {} none f) with
  | error cause => rfl
  | ok checked =>
      have each := Vertraege.Pruefer.RefusalWitness.collect_each (List.finRange unit.fns.length)
        (Vertraege.Pruefer.ContractDuties program (Cover.Differenz.sperrFamilie unit))
        (fun f => Vertraege.Pruefer.checkFunction program (Cover.Differenz.sperrFamilie unit)
          (Cover.Differenz.sperrQuellen unit) {} none f)
        (by rw [result]; rfl) transitionIndex (List.mem_finRange _)
      rw [rejected] at each
      cases each

/-- The exact restored source program cannot pass production admission. -/
theorem checker_refused : OldSource.accepts unit program mainIndex ≠ .ok true :=
  checker_refused_of_contracts unit program mainIndex contracts_refused

/-- The typed state [0,1] satisfies main's precondition and violates cycle's. -/
theorem counterexample_zeuge : ReqAmEintritt program mainIndex busyWorld mainArguments ∧
    ¬ ReqAmEintritt program transitionIndex busyWorld transitionArguments := by
  constructor
  · unfold ReqAmEintritt
    kernel_rfl
  · have blocked : wahr? (eval busyWorld (program.requires transitionIndex)
        busyWorld transitionArguments) = false := by kernel_rfl
    intro accepted
    unfold ReqAmEintritt at accepted
    rw [blocked] at accepted
    cases accepted

/-- The admission rule has an actual refused two-function source as its witness. -/
private theorem checker_refused_of_contracts_zeuge :
    unit.fns.length = 2 ∧
    Vertraege.Pruefer.KontrakteGeprueftB program (Cover.Differenz.sperrFamilie unit)
      (List.finRange unit.fns.length) (Cover.Differenz.sperrQuellen unit) = false ∧
    OldSource.accepts unit program mainIndex ≠ .ok true :=
  ⟨by kernel_rfl, contracts_refused, checker_refused⟩

end Ordered


end Gabbro.Stage0.TransitionContractWitness
