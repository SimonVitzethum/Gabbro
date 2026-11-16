module
public import Stage0.SourceWitness
public import Grammatik.Parser.Elab.UebersetzePipeline
import Grammatik.Kern.Taktik.KernelRfl
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

/-- Recover the actual source contracts before the rejecting admission step. -/
def sourceModel (source : String) : Except String (Σ u : UProg, Programm (declOf u)) := do
  let parsed ← Frontend.source source {}
  let declarations := pre108 parsed.prepared.elaborierbar
  let unit ← (Frontend.elabWithScopes declarations
    parsed.scopes.values parsed.scopes.types parsed.scopes.functions
    (Frontend.tableWithEmpty parsed.scopes.values parsed.scopes.types)
    (widths := parsed.scopes.widths)).bind (Profil.selectUnit {})
  let (raw, _) ← lowerAllg unit
  let program ← OldSource.restore declarations unit raw
  return ⟨unit, program⟩

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
  zustaende := [{ name := "S", stufen := if ordered then [] else ["Idle", "Busy"],
    paare := if ordered then [] else [(0, 1)], transitions := [transition ordered] }]
  regiert := [("T", "s", "S")]

end Data

def text : String :=
  "module transition_probe { table T count 2 { slot { s : u32 in 0 .. 2, } } state S { transition a { s : Idle -> Busy } requires true effects { writes T.slots } } impl fn main() -> u64 in 0 .. 100 effects { writes T.slots } { transition T.slots[0].s : Idle -> Busy; return 23; } }"

def candidate : Except String (Emitted text 64) := emit text 64

#eval IO.FS.writeFile "../.scratch-agent/transition-progress" "A before refusal"

theorem candidate_refused : candidate.toOption.isSome = false := by
  kernel_rfl

#eval IO.FS.writeFile "../.scratch-agent/transition-progress" "A before model"

theorem model_present : (sourceModel text).toOption.isSome = true := by kernel_rfl
def model : Σ u : UProg, Programm (declOf u) := (sourceModel text).toOption.get model_present
def unit : UProg := Data.sourceUnit false

#eval IO.FS.writeFile "../.scratch-agent/transition-progress" "before unit equality false"

theorem model_unit : model.1 = unit := by kernel_rfl

def program : Programm (declOf unit) := model_unit ▸ model.2
def mainIndex : Fin unit.fns.length := ⟨0, by decide +kernel⟩
def transitionIndex : Fin unit.fns.length := ⟨1, by decide +kernel⟩

#eval IO.FS.writeFile "../.scratch-agent/transition-progress" "A before world"

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
#eval IO.FS.writeFile "../.scratch-agent/transition-progress" "A before counterexample"

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

#eval IO.FS.writeFile "../.scratch-agent/transition-progress" "A complete"

namespace Ordered

def text : String :=
  "module ordered_transition_probe { table T count 2 { slot { s : u32 in 0 .. 2, } } state S { transition cycle { T.slots[0].s : 0 -> 1, T.slots[1].s : 0 -> T.slots[0].s } requires true effects { writes T.slots } } impl fn main() -> u64 in 0 .. 100 effects { writes T.slots } { cycle(); return 23; } }"

def candidate : Except String (Emitted text 64) := emit text 64

theorem candidate_refused : candidate.toOption.isSome = false := by
  kernel_rfl

theorem model_present : (sourceModel text).toOption.isSome = true := by kernel_rfl
def model : Σ u : UProg, Programm (declOf u) := (sourceModel text).toOption.get model_present
def unit : UProg := Data.sourceUnit true

#eval IO.FS.writeFile "../.scratch-agent/transition-progress" "before unit equality true"

theorem model_unit : model.1 = unit := by kernel_rfl

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

end Ordered

end Gabbro.Stage0.TransitionContractWitness
