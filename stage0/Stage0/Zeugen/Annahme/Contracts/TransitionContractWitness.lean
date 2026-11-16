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

set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-- Recover the actual source contracts before the rejecting admission step. -/
def sourceModel (source : String) : Except String (Σ u : UProg, Programm (declOf u)) := do
  let lowered ← uebersetzeAllg source
  let tokens ← match lex source with
    | .error _ => .error "lex"
    | .ok tokens => .ok tokens
  let items ← parseTopTief tokens
  let program ← OldSource.restore (pre108 items) lowered.1 lowered.2.1
  return ⟨lowered.1, program⟩

def text : String :=
  "module transition_probe { table T count 2 { slot { s : u32 in 0 .. 2, } } state S { transition a { s : Idle -> Busy } requires true effects { writes T.slots } } impl fn main() -> u64 in 0 .. 100 effects { writes T.slots } { transition T.slots[0].s : Idle -> Busy; return 23; } }"

def candidate : Except String (Emitted text 64) := emit text 64

theorem candidate_refused : candidate = .error
    "function contract: false VC; counterexample in observation order = [1]; parameters = []" := by
  kernel_rfl

theorem model_present : (sourceModel text).toOption.isSome = true := by kernel_rfl
def model : Σ u : UProg, Programm (declOf u) := (sourceModel text).toOption.get model_present
abbrev unit := model.1
def program : Programm (declOf unit) := model.2
def mainIndex : Fin unit.fns.length := ⟨0, by decide +kernel⟩
def transitionIndex : Fin unit.fns.length := ⟨1, by decide +kernel⟩

def busyWorld : World (declOf unit) where
  slots := fun ⟨table, ht⟩ ⟨column, hc⟩ _ => by
    have tableZero : table = 0 := by have bound : table < 1 := ht; omega
    subst table
    have columnZero : column = 0 := by have bound : column < 1 := hc; omega
    subst column
    exact ⟨1, by decide, by decide⟩
  globs := fun g => Fin.elim0 (show Fin 0 from g)
  spur := []

def transitionArguments : Env (declOf unit) ((declOf unit).params transitionIndex) :=
  .cons (τ := .int 0 1) ⟨0, by decide, by decide⟩ .nil

/-- The caller admits Busy=1, while its real transition callee requires Idle=0. -/
theorem counterexample_zeuge : ReqAmEintritt program mainIndex busyWorld .nil ∧
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

namespace Ordered

def text : String :=
  "module ordered_transition_probe { table T count 2 { slot { s : u32 in 0 .. 2, } } state S { transition cycle { T.slots[0].s : 0 -> 1, T.slots[1].s : 0 -> T.slots[0].s } requires true effects { writes T.slots } } impl fn main() -> u64 in 0 .. 100 effects { writes T.slots } { cycle(); return 23; } }"

def candidate : Except String (Emitted text 64) := emit text 64

theorem candidate_refused : candidate = .error
    "function contract: false VC; counterexample in observation order = [0, 1]; parameters = []" := by
  kernel_rfl

theorem model_present : (sourceModel text).toOption.isSome = true := by kernel_rfl
def model : Σ u : UProg, Programm (declOf u) := (sourceModel text).toOption.get model_present
abbrev unit := model.1
def program : Programm (declOf unit) := model.2
def mainIndex : Fin unit.fns.length := ⟨0, by decide +kernel⟩
def transitionIndex : Fin unit.fns.length := ⟨1, by decide +kernel⟩

def busyWorld : World (declOf unit) where
  slots := fun ⟨table, ht⟩ ⟨column, hc⟩ index => by
    have tableZero : table = 0 := by have bound : table < 1 := ht; omega
    subst table
    have columnZero : column = 0 := by have bound : column < 1 := hc; omega
    subst column
    exact ⟨if index.val = 0 then 0 else 1, by split <;> decide, by split <;> decide⟩
  globs := fun g => Fin.elim0 (show Fin 0 from g)
  spur := []

def transitionArguments : Env (declOf unit) ((declOf unit).params transitionIndex) :=
  .cons (τ := .int 0 1) ⟨0, by decide, by decide⟩
    (.cons (τ := .int 0 2) ⟨0, by decide, by decide⟩
      (.cons (τ := .int 0 2) ⟨1, by decide, by decide⟩
        (.cons (τ := .int 0 1) ⟨1, by decide, by decide⟩
          (.cons (τ := .int 0 2) ⟨0, by decide, by decide⟩
            (.cons (τ := .int 0 2) ⟨0, by decide, by decide⟩ .nil)))))

/-- The typed state [0,1] satisfies main's precondition and violates cycle's. -/
theorem counterexample_zeuge : ReqAmEintritt program mainIndex busyWorld .nil ∧
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
