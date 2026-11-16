/- Joint witness of the bridge from the compiler's check to the goal checker (premise (a)).

    A real Stage-0 source: `main` calls a second function (`countdown`, with a declared
    measure). The compiler accepts it (`compiled`), the unit is certifiable, has no declared or
    run-time root, `main` has a typed start environment (`Senke.mainEnv`, the image's), and the
    bridge gives the goal checker's `true` on the judged `Einheit` that starts `main` alone.
    The witness includes the actual start-data gates for every initial memory and foreign
    answer family, without assuming a successful checker result. -/
module
public import Stage0.CompilerPruefer
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

namespace Gabbro.Stage0.GoalCheckerWitness
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- `main` calls `countdown`; `countdown` recurses under its declared measure. -/
def characters : List Char :=
  ("type Small = u8 in 0 .. 1; ".toList ++
   "impl fn countdown(n : Small) decreases n ".toList ++
   "{ if n > 0 { countdown(0); } else { } return; } ".toList ++
   "impl fn main() { countdown(1); return; }".toList)

def text : String := String.ofList characters

/-- The compiler accepts the source; `accepts` with `main` among the judged starts is part of it. -/
theorem compiled : (compile text).toOption.isSome = true := by kernel_rfl

def result : Compiled text := (compile text).toOption.get compiled

/-- Non-degenerate: two functions, the entry is `main`. -/
theorem function_names : result.unit.fns.map (·.name) = ["countdown", "main"] := by kernel_rfl

theorem entry_name : (fnAt result.unit result.main).name = "main" := by kernel_rfl

/-- The unit has no arena table, no declared check and no accumulator storage. -/
theorem certifiable : OldSource.zertifizierbar result.unit = true := by kernel_rfl

/-- A plain `main`: no declared root and no run-time root. -/
theorem no_roots : result.unit.roots = [] := by kernel_rfl

theorem no_started : result.unit.gestartet = [] := by kernel_rfl

/-- `main` has the image's typed start environment. -/
theorem main_env :
    (Senke.mainEnv (D := declOf result.unit) ((declOf result.unit).params result.main)).isSome =
      true := by kernel_rfl

def args : Env (declOf result.unit) ((declOf result.unit).params result.main) :=
  (Senke.mainEnv (D := declOf result.unit) ((declOf result.unit).params result.main)).get main_env

/-- This source has no memory predicates or locks, and its only start has
    requires true. The actual data gate therefore succeeds for every memory
    and foreign-answer family; recursive descent is still checked. -/
theorem start_checked (Q : AxEns (declOf result.unit)) (sp : Speicher (declOf result.unit)) :
    Zielsatz.unitStartGeprueftB
      (OldSource.einheitDer result.unit result.program Q sp result.main args [] [] [])
      (List.finRange result.unit.fns.length) (List.finRange result.unit.locks.length) = true := by
  kernel_rfl

/-- All bridge premises hold jointly on a compiled recursive program, for
    every foreign-answer family and initial memory, without a checker premise. -/
theorem bridge_zeuge (Q : AxEns (declOf result.unit)) (sp : Speicher (declOf result.unit)) :
    Zielsatz.akzeptiertX_pruefer.akzeptiert
      (OldSource.einheitDer result.unit result.program Q sp result.main args [] [] [])
      (List.finRange result.unit.fns.length) (List.finRange result.unit.locks.length)
      ((List.finRange result.unit.tabs.length).map Sum.inl ++
        (List.finRange result.unit.globs.length).map Sum.inr) = true :=
  result.goal_checker_main Q sp args certifiable no_roots no_started (start_checked Q sp)

/-- The general bridge on the same unit, with the derived (empty) check list. -/
theorem bridge_checks_zeuge (Q : AxEns (declOf result.unit)) (sp : Speicher (declOf result.unit)) :
    Zielsatz.akzeptiertX_pruefer.akzeptiert
      (OldSource.einheitDer result.unit result.program Q sp result.main args [] [] [])
      (List.finRange result.unit.fns.length) (List.finRange result.unit.locks.length)
      ((List.finRange result.unit.tabs.length).map Sum.inl ++
        (List.finRange result.unit.globs.length).map Sum.inr) = true :=
  result.goal_checker Q sp args [] [] [] certifiable
    (OldSource.uCheckDecls_zertifizierbar result.unit certifiable)
    (OldSource.roots_leer result.unit no_roots) (OldSource.gestartet_leer result.unit no_started)
    (start_checked Q sp)

end Gabbro.Stage0.GoalCheckerWitness
