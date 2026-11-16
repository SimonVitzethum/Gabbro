module

public import Grammatik.Parser.Elab.Proben.CallElse.Parser
public import Grammatik.Parser.Elab.UebersetzePipeline
public import Grammatik.Parser.Cover.Differenz
public import Grammatik.Parser.Cover.Mitglieder
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
namespace Gabbro.Grammatik.Parser.CallElseProben
open Uebersetze UebersetzeAllg UebersetzeAllg2 Zielsatz

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option Elab.async false

def foreignHead : String :=
  "reason G { Weg = 1 \"failed\" exhaustive } " ++
  "extern fn rd(x: u32 in 0 .. 9) -> u32 in 0 .. 9 or G effects { pure }; "

/-- The success answer is discarded. The original local survives both outcomes;
    the reason is available only in the terminating failure handler. -/
def namedSource : String := foreignHead ++
  "impl fn f() -> u32 in 0 .. 9 { let kept = 1; rd(kept) else (reason) { " ++
  "match reason { Weg => { return 0; } } return 0; }; return kept; }"

def unnamedSource : String := foreignHead ++
  "impl fn f() -> u32 in 0 .. 9 { let kept = 1; rd(kept) else { return 0; }; return kept; }"

/-- The actual source pipeline and the goal theorem's checker, enumerating the
    unit's functions. These fixtures have no locks, carriers or thread starts. -/
def acceptedText (text : String) : Bool :=
  match uebersetzeAllg text with
  | .error _ => false
  | .ok ⟨u, program, functions⟩ =>
    AkzeptiertX program (Cover.Differenz.sperrFamilie u) functions [] [] []

def hasCanonicalHandler (text : String) : Bool :=
  match uebersetzeAllg text with
  | .error _ => false
  | .ok ⟨u, program, functions⟩ =>
    (Cover.Mitglieder.mitglieder u program functions).contains "Stmt.axiomCallElse"

/-- Preserve the strict checker's actual refusal for the unchanged source. -/
def refusalReason (text : String) : Option String :=
  match uebersetzeAllg text with
  | .error cause => some cause
  | .ok ⟨u, program, functions⟩ =>
    match Vertraege.Pruefer.checkContracts program (Cover.Differenz.sperrFamilie u)
        functions (fun _ => none) with
    | .error cause => some cause.message
    | .ok _ => none

/-- The reason dispatch still needs a quantified oracle/poststate WP. -/
theorem named_refused_zeuge : acceptedText namedSource = false ∧
    refusalReason namedSource = some
      "unsupported invariant constructor: contract oracle call needs quantified answer and poststate observations" := by
  constructor <;> kernel_rfl

/-- Both typed oracle outcomes retain the original local and return safely. -/
theorem unnamed_accepted_zeuge : acceptedText unnamedSource = true ∧
    refusalReason unnamedSource = none := by
  constructor <;> kernel_rfl

theorem canonical_handler_zeuge : hasCanonicalHandler namedSource = true := by kernel_rfl

/-- Exercise the continuing-block path as well as function-body lowering. -/
def nestedSource : String := foreignHead ++
  "impl fn f() -> u32 in 0 .. 9 { if true { rd(1) else { return 0; }; } return 1; }"

theorem nested_accepted_zeuge : acceptedText nestedSource = true ∧
    refusalReason nestedSource = none := by
  constructor <;> kernel_rfl

end Gabbro.Grammatik.Parser.CallElseProben
