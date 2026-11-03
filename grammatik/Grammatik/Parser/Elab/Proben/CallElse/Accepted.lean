module

public import Grammatik.Parser.Elab.Proben.CallElse.Parser
public import Grammatik.Parser.Elab.UebersetzePipeline
public import Grammatik.Parser.Cover.Differenz
public import Grammatik.Parser.Cover.Mitglieder

@[expose] public section
namespace Gabbro.Grammatik.Parser.CallElseProben
open Uebersetze UebersetzeAllg UebersetzeAllg2

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

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
    (Cover.mitglieder u program functions).contains "Stmt.axiomCallElse"

theorem named_accepted_zeuge : acceptedText namedSource = true := by decide +kernel
theorem unnamed_accepted_zeuge : acceptedText unnamedSource = true := by decide +kernel

theorem canonical_handler_zeuge : hasCanonicalHandler namedSource = true := by decide +kernel

/-- Exercise the continuing-block path as well as function-body lowering. -/
def nestedSource : String := foreignHead ++
  "impl fn f() -> u32 in 0 .. 9 { if true { rd(1) else { return 0; }; } return 1; }"

theorem nested_accepted_zeuge : acceptedText nestedSource = true := by decide +kernel

end Gabbro.Grammatik.Parser.CallElseProben
