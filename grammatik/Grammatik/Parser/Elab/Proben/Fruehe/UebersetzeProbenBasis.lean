/-
  File:      Grammatik/Parser/UebersetzeProben.lean
  Subject:   Sieve (a), parser lane: witnesses and planted defects for the widenings of the
             elaborator and the generic lowering.

  Every probe runs the WHOLE pipeline `uebersetzeAllg` on a small source text and names the stage
  where it stops (`stufe`). A WITNESS is a source that reaches `OK`; a PLANTED DEFECT is a source
  one token away that must stop, at the stage and with the message the widening promises. A
  widening whose defect also passes would be a widening that let something through.

  The texts are short on purpose: the kernel decodes a `String` per proof (O13).
  Pipeline certificates stop at elaboration and check the actual lowering phases separately.
  The source strings and all expected stage diagnostics stay pinned below.
  Corpus programs are pinned as characters in the chain instances, not here.

  WALL 1 (2026-09-30): units WITHOUT a table; integer arithmetic (`+`, `-`, `*`) in values, with
  the range of the result computed like `Expr.add`/`sub`/`mul` carry it; the built-in widths
  `uN`/`iN`; an omitted `effects` (derived by the checker) read as the empty set.
-/
module
public import Grammatik.Parser.Elab.UebersetzePipeline
-- The shared phase executes these gates even when a source declares no checks or static parameters.
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil12
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
import all Grammatik.Parser.Elab.Generic.StaticConformance
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest1
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a
import all Grammatik.Parser.Elab.UebersetzeAllg3.Measures.Export
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


namespace Gabbro.Grammatik.Parser.UebersetzeProben

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option maxRecDepth 100000

/-- The stage of `uebersetzeAllg` that stops a source (`OK` when none does). -/
def stufe (s : String) : String :=
  match lex s with
  | .error _ => "lex"
  | .ok toks =>
    match parseTopTief toks with
    | .error e => "parse: " ++ e
    | .ok items =>
      match elabU (pre108 items) with
      | .error e => "elab: " ++ e
      | .ok u =>
        match lowerAllg u with
        | .error e => "lower: " ++ e
        | .ok _ => "OK"

-- Use the canonical logarithm equation rather than its large internal recursor fuel.
attribute [local cbv_eval] Nat.log2_def

/-- A proof-only continuation pins every frontend phase without evaluating a lowered program. -/
def Frontend (source : String) (unit : UProg) : Prop :=
  ∀ after : UProg → String,
    (match lex source with
    | .error _ => "lex"
    | .ok tokens => match parseTopTief tokens with
      | .error error => "parse: " ++ error
      | .ok items => match elabU (pre108 items) with
        | .error error => "elab: " ++ error
        | .ok actual => after actual) = after unit

theorem stufe_after {source : String} {unit : UProg} {expected : String}
    (front : Frontend source unit)
    (lowered : (match lowerAllg unit with
      | .error error => "lower: " ++ error | .ok _ => "OK") = expected) :
    stufe source = expected :=
  (front (fun actual => match lowerAllg actual with
    | .error error => "lower: " ++ error | .ok _ => "OK")).trans lowered

/-- All absent source measures produce empty tuples, so the actual cycle-length gate passes
    independently of the program bodies. Every function still passes lowerEach and contractGate. -/
theorem lowering_ok (unit : UProg)
    (invariants : lowerInvs unit (List.finRange unit.invs.length) = .ok ())
    (functions : lowerEach unit (List.finRange unit.fns.length) = .ok ())
    (contracts : contractGate unit = true)
    (measures : (Measures.lowerMeasures unit).toOption.isSome = true)
    (absent : ∀ fn ∈ unit.fns, fn.decreases = none) :
    (lowerAllg unit).toOption.isSome = true := by
  let exported := (Measures.lowerMeasures unit).toOption.get measures
  have measured : Measures.lowerMeasures unit = .ok exported := except_ok_get measures
  have checked (program : Programm (declOf unit)) :
      (Measures.checkedProgram unit program).toOption.isSome = true := by
    have cycles : Measures.cycleLengths unit program exported.mass = true := by
      unfold Measures.cycleLengths
      apply List.all_eq_true.mpr
      intro f _
      apply List.all_eq_true.mpr
      intro g _
      have empty (i : (declOf unit).Fn) : exported.mass i = [] :=
        Measures.lowerMeasures_absent unit exported i
          (absent (fnAt unit i) (List.get_mem unit.fns i))
      rw [empty f, empty g]
      change (!zykS program (List.finRange unit.fns.length) f g || true) = true
      exact Bool.or_true _
    unfold Measures.checkedProgram
    rw [measured]
    dsimp only
    split
    · rfl
    · contradiction
  unfold lowerAllg
  split
  · rename_i error failed
    rw [invariants] at failed
    cases failed
  · split
    · rename_i error failed
      rw [functions] at failed
      cases failed
    · split
      · exact checked _
      · contradiction

theorem lowering_error (unit : UProg) (error : String)
    (invariants : lowerInvs unit (List.finRange unit.invs.length) = .ok ())
    (functions : lowerEach unit (List.finRange unit.fns.length) = .error error) :
    lowerAllg unit = .error error := by
  unfold lowerAllg
  split
  · rename_i message failed
    rw [invariants] at failed
    cases failed
  · split
    · rename_i message failed
      rw [functions] at failed
      have same : error = message := Except.error.inj failed
      subst message
      rfl
    · rename_i succeeded
      rw [functions] at succeeded
      cases succeeded

theorem stufe_ok {source : String} {unit : UProg} (front : Frontend source unit)
    (lowered : (lowerAllg unit).toOption.isSome = true) : stufe source = "OK" := by
  apply stufe_after front
  rw [except_ok_get lowered]

theorem stufe_error {source : String} {unit : UProg} {error : String}
    (front : Frontend source unit) (lowered : lowerAllg unit = .error error) :
    stufe source = "lower: " ++ error := by
  apply stufe_after front
  rw [lowered]

/-- Shared fixture construction only; Frontend certifies equality with the complete actual unit. -/
def scalarUnit (name : String) (parameters : List (String × Ty))
    (result : Int × Int) (value : USide) : UProg :=
  { tabs := []
    locks := []
    fns := [
      { name := name
        params := parameters
        kinds := parameters.map (fun _ => .int)
        res := some result
        held := []
        puts := []
        gives := []
        body := []
        ret := .val value }] }

end Gabbro.Grammatik.Parser.UebersetzeProben
