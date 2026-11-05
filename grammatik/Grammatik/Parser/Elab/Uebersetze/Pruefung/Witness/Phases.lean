module

public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Export
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Ableitung
public import Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a
public import Grammatik.Parser.Cover.Differenz
public import Grammatik.Zielsatz.Atomar.AtomarAkzeptiert
public import Grammatik.Zielsatz.Kern.Akzeptiert.CheckDecide
import Grammatik.Parser.Elab.UebersetzePipeline
import all Grammatik.Parser.Lex.Lexer.Teil1
import all Grammatik.Parser.Elab.Uebersetze.Folds.Expressions
import all Grammatik.Parser.Elab.Uebersetze.Folds.Expansion
import all Grammatik.Parser.Elab.Uebersetze.Folds.FloatLiterals
import all Grammatik.Parser.Elab.Uebersetze.Branches
import all Grammatik.Parser.Elab.Uebersetze.LoopHeaders
import all Grammatik.Parser.Elab.Uebersetze.Records.Records
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil3
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil4
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil5
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil5Rest
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil7
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil8
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil9
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil10
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil1
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil2
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil3
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil3Values
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil4
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil5
import all Grammatik.Parser.Elab.UebersetzeAllg3.Body
import all Grammatik.Parser.Elab.UebersetzeAllg3.Ende
import all Grammatik.Parser.Elab.UebersetzeAllg3.Kopf
import all Grammatik.Parser.Elab.UebersetzeAllg3.Seq
import all Grammatik.Parser.Elab.UebersetzeAllg3.Stufe
import all Grammatik.Parser.Elab.UebersetzeAllg3.Struct
import all Grammatik.Parser.Elab.UebersetzeAllg3.Transition
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest1
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a
import all Grammatik.Parser.Elab.UebersetzeAllg3.Measures.Export
import all Grammatik.Parser.Elab.Generic.Signatures
import all Grammatik.Parser.Elab.Generic.StaticConformance
import all Init.Data.Repr
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
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
import all Init.Data.String.ToSlice
import all Init.Data.String.Defs
import all Init.Data.String.Basic
import all Init.Data.String.Extra
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Legacy
import all Init.Data.String.Termination
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Export
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Ableitung
import all Grammatik.Parser.Elab.Uebersetze.Einheit.Elaboration
import all Grammatik.Parser.Elab.Uebersetze.Einheit.Signatures
import all Grammatik.Parser.Elab.Uebersetze.Akku.ProbenPhases

public section
namespace Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

-- These are equations of the actual recording traversal, not a second recorder.
-- Match the fuel before selecting a callback, keeping its large numeral opaque.
private theorem recording_block (heads : List UFnKopf) (check : SCheck)
    (fuel : Nat) (ctx : UCtx) (point : Nat) (statements : List SAnw) (value : SExpr) :
    recordCheckCode heads check fuel ctx point
      (.block statements (some (.ret (some value)))) = match fuel with
      | 0 => .error "check recording expansion exhausted"
      | n + 1 => (do
        let (statements, ctx, reporters, extraHeads, point) ←
          recordCheckStatements heads check n ctx point statements
        let (body, reporter, head) ← recordCheckReturn ctx check point value
        match body with
        | .block recorded ending =>
          pure (.block (statements ++ recorded) ending, reporters ++ [reporter],
            extraHeads ++ [head], point + 1)
        | _ => .error "check reporter expansion is not a block") := by
  cases fuel <;> rfl

private theorem recording_bind (heads : List UFnKopf) (check : SCheck)
    (fuel : Nat) (ctx : UCtx) (point : Nat) (mutable : Bool) (name : String)
    (ty : Option STyp) (value : SExpr) :
    recordCheckCode heads check fuel ctx point (.bind mutable name ty value) = match fuel with
      | 0 => .error "check recording expansion exhausted"
      | _ + 1 => .ok (.bind mutable name ty value, [], [], point) := by
  cases fuel <;> rfl

private theorem recording_nil (heads : List UFnKopf) (check : SCheck)
    (fuel : Nat) (ctx : UCtx) (point : Nat) :
    recordCheckStatements heads check fuel ctx point [] = match fuel with
      | 0 => .error "check recording expansion exhausted"
      | _ + 1 => .ok ([], ctx, [], [], point) := by
  cases fuel <;> rfl

private theorem recording_cons (heads : List UFnKopf) (check : SCheck)
    (fuel : Nat) (ctx : UCtx) (point : Nat) (statement : SAnw) (rest : List SAnw) :
    recordCheckStatements heads check fuel ctx point (statement :: rest) = match fuel with
      | 0 => .error "check recording expansion exhausted"
      | n + 1 => (do
        let (transformed, reporters, extraHeads, point) ←
          recordCheckCode heads check n ctx point statement
        let (_, nextCtx) ← uAnwReihe ctx.tabs heads 1000000 ctx [statement]
        let (rest, endCtx, more, moreHeads, point) ←
          recordCheckStatements heads check n nextCtx point rest
        let recorded := match statement, transformed with
          | .ret _, .block before (some (.ret result)) => before ++ [.ret result]
          | _, _ => [transformed]
        pure (recorded ++ rest, endCtx, reporters ++ more, extraHeads ++ moreHeads, point)) := by
  cases fuel <;> rfl

private theorem sample_binary (bindings : List (SExpr × SExpr)) (fuel : Nat)
    (op : String) (left right : SExpr) :
    checkSampleSubstitute bindings fuel (.bin op left right) = match fuel with
      | 0 => .bin op left right
      | n + 1 => match bindings.find? (fun p => beqSExpr p.1 (.bin op left right)) with
        | some p => p.2
        | none => .bin op (checkSampleSubstitute bindings n left)
            (checkSampleSubstitute bindings n right) := by
  cases fuel <;> rfl

private theorem sample_variable (bindings : List (SExpr × SExpr)) (fuel : Nat) (name : String) :
    checkSampleSubstitute bindings fuel (.variable name) = match fuel with
      | 0 => .variable name
      | _ + 1 => match bindings.find? (fun p => beqSExpr p.1 (.variable name)) with
        | some p => p.2
        | none => .variable name := by
  cases fuel <;> rfl

private theorem sample_literal (bindings : List (SExpr × SExpr)) (fuel value : Nat) :
    checkSampleSubstitute bindings fuel (.lit value) = match fuel with
      | 0 => .lit value
      | _ + 1 => match bindings.find? (fun p => beqSExpr p.1 (.lit value)) with
        | some p => p.2
        | none => .lit value := by
  cases fuel <;> rfl

private theorem check_sequence_select {l : Bool} (u : UProg) (caller : Fin u.fns.length)
    (Γ : Ctx) (fn : UFn) (fuel : Nat) (Λ : List (Res (declOf u)))
    (top : AtTop u caller Λ) (ss : List UStmt) :
    lowSeqL (l := l) u caller Γ fn fuel Λ top ss = match fuel with
      | 0 => .error "lower: blocks nested too deep"
      | n + 1 => lowSeqStep u caller (lowStufe u caller n) Γ fn Λ top ss := by
  cases fuel <;> rfl

private theorem check_structure_select {l : Bool} (u : UProg) (caller : Fin u.fns.length)
    (Γ : Ctx) (fn : UFn) (fuel : Nat) (Λ : List (Res (declOf u)))
    (top : AtTop u caller Λ) (s : UStmt) (ss : List UStmt) :
    lowStructL (l := l) u caller Γ fn fuel Λ top s ss = match fuel with
      | 0 => .error "lower: blocks nested too deep"
      | n + 1 => lowStructStep u caller (lowStufe u caller n) Γ fn Λ top s ss := by
  cases fuel <;> rfl

-- The measure gate retains its actual export. Absent clauses make its length
-- comparisons true independently of bodies, so no reachability reduction is needed.
private theorem check_measure_gate (u : UProg) (exported : Measures.Export u)
    (made : Measures.lowerMeasures u = .ok exported)
    (absent : ∀ fn ∈ u.fns, fn.decreases = none) (P : Programm (declOf u)) :
    Measures.checkedProgram u P = .ok (P, List.finRange u.fns.length) := by
  have cycles : Measures.cycleLengths u P exported.mass = true := by
    unfold Measures.cycleLengths
    apply List.all_eq_true.mpr
    intro f _
    apply List.all_eq_true.mpr
    intro g _
    have empty (i : (declOf u).Fn) : exported.mass i = [] :=
      Measures.lowerMeasures_absent u exported i
        (absent (fnAt u i) (List.get_mem u.fns i))
    rw [empty f, empty g]
    change (!zykS P (List.finRange u.fns.length) f g || true) = true
    exact Bool.or_true _
  -- Pin the whole tuple at the declaration's actual function type before
  -- reducing the dependent export match. No rewrite crosses its binder.
  let accepted : Programm (declOf u) × List (declOf u).Fn :=
    (P, List.finRange u.fns.length)
  change (match Measures.lowerMeasures u with
    | .error error => .error error
    | .ok actual =>
      if Measures.cycleLengths u P actual.mass then .ok accepted
      else .error "differing decreases tuple lengths in a recursion cycle") = .ok accepted
  rw [made]
  dsimp only
  exact if_pos cycles

-- Retain the complete dependent endpoints together. Transporting this certificate
-- along the whole source result never has to eliminate a function index or a body.
private structure CheckWitness (u : UProg) (floors : Nat) : Prop where
  lowered : (lowerAllg u).toOption.isSome = true
  derived : (uCheckDecls u).toOption.isSome = true
  marks : u.marken = ["p#duty"]
  tabs : u.tabs = []
  globs : u.globs = []
  sourceFloors : u.checks.map (·.boeden.length) = [floors]
  names : (uCheckDecls u).map (List.map CheckDecl.name) = .ok ["p"]
  duty : (uCheckDecls u).map
    (List.map fun d => (u.marken.get d.duty.1, d.duty.2)) = .ok [("p#duty", 0)]
  declared : (uCheckDecls u).map (fun cs => cs.all fun d =>
    decide (u.marken.get d.duty.1 ∈ u.marken)) = .ok true
  probe : (uCheckDecls u).map (fun cs => cs.all fun d =>
    decide (((declOf u).signatur d.probe).konsumiert = [d.duty]) &&
    decide (((declOf u).signatur d.probe).produziert = [d.duty])) = .ok true
  gates : (uCheckDecls u).map (fun cs => cs.all fun d => d.gates.all fun g =>
    decide (d.duty ∈ ((declOf u).signatur g).konsumiert)) = .ok true
  floorCounts : ((uCheckDecls u).toOption.get derived).map (fun d => d.boden.length) = [floors]
  gateCounts : ((uCheckDecls u).toOption.get derived).map (fun d => d.gates.length) = [1]
  probeReturn : (u.fns.find? (fun f => strEq f.name "p#probe")).map (·.ret) =
    some (.bool (.var "#checkReport"))
  admitted : Gabbro.Grammatik.checkB ((lowerAllg u).toOption.get lowered).1 [] []
    (List.finRange u.fns.length) ((uCheckDecls u).toOption.get derived) = true
  accepted : Zielsatz.AkzeptiertX ((lowerAllg u).toOption.get lowered).1
    (Cover.Differenz.sperrFamilie u) (List.finRange u.fns.length) [] [] [] []
    ((uCheckDecls u).toOption.get derived) = true

end Gabbro.Grammatik.Parser.Uebersetze

