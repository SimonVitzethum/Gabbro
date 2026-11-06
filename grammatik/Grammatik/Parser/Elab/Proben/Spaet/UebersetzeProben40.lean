/-
  File:      Grammatik/Parser/Elab/Proben/Spaet/UebersetzeProben40.lean
  Subject:   Track P, the open region from source text (PLAN-DYNAMIC 14): `table T from neu` (an open table and its
             provider), `extern fn neu() -> index into T` (the provider answers a reference), `let r = alloc T;` (the
             provider's call, `Block.alloc`) and `r->x = 7;` (`Stmt.assignSlotRef`). The whole Lean pipeline --
             lex, parse, elaborate, lower onto `declOf u` -- runs on the text, and the core checker `Akzeptiert`
             accepts the result, decided by the kernel. The twins are refused: `alloc` of a table without a provider,
             and the write without `writes T.slots`.
-/
module
public import Grammatik.Parser.Elab.UebersetzePipeline
public import Grammatik.Zielsatz.Kern.Akzeptiert
import Grammatik.Parser.Stmt.LibraryFixtureScanning
import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben2Basis
import all Grammatik.Kern.Syntax.Typen.Shape
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil12
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
import all Grammatik.Parser.Elab.Generic.StaticConformance
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest1
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a
import all Grammatik.Parser.Elab.UebersetzeAllg3.Body
import all Grammatik.Parser.Elab.UebersetzeAllg3.Stufe
import all Grammatik.Parser.Elab.UebersetzeAllg3.Seq
import all Grammatik.Parser.Elab.UebersetzeAllg3.Struct
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


namespace Gabbro.Grammatik.Parser.UebersetzeProben40

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Uebersetzung.LibraryFixtureScanning

/-- The unit, with its write effect `w` and the table `alloc` names. -/
def quelle (w tab : String) : String := "module zellen::region {
table T from neu {
    slot {
        x : u64 in 0 .. 255,
    }
}
table U count 4 {
    slot {
        y : u64 in 0 .. 255,
    }
}
extern fn neu() -> index into T effects { pure } costs <= 1000 ops;
impl fn f()
    effects { " ++ w ++ " }
    costs   <= 1000 ops
{
    let r = alloc " ++ tab ++ ";
    r->x = 7;
    return;
}
}
"

/-- The accepted unit. -/
def src : String := quelle "writes T.slots" "T"

private def allTables (unit : UProg) : List (declOf unit).Tab := List.finRange unit.tabs.length

/-- The core checker on what the pipeline makes of a text (`false` when the pipeline refuses it). -/
def akzeptiertText (s : String) : Bool :=
  match uebersetzeAllg s with
  | .ok ⟨u, P, fs⟩ =>
    Akzeptiert P ⟨fun _ => [], fun _ _ => true⟩ fs [] ((allTables u).map Sum.inl) fs
  | .error _ => false

-- These cuts carry equations of the existing scanner, with arbitrary suffixes.
private def moduleChunk : Chunk where
  characters := "module zellen::region {\n".toList
  tokens := [.wort "module", .ident "zellen", .zeichen "::", .ident "region", .zeichen "{"]
  steps := 8
  scanned := by intro rest remaining; cbv

private def providerChunk : Chunk where
  characters := "table T from neu {\n    slot {\n        x : u64 in 0 .. 255,\n    }\n}\n".toList
  tokens := [.wort "table", .ident "T", .wort "from", .ident "neu", .zeichen "{",
    .wort "slot", .zeichen "{", .wort "x", .zeichen ":", .wort "u64", .wort "in",
    .num 0, .zeichen "..", .num 255, .zeichen ",", .zeichen "}", .zeichen "}"]
  steps := 49
  scanned := by intro rest remaining; cbv

private def finiteChunk : Chunk where
  characters := "table U count 4 {\n    slot {\n        y : u64 in 0 .. 255,\n    }\n}\n".toList
  tokens := [.wort "table", .ident "U", .wort "count", .num 4, .zeichen "{",
    .wort "slot", .zeichen "{", .ident "y", .zeichen ":", .wort "u64", .wort "in",
    .num 0, .zeichen "..", .num 255, .zeichen ",", .zeichen "}", .zeichen "}"]
  steps := 49
  scanned := by intro rest remaining; cbv

private def externChunk : Chunk where
  characters := "extern fn neu() -> index into T effects { pure } costs <= 1000 ops;\n".toList
  tokens := [.wort "extern", .wort "fn", .ident "neu", .zeichen "(", .zeichen ")",
    .zeichen "->", .wort "index", .wort "into", .ident "T", .wort "effects",
    .zeichen "{", .wort "pure", .zeichen "}", .wort "costs", .zeichen "<=",
    .num 1000, .wort "ops", .zeichen ";"]
  steps := 33
  scanned := by intro rest remaining; cbv

private def functionChunk : Chunk where
  characters := "impl fn f()\n    effects { ".toList
  tokens := [.wort "impl", .wort "fn", .ident "f", .zeichen "(", .zeichen ")",
    .wort "effects", .zeichen "{"]
  steps := 16
  scanned := by intro rest remaining; cbv

private def writesChunk : Chunk where
  characters := "writes T.slots ".toList
  tokens := [.wort "writes", .ident "T", .zeichen ".", .wort "slots"]
  steps := 6
  scanned := by intro rest remaining; cbv

private def pureChunk : Chunk where
  characters := "pure ".toList
  tokens := [.wort "pure"]
  steps := 2
  scanned := by intro rest remaining; cbv

private def allocationChunk : Chunk where
  characters := "}\n    costs   <= 1000 ops\n{\n    let r = alloc ".toList
  tokens := [.zeichen "}", .wort "costs", .zeichen "<=", .num 1000, .wort "ops",
    .zeichen "{", .wort "let", .wort "r", .zeichen "=", .wort "alloc"]
  steps := 30
  scanned := by intro rest remaining; cbv

private def targetChunk (provider : Bool) : Chunk := if provider then {
  characters := "T;\n".toList
  tokens := [.ident "T", .zeichen ";"]
  steps := 3
  scanned := by intro rest remaining; cbv } else {
  characters := "U;\n".toList
  tokens := [.ident "U", .zeichen ";"]
  steps := 3
  scanned := by intro rest remaining; cbv }

private def returnChunk : Chunk where
  characters := "    r->x = 7;\n    return;\n}\n}\n".toList
  tokens := [.wort "r", .zeichen "->", .wort "x", .zeichen "=", .num 7, .zeichen ";",
    .wort "return", .zeichen ";", .zeichen "}", .zeichen "}"]
  steps := 24
  scanned := by intro rest remaining; cbv

private def sourceChunks (writes provider : Bool) : List Chunk :=
  [moduleChunk, providerChunk, finiteChunk, externChunk, functionChunk,
    if writes then writesChunk else pureChunk, allocationChunk, targetChunk provider, returnChunk]

private theorem source_characters (writes provider : Bool) :
    quelle (if writes then "writes T.slots" else "pure") (if provider then "T" else "U") =
      String.ofList (characters (sourceChunks writes provider)) := by
  cases writes <;> cases provider <;>
    simp only [characters, sourceChunks, moduleChunk, providerChunk, finiteChunk,
      externChunk, functionChunk, writesChunk, pureChunk, allocationChunk, targetChunk,
      returnChunk, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      String.ofList_append, String.ofList_toList] <;> cbv

private theorem source_lexed (writes provider : Bool) :
    lexL (characters (sourceChunks writes provider)) = .ok (tokens (sourceChunks writes provider)) :=
  lex_chunks _ (by
    cases writes <;> cases provider <;>
      simp only [sourceChunks, Bool.true_eq_true, Bool.false_eq_true, reduceIte,
        steps, characters, List.flatMap_cons, List.flatMap_nil, List.length_append,
        List.length_nil] <;> cbv <;> omega)

-- Select only the operation used by this body from the canonical fuel record.
attribute [local cbv_opaque] lowStufe lowSeqL lowStructL uFloatLimit
attribute [local cbv_eval] UebersetzeProben2.seq_select UebersetzeProben2.struct_select
  lowStufe_seq lowStufe_struct

private def observed (unit : UProg) : Bool :=
  unit.fns.map (·.body) == [[.bindAx "r" "neu" [], .assignRef "r" "x" (.lit 7)]] &&
    unit.tabs.map (·.von) == [some "neu", none] && unit.axs.map (·.res) == [some (.ref 0)]

private def checkedImage (unit : UProg)
    (image : Programm (declOf unit) × List (declOf unit).Fn) : Prop :=
  Akzeptiert image.1 ⟨fun _ => [], fun _ _ => true⟩ image.2 []
    ((allTables unit).map Sum.inl) image.2 = true

/-- The checker certificate is attached to actual function results before assembly projects them. -/
private structure RegionFacts (unit : UProg) : Prop where
  invs : unit.invs = []
  contracts : contractGate unit = true
  measures : ∀ f : Fin unit.fns.length, (fnAt unit f).decreases = none
  functions : ∃ pieces : ∀ f : Fin unit.fns.length,
      EnsTy unit f × RumpTy unit f × ReqTy unit f,
    (∀ f, lowerFnAt unit f = .ok (pieces f)) ∧
    ∀ invariants pointers foreigns,
      checkedImage unit (progOfFn unit (fun f => (pieces f).1) (fun f => (pieces f).2.1)
        (fun f => (pieces f).2.2) invariants pointers foreigns, List.finRange unit.fns.length)

private theorem region_lowered {unit : UProg} (facts : RegionFacts unit) :
    (lowerAllg unit).toOption.isSome = true := by
  obtain ⟨pieces, origin, _⟩ := facts.functions
  apply Gabbro.Grammatik.Uebersetzung.LibraryFixtureProofs.lowering_ok unit facts.invs facts.contracts
  intro f
  exact ⟨by rw [origin f] <;> rfl, facts.measures f⟩

private theorem region_checked {unit : UProg} (facts : RegionFacts unit)
    {image : Programm (declOf unit) × List (declOf unit).Fn}
    (emitted : lowerAllg unit = .ok image) : checkedImage unit image := by
  rcases image with ⟨program, functions⟩
  obtain ⟨pieces, origin, safe⟩ := facts.functions
  have selected (f : Fin unit.fns.length) (proof : ∃ value, lowerFnAt unit f = .ok value) :
      lowerAtPair unit f proof = pieces f := lowerAtPair_of_ok unit f proof (origin f)
  unfold lowerAllg at emitted
  split at emitted
  · cases emitted
  · split at emitted
    · cases emitted
    · split at emitted
      · obtain ⟨programEq, functionsEq⟩ := Measures.checkedProgram_eq emitted
        rw [programEq, functionsEq]
        simp only [selected]
        exact safe _ _ _
      · cases emitted

private theorem region_phases : ∃ items unit,
    parseTopTief (tokens (sourceChunks true true)) = .ok items ∧
    elabU (pre108 items) = .ok unit ∧ observed unit = true ∧ RegionFacts unit := by
  let items : List SItemTief := ?items
  have parsed : parseTopTief (tokens (sourceChunks true true)) = .ok items := by
    cbv <;> exact Eq.refl _
  let unit : UProg := ?unit
  have elaborated : elabU (pre108 items) = .ok unit := by cbv <;> exact Eq.refl _
  have count : unit.fns.length = 1 := by cbv
  refine ⟨items, unit, parsed, elaborated, ?observed, ?facts⟩
  case observed => cbv
  case facts =>
    refine {
      invs := by cbv
      contracts := by cbv
      measures := ?_
      functions := ?_ }
    · rintro ⟨index, bound⟩
      have small : index < 1 := bound
      have zero : index = 0 := by omega
      subst index
      cbv
    · let first : Fin unit.fns.length := ⟨0, by omega⟩
      let value : EnsTy unit first × RumpTy unit first × ReqTy unit first := ?value
      have produced : lowerFnAt unit first = .ok value := by cbv <;> exact Eq.refl _
      refine ⟨?pieces, ?equations, ?safe⟩
      case pieces =>
        change (f : Fin 1) → EnsTy unit f × RumpTy unit f × ReqTy unit f
        exact Fin.cases (motive := fun f : Fin 1 => EnsTy unit f × RumpTy unit f × ReqTy unit f)
          value (fun f : Fin 0 => Fin.elim0 f)
      case equations =>
        rintro ⟨index, bound⟩
        have small : index < 1 := bound
        have zero : index = 0 := by omega
        subst index
        exact produced
      case safe => intro invariants pointers foreigns; cbv

private theorem elab_refused : ∃ items error,
    parseTopTief (tokens (sourceChunks true false)) = .ok items ∧
    elabU (pre108 items) = .error error := by
  refine ⟨?items, ?error, ?parsed, ?refused⟩
  case parsed => cbv <;> exact Eq.refl _
  case refused => cbv <;> exact Eq.refl _

private theorem lower_rejected {unit : UProg} {error : String}
    (stage : UebersetzeProben2.lowerStage unit = "lower: " ++ error) :
    ∃ reason, lowerAllg unit = .error reason := by
  cases result : lowerAllg unit with
  | error reason => exact ⟨reason, rfl⟩
  | ok image =>
    have impossible : "OK" = "lower: " ++ error := by
      simpa only [UebersetzeProben2.lowerStage, result] using stage
    have lengths := congrArg String.length impossible
    rw [String.length_append] at lengths
    change 2 = 7 + error.length at lengths
    omega

private theorem write_refused : ∃ items unit error,
    parseTopTief (tokens (sourceChunks false true)) = .ok items ∧
    elabU (pre108 items) = .ok unit ∧ lowerAllg unit = .error error := by
  let items : List SItemTief := ?items
  have parsed : parseTopTief (tokens (sourceChunks false true)) = .ok items := by
    cbv <;> exact Eq.refl _
  let unit : UProg := ?unit
  have elaborated : elabU (pre108 items) = .ok unit := by cbv <;> exact Eq.refl _
  have count : unit.fns.length = 1 := by cbv
  let first : Fin unit.fns.length := ⟨0, by omega⟩
  have failed : lowerFnAt unit first = .error "write without right" := by cbv
  have outcomes : ∀ f : Fin unit.fns.length,
      lowerFnAt unit f = .error "write without right" ∨ (lowerFnAt unit f).toOption.isSome = true := by
    rintro ⟨index, bound⟩
    have small : index < 1 := bound
    have zero : index = 0 := by omega
    subst index
    exact Or.inl failed
  have stage := UebersetzeProben2.lowerStage_error unit "write without right"
    (by cbv) outcomes ⟨first, failed⟩
  obtain ⟨error, rejected⟩ := lower_rejected stage
  exact ⟨items, unit, error, parsed, elaborated, rejected⟩

private theorem region_pipeline : ∃ unit image,
    uebersetzeAllg src = .ok ⟨unit, image⟩ ∧ observed unit = true ∧ checkedImage unit image := by
  obtain ⟨items, unit, parsed, elaborated, body, facts⟩ := region_phases
  let image : Programm (declOf unit) × List (declOf unit).Fn :=
    (lowerAllg unit).toOption.get (region_lowered facts)
  have lowered : lowerAllg unit = .ok (image.1, image.2) := except_ok_get (region_lowered facts)
  have pipeline := uebersetzeAllg_von_zeichen (source_lexed true true) parsed elaborated lowered
  have text : src = String.ofList (characters (sourceChunks true true)) := source_characters true true
  rw [← text] at pipeline
  exact ⟨unit, image, pipeline, body, region_checked facts lowered⟩

private theorem pipeline_elab_error {writes provider : Bool} {items : List SItemTief} {error : String}
    (parsed : parseTopTief (tokens (sourceChunks writes provider)) = .ok items)
    (elaborated : elabU (pre108 items) = .error error) :
    uebersetzeAllg (quelle (if writes then "writes T.slots" else "pure")
      (if provider then "T" else "U")) = .error error := by
  rw [source_characters writes provider]
  unfold uebersetzeAllg
  rw [lex_ofList, source_lexed]
  dsimp only
  rw [parsed]
  dsimp only
  rw [elaborated]

private theorem pipeline_lower_error {writes provider : Bool} {items : List SItemTief}
    {unit : UProg} {error : String}
    (parsed : parseTopTief (tokens (sourceChunks writes provider)) = .ok items)
    (elaborated : elabU (pre108 items) = .ok unit) (lowered : lowerAllg unit = .error error) :
    uebersetzeAllg (quelle (if writes then "writes T.slots" else "pure")
      (if provider then "T" else "U")) = .error error := by
  rw [source_characters writes provider]
  unfold uebersetzeAllg
  rw [lex_ofList, source_lexed]
  dsimp only
  rw [parsed]
  dsimp only
  rw [elaborated]
  dsimp only
  rw [lowered]

/-- The body elaborates to the provider's call and the write through the reference. -/
theorem region_koerper : (match uebersetzeAllg src with
    | .ok ⟨u, _, _⟩ => u.fns.map (·.body) == [[.bindAx "r" "neu" [], .assignRef "r" "x" (.lit 7)]] &&
        u.tabs.map (·.von) == [some "neu", none] &&
        u.axs.map (·.res) == [some (.ref 0)]
    | .error _ => false) = true := by
  obtain ⟨unit, image, pipeline, body, _⟩ := region_pipeline
  rw [pipeline]
  exact body

/-- **The open region from source text is accepted by the core checker.** -/
theorem region_akzeptiert : akzeptiertText src = true := by
  obtain ⟨unit, image, pipeline, _, checked⟩ := region_pipeline
  unfold akzeptiertText
  rw [pipeline]
  exact checked

/-- Refused: `alloc U`, a table without a provider. -/
theorem alloc_ohne_anbieter : akzeptiertText (quelle "writes T.slots" "U") = false := by
  obtain ⟨items, error, parsed, elaborated⟩ := elab_refused
  have rejected := pipeline_elab_error parsed elaborated
  simp only [Bool.true_eq_true, Bool.false_eq_true, reduceIte] at rejected
  unfold akzeptiertText
  rw [rejected]

/-- Refused: the write through the reference without the write right on `T`. -/
theorem schreiben_ohne_recht : akzeptiertText (quelle "pure" "T") = false := by
  obtain ⟨items, unit, error, parsed, elaborated, lowered⟩ := write_refused
  have rejected := pipeline_lower_error parsed elaborated lowered
  simp only [Bool.true_eq_true, Bool.false_eq_true, reduceIte] at rejected
  unfold akzeptiertText
  rw [rejected]

end Gabbro.Grammatik.Parser.UebersetzeProben40
