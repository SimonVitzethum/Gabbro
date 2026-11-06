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
import Init.Data.String.Lemmas.Intercalate
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

def allTables (unit : UProg) : List (declOf unit).Tab := List.finRange unit.tabs.length

/-- The core checker on what the pipeline makes of a text (`false` when the pipeline refuses it). -/
def akzeptiertText (s : String) : Bool :=
  match uebersetzeAllg s with
  | .ok ⟨u, P, fs⟩ =>
    Akzeptiert P ⟨fun _ => [], fun _ _ => true⟩ fs [] ((allTables u).map Sum.inl) fs
  | .error _ => false

-- Data projections retain the original spelling, tokens and step count;
-- the arbitrary-suffix scanner proof is a separate opaque theorem.
scoped macro "region_chunk " name:ident " as " text:str
    " with_tokens " emitted:term " with_steps " fuel:num : command => do
  let spelling := Lean.mkIdentFrom name (name.getId.appendAfter "_spelling")
  let chars := Lean.mkIdentFrom name (name.getId.appendAfter "_characters")
  let ts := Lean.mkIdentFrom name (name.getId.appendAfter "_tokens")
  let count := Lean.mkIdentFrom name (name.getId.appendAfter "_steps")
  let scanned := Lean.mkIdentFrom name (name.getId.appendAfter "_scanned")
  let decoded := Lean.mkIdentFrom name (name.getId.appendAfter "_text")
  let bounded := Lean.mkIdentFrom name (name.getId.appendAfter "_bounded")
  let literal : Lean.TSyntax `term := ⟨text.raw⟩
  let steps : Lean.TSyntax `term := ⟨fuel.raw⟩
  let a : Lean.TSyntax `command ← `(command| private def $spelling : String := $literal)
  let b : Lean.TSyntax `command ← `(command| private def $chars : List Char := ($spelling).toList)
  let c : Lean.TSyntax `command ← `(command| private def $ts : List Token := $emitted)
  let d : Lean.TSyntax `command ← `(command| private def $count : Nat := $steps)
  let e : Lean.TSyntax `command ← `(command|
    private theorem $scanned (rest : List Char) (remaining : Nat) :
        scan false ($chars ++ rest) (remaining + $count) =
          ($ts).foldr (fun token answer => Except.map (token :: ·) answer)
            (scan false rest remaining) := by cbv)
  let f : Lean.TSyntax `command ← `(command|
    private def $name : Chunk := ⟨$chars, $ts, $count, $scanned⟩)
  let g : Lean.TSyntax `command ← `(command|
    private theorem $decoded : String.ofList ($name).characters = $spelling := by
      change String.ofList (($spelling).toList) = $spelling
      exact String.ofList_toList)
  let h : Lean.TSyntax `command ← `(command|
    private theorem $bounded : decide (($name).steps ≤ ($name).characters.length) = true := by cbv)
  return ⟨Lean.mkNullNode #[a, b, c, d, e, f, g, h]⟩

open scoped Gabbro.Grammatik.Parser.UebersetzeProben40

region_chunk moduleChunk as "module zellen::region {\n"
  with_tokens [.wort "module", .ident "zellen", .zeichen "::", .ident "region", .zeichen "{"]
  with_steps 8

region_chunk providerChunk as "table T from neu {\n    slot {\n        x : u64 in 0 .. 255,\n    }\n}\n"
  with_tokens [.wort "table", .ident "T", .wort "from", .ident "neu", .zeichen "{",
    .wort "slot", .zeichen "{", .wort "x", .zeichen ":", .wort "u64", .wort "in",
    .num 0, .zeichen "..", .num 255, .zeichen ",", .zeichen "}", .zeichen "}"]
  with_steps 49

region_chunk finiteChunk as "table U count 4 {\n    slot {\n        y : u64 in 0 .. 255,\n    }\n}\n"
  with_tokens [.wort "table", .ident "U", .wort "count", .num 4, .zeichen "{",
    .wort "slot", .zeichen "{", .ident "y", .zeichen ":", .wort "u64", .wort "in",
    .num 0, .zeichen "..", .num 255, .zeichen ",", .zeichen "}", .zeichen "}"]
  with_steps 49

region_chunk externChunk as "extern fn neu() -> index into T effects { pure } costs <= 1000 ops;\n"
  with_tokens [.wort "extern", .wort "fn", .ident "neu", .zeichen "(", .zeichen ")",
    .zeichen "->", .wort "index", .wort "into", .ident "T", .wort "effects",
    .zeichen "{", .wort "pure", .zeichen "}", .wort "costs", .zeichen "<=",
    .num 1000, .wort "ops", .zeichen ";"]
  with_steps 33

region_chunk functionChunk as "impl fn f()\n    effects { "
  with_tokens [.wort "impl", .wort "fn", .ident "f", .zeichen "(", .zeichen ")",
    .wort "effects", .zeichen "{"]
  with_steps 16

region_chunk writesChunk as "writes T.slots "
  with_tokens [.wort "writes", .ident "T", .zeichen ".", .wort "slots"]
  with_steps 6

region_chunk pureChunk as "pure "
  with_tokens [.wort "pure"]
  with_steps 2

region_chunk allocationChunk as "}\n    costs   <= 1000 ops\n{\n    let r = alloc "
  with_tokens [.zeichen "}", .wort "costs", .zeichen "<=", .num 1000, .wort "ops",
    .zeichen "{", .wort "let", .wort "r", .zeichen "=", .wort "alloc"]
  with_steps 30

region_chunk providerTargetChunk as "T;\n"
  with_tokens [.ident "T", .zeichen ";"]
  with_steps 3

region_chunk finiteTargetChunk as "U;\n"
  with_tokens [.ident "U", .zeichen ";"]
  with_steps 3

private def targetChunk (provider : Bool) : Chunk :=
  if provider then providerTargetChunk else finiteTargetChunk

region_chunk returnChunk as "    r->x = 7;\n    return;\n}\n}\n"
  with_tokens [.wort "r", .zeichen "->", .wort "x", .zeichen "=", .num 7, .zeichen ";",
    .wort "return", .zeichen ";", .zeichen "}", .zeichen "}"]
  with_steps 24

private def sourceChunks (writes provider : Bool) : List Chunk :=
  [moduleChunk, providerChunk, finiteChunk, externChunk, functionChunk,
    if writes then writesChunk else pureChunk, allocationChunk, targetChunk provider, returnChunk]

private def sourceSpellings (writes provider : Bool) : List String :=
  [moduleChunk_spelling, providerChunk_spelling, finiteChunk_spelling,
    externChunk_spelling, functionChunk_spelling,
    if writes then writesChunk_spelling else pureChunk_spelling,
    allocationChunk_spelling,
    if provider then providerTargetChunk_spelling else finiteTargetChunk_spelling,
    returnChunk_spelling]

private theorem source_fragment_text (writes provider : Bool) :
    (sourceChunks writes provider).map (fun chunk => String.ofList chunk.characters) =
      sourceSpellings writes provider := by
  cases writes <;> cases provider <;>
    simp only [sourceChunks, sourceSpellings, targetChunk,
      Bool.false_eq_true, reduceIte, List.map_cons, List.map_nil,
      moduleChunk_text, providerChunk_text, finiteChunk_text, externChunk_text,
      functionChunk_text, writesChunk_text, pureChunk_text, allocationChunk_text,
      providerTargetChunk_text, finiteTargetChunk_text, returnChunk_text]

private theorem source_spelling (writes provider : Bool) :
    quelle (if writes then "writes T.slots" else "pure") (if provider then "T" else "U") =
      String.join (sourceSpellings writes provider) := by
  cases writes <;> cases provider <;> decide +kernel

private theorem source_characters (writes provider : Bool) :
    quelle (if writes then "writes T.slots" else "pure") (if provider then "T" else "U") =
      String.ofList (characters (sourceChunks writes provider)) :=
  (source_spelling writes provider).trans
    ((characters_join (sourceChunks writes provider)).trans
      (congrArg String.join (source_fragment_text writes provider))).symm

private theorem source_bound (writes provider : Bool) :
    steps (sourceChunks writes provider) ≤ (characters (sourceChunks writes provider)).length := by
  apply steps_le_length
  cases writes <;> cases provider <;>
    simp only [sourceChunks, targetChunk, Bool.false_eq_true,
      reduceIte, List.all_cons, List.all_nil, moduleChunk_bounded, providerChunk_bounded,
      finiteChunk_bounded, externChunk_bounded, functionChunk_bounded, writesChunk_bounded,
      pureChunk_bounded, allocationChunk_bounded, providerTargetChunk_bounded,
      finiteTargetChunk_bounded, returnChunk_bounded, Bool.and_self]

private theorem source_lexed (writes provider : Bool) :
    lexL (characters (sourceChunks writes provider)) = .ok (tokens (sourceChunks writes provider)) :=
  lex_chunks _ (Nat.le_trans (source_bound writes provider) (Nat.le_succ _))

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
  have rejected : uebersetzeAllg (quelle "writes T.slots" "U") = .error error :=
    pipeline_elab_error (writes := true) (provider := false) parsed elaborated
  unfold akzeptiertText
  rw [rejected]

/-- Refused: the write through the reference without the write right on `T`. -/
theorem schreiben_ohne_recht : akzeptiertText (quelle "pure" "T") = false := by
  obtain ⟨items, unit, error, parsed, elaborated, lowered⟩ := write_refused
  have rejected : uebersetzeAllg (quelle "pure" "T") = .error error :=
    pipeline_lower_error (writes := false) (provider := true) parsed elaborated lowered
  unfold akzeptiertText
  rw [rejected]

end Gabbro.Grammatik.Parser.UebersetzeProben40
