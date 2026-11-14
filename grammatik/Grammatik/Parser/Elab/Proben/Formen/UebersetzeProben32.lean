/-
  File:      Grammatik/Parser/Elab/Proben/Formen/UebersetzeProben32.lean
  Subject:   Track P: invariants (`D.Inv`). A table's `invariant I : p;` and a
             `group G over { T, U } { invariant I .. }` elaborate to `UProg.invs` (carrier tables, the predicate
             over no parameter); `declOf` reads them (`Inv := Fin u.invs.length`, `traeger` over tables and statics, `invs`) and
             `Programm.invariante` is the lowered predicate under the guards of its carriers (`invSicht`). A
             writer of a carrier holds every lock guarding a carrier (`U003`, `invarianten_gehalten`); the
             elaborator refuses a unit where it does not.
-/
module
public import Grammatik.Parser.Elab.Proben.Invariants.Phases
import Grammatik.Parser.Elab.Proben.Invariants.Lexical
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil5
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest1
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a
import all Grammatik.Parser.Elab.UebersetzeAllg3.Body
import all Grammatik.Parser.Elab.UebersetzeAllg3.Stufe
import all Grammatik.Parser.Elab.UebersetzeAllg3.Seq
import all Grammatik.Parser.Elab.UebersetzeAllg3.Struct
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil12
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
import all Grammatik.Parser.Elab.Generic.StaticConformance
import all Grammatik.Parser.Elab.Generic.Signatures
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


namespace Gabbro.Grammatik.Parser.UebersetzeProben32

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.UebersetzeProben3 (stufe stufe_after stufe_elab_error)
open Gabbro.Grammatik.Uebersetzung.LibraryFixtureScanning

set_option maxRecDepth 100000

-- Select the used node of the typed mutual before inspecting its result.
-- Unfolding its shared recursion evaluates unrelated branches and contexts.
attribute [local cbv_eval] Nat.log2_def lowWertE.eq_def lowCmp.eq_def lowEns.eq_def
attribute [local cbv_opaque] lowStufe lowSeqL lowStructL
attribute [local cbv_eval] UebersetzeProben2.seq_select UebersetzeProben2.struct_select
  lowStufe_seq lowStufe_struct

/-- The carriers of the invariants, read through the declaration: `.inl` a table number, `.inr` a static number. -/
abbrev traeger := InvariantPhases.traeger

/-- A table invariant; its writer holds the guard by signature. -/
def inv_ok : String :=
  "module m { table T count 2 { slot { v : u32, } invariant I : forall k in slots of T : T.slots[k].v < 9; } lock L protects { T } rank 0; impl fn f(i : index into T) requires Held(L) effects { writes T.slots } { T.slots[i].v = 1; } }"

private def inv_ok_chunks : List Chunk :=
  [InvariantText.moduleM, InvariantText.tableT, InvariantText.slotV, InvariantText.invariantI,
   InvariantText.forallT, InvariantText.indexedLess, Chunk.closeSpace, InvariantText.lockT,
   InvariantText.indexFunction, InvariantText.heldL, InvariantText.writesT, InvariantText.writeT, Chunk.close]

private theorem inv_ok_text : inv_ok = String.ofList (characters inv_ok_chunks) := by
  rw [characters_join]
  cbv

private theorem inv_ok_lexed_zeuge :
    lexL (characters inv_ok_chunks) = .ok (tokens inv_ok_chunks) :=
  InvariantText.lexed _ (by cbv)

private def inv_ok_parsed :
    {items : List SItemTief // parseTopTief (tokens inv_ok_chunks) = .ok items} := by
  refine ⟨?items, ?parsed⟩
  case parsed => cbv <;> exact Eq.refl _

private def inv_ok_elaborated :
    {unit : UProg // elabU (pre108 inv_ok_parsed.val) = .ok unit} := by
  refine ⟨?unit, ?elaborated⟩
  case elaborated => cbv <;> exact Eq.refl _

private theorem inv_ok_invariants :
    lowerInvs inv_ok_elaborated.val (List.finRange inv_ok_elaborated.val.invs.length) = .ok () := by
  cbv

private theorem inv_ok_functions : ∀ f : Fin inv_ok_elaborated.val.fns.length,
    (lowerFnAt inv_ok_elaborated.val f).toOption.isSome = true ∧
      (fnAt inv_ok_elaborated.val f).decreases = none := by
  refine UebersetzeProben2.singleFn_all inv_ok_elaborated.val (by cbv) _ ?_
  constructor <;> cbv

private theorem inv_ok_lowered : UebersetzeProben2.lowerStage inv_ok_elaborated.val = "OK" :=
  UebersetzeProben2.lowerStage_checked _ inv_ok_invariants inv_ok_functions (by cbv)

theorem inv_ok_stufe : stufe inv_ok = "OK" :=
  stufe_after inv_ok_text inv_ok_lexed_zeuge inv_ok_parsed.property
    inv_ok_elaborated.property inv_ok_lowered
theorem inv_ok_traeger : traeger inv_ok = some [[.inl 0]] :=
  InvariantPhases.traeger_after inv_ok_text inv_ok_lexed_zeuge inv_ok_parsed.property
    inv_ok_elaborated.property (by
      simp only [InvariantPhases.carrierLists, declOf]
      cbv)

/-- Planted defect (`U003`): the writer takes the guard only in a block. -/
def inv_u003_refused : String :=
  "module m { table T count 2 { slot { v : u32, } invariant I : T.slots[0].v < 9; } lock L protects { T } rank 0; impl fn f(i : index into T) effects { writes T.slots, locks L } { locks L { T.slots[i].v = 1; } } }"

private def inv_u003_refused_chunks : List Chunk :=
  [InvariantText.moduleM, InvariantText.tableT, InvariantText.slotV, InvariantText.invariantI,
   InvariantText.firstLess, Chunk.closeSpace, InvariantText.lockT, InvariantText.indexFunction,
   InvariantText.locksT, InvariantText.lockedWriteT, Chunk.close]

private theorem inv_u003_refused_text : inv_u003_refused = String.ofList (characters inv_u003_refused_chunks) := by
  rw [characters_join]
  cbv

private theorem inv_u003_refused_lexed_zeuge :
    lexL (characters inv_u003_refused_chunks) = .ok (tokens inv_u003_refused_chunks) :=
  InvariantText.lexed _ (by cbv)

private def inv_u003_refused_parsed :
    {items : List SItemTief // parseTopTief (tokens inv_u003_refused_chunks) = .ok items} := by
  refine ⟨?items, ?parsed⟩
  case parsed => cbv <;> exact Eq.refl _

private theorem inv_u003_refused_elaborated :
    elabU (pre108 inv_u003_refused_parsed.val) = .error "a writer of an invariant's carrier does not hold all its locks" := by cbv

theorem inv_u003_refused_stufe :
    stufe inv_u003_refused = "elab: a writer of an invariant's carrier does not hold all its locks" :=
  stufe_elab_error inv_u003_refused_text inv_u003_refused_lexed_zeuge inv_u003_refused_parsed.property
    inv_u003_refused_elaborated

/-- A group invariant over two tables. -/
def gruppe_ok : String :=
  "module m { table T count 2 { slot { v : u32, } } table U count 2 { slot { w : u32, } } group G over { T, U } { invariant J : T.slots[0].v <= U.slots[0].w; } impl fn f() { } }"

private def gruppe_ok_chunks : List Chunk :=
  [InvariantText.moduleM, InvariantText.tableT, InvariantText.slotV, Chunk.closeSpace, InvariantText.tableU,
   InvariantText.slotW, Chunk.closeSpace, InvariantText.groupTU, InvariantText.compareT,
   InvariantText.firstU, Chunk.closeSpace, InvariantText.emptyFunction, Chunk.close]

private theorem gruppe_ok_text : gruppe_ok = String.ofList (characters gruppe_ok_chunks) := by
  rw [characters_join]
  cbv

private theorem gruppe_ok_lexed_zeuge :
    lexL (characters gruppe_ok_chunks) = .ok (tokens gruppe_ok_chunks) :=
  InvariantText.lexed _ (by cbv)

private def gruppe_ok_parsed :
    {items : List SItemTief // parseTopTief (tokens gruppe_ok_chunks) = .ok items} := by
  refine ⟨?items, ?parsed⟩
  case parsed => cbv <;> exact Eq.refl _

private def gruppe_ok_elaborated :
    {unit : UProg // elabU (pre108 gruppe_ok_parsed.val) = .ok unit} := by
  refine ⟨?unit, ?elaborated⟩
  case elaborated => cbv <;> exact Eq.refl _

private theorem gruppe_ok_invariants :
    lowerInvs gruppe_ok_elaborated.val (List.finRange gruppe_ok_elaborated.val.invs.length) = .ok () := by
  cbv

private theorem gruppe_ok_functions : ∀ f : Fin gruppe_ok_elaborated.val.fns.length,
    (lowerFnAt gruppe_ok_elaborated.val f).toOption.isSome = true ∧
      (fnAt gruppe_ok_elaborated.val f).decreases = none := by
  refine UebersetzeProben2.singleFn_all gruppe_ok_elaborated.val (by cbv) _ ?_
  constructor <;> cbv

private theorem gruppe_ok_lowered : UebersetzeProben2.lowerStage gruppe_ok_elaborated.val = "OK" :=
  UebersetzeProben2.lowerStage_checked _ gruppe_ok_invariants gruppe_ok_functions (by cbv)

theorem gruppe_ok_stufe : stufe gruppe_ok = "OK" :=
  stufe_after gruppe_ok_text gruppe_ok_lexed_zeuge gruppe_ok_parsed.property
    gruppe_ok_elaborated.property gruppe_ok_lowered
theorem gruppe_ok_traeger : traeger gruppe_ok = some [[.inl 0, .inl 1]] :=
  InvariantPhases.traeger_after gruppe_ok_text gruppe_ok_lexed_zeuge gruppe_ok_parsed.property
    gruppe_ok_elaborated.property (by
      simp only [InvariantPhases.carrierLists, declOf]
      cbv)

/-- Statement text is transported as a labelled scope; the ordinary invariant
    reader still checks every declared carrier and predicate. -/
def breakingText (source : String) : Option (List UStmt) := do
  let tokens ← (lex source).toOption
  let statement ← (parseTopStmt tokens).toOption
  let ctx : UCtx := { names := [], kinds := [], types := [], tabs := [], locks := [],
                      held := [], res := none, fname := "sample", alias := [], lits := [] }
  ((uAnwReihe [] [] 1000 ctx [statement]).toOption).map (·.1)

theorem breaking_text_export_zeuge :
    breakingText "breaking I { }" = some [.breakingBeg "I", .blkEnd] := by
  cbv

theorem breaking_multiple_text_export_zeuge :
    breakingText "breaking I, J { }" =
      some [.breakingBeg "I", .breakingBeg "J", .blkEnd, .blkEnd] := by
  cbv

private def breaking_source : String :=
  "module m { table T count 2 { slot { v : u32, } invariant I : true; } impl fn f() { breaking I { } } }"

private def breaking_source_chunks : List Chunk :=
  [InvariantText.moduleM, InvariantText.tableT, InvariantText.slotV, InvariantText.invariantI,
   InvariantText.truePredicate, Chunk.closeSpace, InvariantText.breakingFunction, Chunk.close]

private theorem breaking_source_text : breaking_source = String.ofList (characters breaking_source_chunks) := by
  rw [characters_join]
  cbv

private theorem breaking_source_lexed_zeuge :
    lexL (characters breaking_source_chunks) = .ok (tokens breaking_source_chunks) :=
  InvariantText.lexed _ (by cbv)

private def breaking_source_parsed :
    {items : List SItemTief // parseTopTief (tokens breaking_source_chunks) = .ok items} := by
  refine ⟨?items, ?parsed⟩
  case parsed => cbv <;> exact Eq.refl _

private def breaking_source_elaborated :
    {unit : UProg // elabU (pre108 breaking_source_parsed.val) = .ok unit} := by
  refine ⟨?unit, ?elaborated⟩
  case elaborated => cbv <;> exact Eq.refl _

private theorem breaking_source_invariants :
    lowerInvs breaking_source_elaborated.val (List.finRange breaking_source_elaborated.val.invs.length) = .ok () := by
  cbv

private theorem breaking_source_functions : ∀ f : Fin breaking_source_elaborated.val.fns.length,
    (lowerFnAt breaking_source_elaborated.val f).toOption.isSome = true ∧
      (fnAt breaking_source_elaborated.val f).decreases = none := by
  refine UebersetzeProben2.singleFn_all breaking_source_elaborated.val (by cbv) _ ?_
  constructor <;> cbv

private theorem breaking_source_lowered : UebersetzeProben2.lowerStage breaking_source_elaborated.val = "OK" :=
  UebersetzeProben2.lowerStage_checked _ breaking_source_invariants breaking_source_functions (by cbv)

/-- An invariant declaration and its named scope elaborate through the new surface. -/
theorem breaking_invariant_bound_zeuge :
    stufe "module m { table T count 2 { slot { v : u32, } invariant I : true; } impl fn f() { breaking I { } } }" =
      "OK" :=
  stufe_after breaking_source_text breaking_source_lexed_zeuge breaking_source_parsed.property
    breaking_source_elaborated.property breaking_source_lowered

end Gabbro.Grammatik.Parser.UebersetzeProben32
