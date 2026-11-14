/-
  File:      Grammatik/Parser/Elab/Proben/Spaet/UebersetzeProben41.lean
  Subject:   C05: an invariant's carriers are tables AND statics (`D.traeger : Inv -> List (Tab ⊕ Glob)`).
             A `group G over { A, B }` of statics, and a group of a table and a static under one lock,
             elaborate and lower; `declOf` carries the whole carrier list (`lowerAllg_traeger`). `U003`
             covers a writer of a static (`gputs`); refused: a static writer without the group's lock, a
             predicate reading a static the group does not declare (`lowerInvAt`), an unknown carrier.
             The sources are SHORT on purpose (the kernel lexes them).
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



namespace Gabbro.Grammatik.Parser.UebersetzeProben41

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

/-- The carriers of the invariants, read through the declaration: `.inl` a table number, `.inr` a static
    number. -/
abbrev traeger := InvariantPhases.traeger

/-- A global-only group; its writer holds the guard by signature. -/
def glob_gruppe_ok : String :=
  "module m { static mut A : u32 = 0 shared; static mut B : u32 = 0 shared; lock L protects { A, B } rank 0; group G over { A, B } { invariant J : A <= B; } impl fn f() requires Held(L) effects { writes A } { A = 1; } }"

private def glob_gruppe_ok_chunks : List Chunk :=
  [InvariantText.moduleM, InvariantText.staticA, InvariantText.staticB, InvariantText.lockAB,
   InvariantText.groupAB, InvariantText.compareAB, Chunk.closeSpace, InvariantText.plainFunction,
   InvariantText.heldL, InvariantText.writesA, InvariantText.writeA, Chunk.close]

private theorem glob_gruppe_ok_text : glob_gruppe_ok = String.ofList (characters glob_gruppe_ok_chunks) := by
  rw [characters_join]
  cbv

private theorem glob_gruppe_ok_lexed_zeuge :
    lexL (characters glob_gruppe_ok_chunks) = .ok (tokens glob_gruppe_ok_chunks) :=
  InvariantText.lexed _ (by cbv)

private def glob_gruppe_ok_parsed :
    {items : List SItemTief // parseTopTief (tokens glob_gruppe_ok_chunks) = .ok items} := by
  refine ⟨?items, ?parsed⟩
  case parsed => cbv <;> exact Eq.refl _

private def glob_gruppe_ok_elaborated :
    {unit : UProg // elabU (pre108 glob_gruppe_ok_parsed.val) = .ok unit} := by
  refine ⟨?unit, ?elaborated⟩
  case elaborated => cbv <;> exact Eq.refl _

private theorem glob_gruppe_ok_invariants :
    lowerInvs glob_gruppe_ok_elaborated.val (List.finRange glob_gruppe_ok_elaborated.val.invs.length) = .ok () := by
  cbv

private theorem glob_gruppe_ok_functions : ∀ f : Fin glob_gruppe_ok_elaborated.val.fns.length,
    (lowerFnAt glob_gruppe_ok_elaborated.val f).toOption.isSome = true ∧
      (fnAt glob_gruppe_ok_elaborated.val f).decreases = none := by
  refine UebersetzeProben2.singleFn_all glob_gruppe_ok_elaborated.val (by cbv) _ ?_
  constructor <;> cbv

private theorem glob_gruppe_ok_lowered : UebersetzeProben2.lowerStage glob_gruppe_ok_elaborated.val = "OK" :=
  UebersetzeProben2.lowerStage_checked _ glob_gruppe_ok_invariants glob_gruppe_ok_functions (by cbv)

theorem glob_gruppe_ok_stufe : stufe glob_gruppe_ok = "OK" :=
  stufe_after glob_gruppe_ok_text glob_gruppe_ok_lexed_zeuge glob_gruppe_ok_parsed.property
    glob_gruppe_ok_elaborated.property glob_gruppe_ok_lowered
theorem glob_gruppe_ok_traeger : traeger glob_gruppe_ok = some [[.inr 0, .inr 1]] :=
  InvariantPhases.traeger_after glob_gruppe_ok_text glob_gruppe_ok_lexed_zeuge glob_gruppe_ok_parsed.property
    glob_gruppe_ok_elaborated.property (by
      simp only [InvariantPhases.carrierLists, declOf]
      cbv)

/-- A mixed group of a table and a static under one lock; the writer touches only the static. -/
def gemischt_ok : String :=
  "module m { table T count 2 shared { slot { v : u32, } } static mut N : u32 = 0 shared; lock L protects { T, N } rank 0; group G over { T, N } { invariant J : T.slots[0].v <= N; } impl fn f() requires Held(L) effects { writes N } { N = 1; } }"

private def gemischt_ok_chunks : List Chunk :=
  [InvariantText.moduleM, InvariantText.sharedTableT, InvariantText.slotV, Chunk.closeSpace,
   InvariantText.staticN, InvariantText.lockTN, InvariantText.groupTN, InvariantText.compareT,
   InvariantText.readN, Chunk.closeSpace, InvariantText.plainFunction, InvariantText.heldL,
   InvariantText.writesN, InvariantText.writeN, Chunk.close]

private theorem gemischt_ok_text : gemischt_ok = String.ofList (characters gemischt_ok_chunks) := by
  rw [characters_join]
  cbv

private theorem gemischt_ok_lexed_zeuge :
    lexL (characters gemischt_ok_chunks) = .ok (tokens gemischt_ok_chunks) :=
  InvariantText.lexed _ (by cbv)

private def gemischt_ok_parsed :
    {items : List SItemTief // parseTopTief (tokens gemischt_ok_chunks) = .ok items} := by
  refine ⟨?items, ?parsed⟩
  case parsed => cbv <;> exact Eq.refl _

private def gemischt_ok_elaborated :
    {unit : UProg // elabU (pre108 gemischt_ok_parsed.val) = .ok unit} := by
  refine ⟨?unit, ?elaborated⟩
  case elaborated => cbv <;> exact Eq.refl _

private theorem gemischt_ok_invariants :
    lowerInvs gemischt_ok_elaborated.val (List.finRange gemischt_ok_elaborated.val.invs.length) = .ok () := by
  cbv

private theorem gemischt_ok_functions : ∀ f : Fin gemischt_ok_elaborated.val.fns.length,
    (lowerFnAt gemischt_ok_elaborated.val f).toOption.isSome = true ∧
      (fnAt gemischt_ok_elaborated.val f).decreases = none := by
  refine UebersetzeProben2.singleFn_all gemischt_ok_elaborated.val (by cbv) _ ?_
  constructor <;> cbv

private theorem gemischt_ok_lowered : UebersetzeProben2.lowerStage gemischt_ok_elaborated.val = "OK" :=
  UebersetzeProben2.lowerStage_checked _ gemischt_ok_invariants gemischt_ok_functions (by cbv)

theorem gemischt_ok_stufe : stufe gemischt_ok = "OK" :=
  stufe_after gemischt_ok_text gemischt_ok_lexed_zeuge gemischt_ok_parsed.property
    gemischt_ok_elaborated.property gemischt_ok_lowered
theorem gemischt_ok_traeger : traeger gemischt_ok = some [[.inl 0, .inr 0]] :=
  InvariantPhases.traeger_after gemischt_ok_text gemischt_ok_lexed_zeuge gemischt_ok_parsed.property
    gemischt_ok_elaborated.property (by
      simp only [InvariantPhases.carrierLists, declOf]
      cbv)

/-- Planted defect (`U003`): the writer of the static takes the group's guard only in a block. -/
def glob_u003_refused : String :=
  "module m { static mut A : u32 = 0 shared; static mut B : u32 = 0 shared; lock L protects { A, B } rank 0; group G over { A, B } { invariant J : A <= B; } impl fn f() effects { writes A, locks L } { locks L { A = 1; } } }"

private def glob_u003_refused_chunks : List Chunk :=
  [InvariantText.moduleM, InvariantText.staticA, InvariantText.staticB, InvariantText.lockAB,
   InvariantText.groupAB, InvariantText.compareAB, Chunk.closeSpace, InvariantText.plainFunction,
   InvariantText.locksA, InvariantText.lockedWriteA, Chunk.close]

private theorem glob_u003_refused_text : glob_u003_refused = String.ofList (characters glob_u003_refused_chunks) := by
  rw [characters_join]
  cbv

private theorem glob_u003_refused_lexed_zeuge :
    lexL (characters glob_u003_refused_chunks) = .ok (tokens glob_u003_refused_chunks) :=
  InvariantText.lexed _ (by cbv)

private def glob_u003_refused_parsed :
    {items : List SItemTief // parseTopTief (tokens glob_u003_refused_chunks) = .ok items} := by
  refine ⟨?items, ?parsed⟩
  case parsed => cbv <;> exact Eq.refl _

private theorem glob_u003_refused_elaborated :
    elabU (pre108 glob_u003_refused_parsed.val) = .error "a writer of an invariant's carrier does not hold all its locks" := by cbv

theorem glob_u003_refused_stufe :
    stufe glob_u003_refused = "elab: a writer of an invariant's carrier does not hold all its locks" :=
  stufe_elab_error glob_u003_refused_text glob_u003_refused_lexed_zeuge glob_u003_refused_parsed.property
    glob_u003_refused_elaborated

/-- Planted defect: the predicate reads a static (`N`) under the same lock that the group does not declare. -/
def undeklariert_refused : String :=
  "module m { table T count 2 shared { slot { v : u32, } } static mut N : u32 = 0 shared; lock L protects { T, N } rank 0; group G over { T } { invariant J : T.slots[0].v <= N; } impl fn f(i : index into T) requires Held(L) effects { writes T.slots } { T.slots[i].v = 1; } }"

private def undeklariert_refused_chunks : List Chunk :=
  [InvariantText.moduleM, InvariantText.sharedTableT, InvariantText.slotV, Chunk.closeSpace,
   InvariantText.staticN, InvariantText.lockTN, InvariantText.groupT, InvariantText.compareT,
   InvariantText.readN, Chunk.closeSpace, InvariantText.indexFunction, InvariantText.heldL,
   InvariantText.writesT, InvariantText.writeT, Chunk.close]

private theorem undeklariert_refused_text : undeklariert_refused = String.ofList (characters undeklariert_refused_chunks) := by
  rw [characters_join]
  cbv

private theorem undeklariert_refused_lexed_zeuge :
    lexL (characters undeklariert_refused_chunks) = .ok (tokens undeklariert_refused_chunks) :=
  InvariantText.lexed _ (by cbv)

private def undeklariert_refused_parsed :
    {items : List SItemTief // parseTopTief (tokens undeklariert_refused_chunks) = .ok items} := by
  refine ⟨?items, ?parsed⟩
  case parsed => cbv <;> exact Eq.refl _

private def undeklariert_refused_elaborated :
    {unit : UProg // elabU (pre108 undeklariert_refused_parsed.val) = .ok unit} := by
  refine ⟨?unit, ?elaborated⟩
  case elaborated => cbv <;> exact Eq.refl _

private theorem undeklariert_refused_invariants :
    lowerInvs undeklariert_refused_elaborated.val (List.finRange undeklariert_refused_elaborated.val.invs.length) =
      .error "an invariant reads a carrier it does not declare" := by cbv

private theorem undeklariert_refused_lowered : UebersetzeProben2.lowerStage undeklariert_refused_elaborated.val =
    "lower: an invariant reads a carrier it does not declare" :=
  InvariantPhases.lowerStage_invariant_error _ _ undeklariert_refused_invariants

theorem undeklariert_refused_stufe :
    stufe undeklariert_refused = "lower: an invariant reads a carrier it does not declare" :=
  stufe_after undeklariert_refused_text undeklariert_refused_lexed_zeuge undeklariert_refused_parsed.property
    undeklariert_refused_elaborated.property undeklariert_refused_lowered

/-- Planted defect: a carrier that names no table and no static. -/
def traeger_unbekannt_refused : String :=
  "module m { static mut A : u32 = 0 shared; lock L protects { A } rank 0; group G over { A, Z } { invariant J : A <= 9; } impl fn f() { } }"

private def traeger_unbekannt_refused_chunks : List Chunk :=
  [InvariantText.moduleM, InvariantText.staticA, InvariantText.lockA, InvariantText.groupAZ,
   InvariantText.compareA, Chunk.closeSpace, InvariantText.emptyFunction, Chunk.close]

private theorem traeger_unbekannt_refused_text : traeger_unbekannt_refused = String.ofList (characters traeger_unbekannt_refused_chunks) := by
  rw [characters_join]
  cbv

private theorem traeger_unbekannt_refused_lexed_zeuge :
    lexL (characters traeger_unbekannt_refused_chunks) = .ok (tokens traeger_unbekannt_refused_chunks) :=
  InvariantText.lexed _ (by cbv)

private def traeger_unbekannt_refused_parsed :
    {items : List SItemTief // parseTopTief (tokens traeger_unbekannt_refused_chunks) = .ok items} := by
  refine ⟨?items, ?parsed⟩
  case parsed => cbv <;> exact Eq.refl _

private theorem traeger_unbekannt_refused_elaborated :
    elabU (pre108 traeger_unbekannt_refused_parsed.val) = .error "invariant carrier without G form, or ambiguous" := by cbv

theorem traeger_unbekannt_refused_stufe :
    stufe traeger_unbekannt_refused = "elab: invariant carrier without G form, or ambiguous" :=
  stufe_elab_error traeger_unbekannt_refused_text traeger_unbekannt_refused_lexed_zeuge traeger_unbekannt_refused_parsed.property
    traeger_unbekannt_refused_elaborated

end Gabbro.Grammatik.Parser.UebersetzeProben41
