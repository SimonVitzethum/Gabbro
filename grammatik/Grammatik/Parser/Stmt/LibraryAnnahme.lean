module

public import Grammatik.Logik.Vertraege.Uebersetzung
public import Grammatik.Parser.Stmt.LibraryFixtures
public import Grammatik.Parser.Stmt.LibraryCertificates
public import Grammatik.Parser.Stmt.LibraryExport
public import Grammatik.Zielsatz.Kern.Akzeptiert
public import Grammatik.Nebenlaeufigkeit.Sperren.SperreSem
import all Grammatik.Parser.Stmt.LibraryExport
import all Grammatik.Parser.Stmt.LibraryTranslationFixtures
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil12
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
import all Grammatik.Parser.Elab.Generic.StaticConformance
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest1
import all Grammatik.Parser.Elab.UebersetzeAllg3.Body
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a
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

namespace Gabbro.Grammatik.Uebersetzung

open Gabbro.Grammatik.Parser
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! ## C02 item 8: connected source/image correctness and refusal witnesses.

    The generic lowering covers the expanded call: source text with an
    (unqualified) library call elaborates through the actual export path
    to an ordinary unit, lowers with `lowerAllg`, and the checker Bool
    holds -- on the non-degenerate identity fixture with a real call, not
    a degenerate empty unit. Layout and image, C14/C08 and Stage-0
    closure stay with their owners. The certified expansion can never hit
    the lowering's C02 refusal (`uAnwReiheCore` refuses `lcall`/`bindLib`
    by name): an expanded statement is definitionally no library call. -/

-- Reuse the checked ordinary-source tokens, parser equation and exact text
-- bridge. Instantiate getter laws only after they have been proved symbolically.
private theorem ident_tokens : translationTokens false = translationPhaseTokens false := by
  unfold translationTokens
  exact tokens_from_text (translationText false) (translationCharacters false)
    (translationPhaseTokens false) (translation_text false) (translation_lexed false)

private theorem items_from_tokens (original tokens : List Token) (items : List SItemTief)
    (tokenEq : original = tokens) (parsed : parseTopTief tokens = .ok items) :
    (parseTopTief original).toOption.getD [] = items := by
  rw [tokenEq, parsed]
  rfl

private theorem ident_items : translationItems false =
    LibraryFixtureProofs.parsedFixture 2 (translationResult false) [.num 3, .num 5] := by
  unfold translationItems
  exact items_from_tokens (translationTokens false) (translationPhaseTokens false)
    (LibraryFixtureProofs.parsedFixture 2 (translationResult false) [.num 3, .num 5])
    ident_tokens (translation_parsed false)

attribute [local cbv_opaque] lowStufe lowSeqL lowStructL lowEndL uFloatLimit
attribute [local cbv_eval] export_seq_succ lowStructL_succ lowEndL_succ
  lowStufe_seq lowStufe_struct lowStufe_ende

-- The actual whole ordinary caller unit has two implemented functions after
-- its translator declaration is consumed. Check this against its own carrier.
local macro "ident_functions" : tactic => `(tactic| (
  rintro ⟨index, bound⟩
  have size : index < 2 := bound
  have choices : index = 0 ∨ index = 1 := by omega
  rcases choices with first | second
  · subst index
    cbv <;> exact Eq.refl _
  · subst index
    cbv <;> exact Eq.refl _))

-- Use LibraryExport's one generic assembler/checker certificate. The values
-- here are inferred from successful canonical producers, never reconstructed.
private theorem ident_phases :
    (∃ expanded, exportLibraryUnit (uMembers (pre108 (translationItems false))) = .ok expanded ∧
      alleOhneBibliothek expanded = true) ∧
    ∃ unit, elabU (pre108 (translationItems false)) = .ok unit ∧ ExportFacts unit := by
  rw [ident_items]
  constructor
  · refine ⟨?expanded, ?produced, ?ordinary⟩
    case produced => cbv <;> exact Eq.refl _
    case ordinary => cbv
  · refine ⟨?unit, ?made, ?facts⟩
    case made => cbv <;> exact Eq.refl _
    case facts =>
      refine {
        gate := by cbv
        invs := by cbv
        contracts := by cbv
        measures := by ident_functions
        functions := ?_ }
      refine functions_of_success _ ?produced ?safe
      case produced => ident_functions
      case safe => intro invariants pointers foreigns; cbv

/-- The identity caller unit through the export: the source text with an
    unqualified library call elaborates to an ordinary unit. -/
def exportIdentEinheit : UProg :=
  (elabU (pre108 (translationItems false))).toOption.getD { tabs := [], locks := [], fns := [] }

theorem export_ident_elab_zeuge :
    (elabU (pre108 (translationItems false))).toOption.isSome = true := by
  obtain ⟨unit, made, _⟩ := ident_phases.2
  rw [made]
  rfl

private theorem ident_export_facts : ExportFacts exportIdentEinheit := by
  obtain ⟨unit, made, facts⟩ := ident_phases.2
  unfold exportIdentEinheit
  rw [made]
  exact facts

/-- The export leaves no ignored source duty behind on the fixture. -/
theorem export_ident_tor_zeuge : exportIdentEinheit.exportGate = .ok () := ident_export_facts.gate

/-- The expanded source: the pre-pass output on the fixture members. -/
def exportIdentErweitert : List SItemTief :=
  (exportLibraryUnit (uMembers (pre108 (translationItems false)))).toOption.getD []

/-- The pre-pass ran: every expanded body is ordinary. -/
theorem export_ident_ohne_zeuge :
    Gabbro.Grammatik.Uebersetzung.alleOhneBibliothek exportIdentErweitert = true := by
  obtain ⟨expanded, produced, ordinary⟩ := ident_phases.1
  unfold exportIdentErweitert
  rw [produced]
  exact ordinary

theorem export_ident_lower_ok :
    (lowerAllg exportIdentEinheit).toOption.isSome = true := export_lowered ident_export_facts

def exportIdentGesenkert :
    Programm (declOf exportIdentEinheit) × List (declOf exportIdentEinheit).Fn :=
  (lowerAllg exportIdentEinheit).toOption.get export_ident_lower_ok

-- Normalize the actual selected-image alias before applying the success law.
private theorem ident_emitted : lowerAllg exportIdentEinheit = .ok exportIdentGesenkert := by
  unfold exportIdentGesenkert
  exact except_ok_get (x := lowerAllg exportIdentEinheit) export_ident_lower_ok

/-- The connected verdict: source text with an unqualified library call
    elaborates, lowers, and the checker Bool holds. The enumerations are
    complete by construction (`finRange` over the elaborated tables,
    statics and locks; the lowered functions; no starts, since the fixture
    declares no `concurrent` item). -/
theorem export_ident_akzeptiert_zeuge :
    Gabbro.Grammatik.Akzeptiert exportIdentGesenkert.1 (Gabbro.Grammatik.SperrInv.leer _)
      exportIdentGesenkert.2 (List.finRange exportIdentEinheit.locks.length)
      ((List.finRange exportIdentEinheit.tabs.length).map Sum.inl ++
        (List.finRange exportIdentEinheit.globs.length).map Sum.inr) [] = true := by
  exact export_checked ident_export_facts ident_emitted

/-- The end-to-end chain in one witness: source text to accepted unit. -/
theorem export_ident_kette_zeuge :
    (elabU (pre108 (translationItems false))).toOption.isSome = true ∧
    (lowerAllg exportIdentEinheit).toOption.isSome = true ∧
    Gabbro.Grammatik.Akzeptiert exportIdentGesenkert.1 (Gabbro.Grammatik.SperrInv.leer _)
      exportIdentGesenkert.2 (List.finRange exportIdentEinheit.locks.length)
      ((List.finRange exportIdentEinheit.tabs.length).map Sum.inl ++
        (List.finRange exportIdentEinheit.globs.length).map Sum.inr) [] = true :=
  ⟨export_ident_elab_zeuge, export_ident_lower_ok, export_ident_akzeptiert_zeuge⟩

/-- An expanded statement is definitionally no `lcall`: the lowering's
    C02 refusal is unreachable on certified expansions. -/
theorem ohneBibliothekAnw_kein_lcall (c : SLibraryCall) :
    ohneBibliothekAnw (.lcall c) = false := rfl

/-- An expanded statement is definitionally no `bindLib` either. -/
theorem ohneBibliothekAnw_kein_bindLib (m : Bool) (x : String) (ty : Option STyp)
    (c : SLibraryCall) :
    ohneBibliothekAnw (.bindLib m x ty c) = false := rfl

/-- Every certified expansion takes the ordinary lowering path: it is
    neither an `lcall` nor a `bindLib`, in either call form, so the
    generic lowering (`uAnwReiheCore`, which refuses both by name) treats
    it exactly like an ordinary call. -/
theorem libraryExpansion_trifft_kein_bibliothekruf {source : LibrarySource} {u : UProg}
    {decl : TranslationDecl source u} {certificate : TranslationCertificate decl}
    {payload : LibraryPayload certificate} (expansion : LibraryExpansion payload)
    (c : SLibraryCall) :
    expansion.aufruf ≠ .lcall c ∧
      (∀ m x ty, expansion.aufruf ≠ .bindLib m x ty c) := by
  have h := libraryExpansion_ohneBibliothek expansion
  constructor
  · intro heq
    have same : ohneBibliothekAnw (.lcall c) = true := heq ▸ h
    rw [ohneBibliothekAnw_kein_lcall] at same
    exact absurd same (by decide)
  · intro m x ty heq
    have same : ohneBibliothekAnw (.bindLib m x ty c) = true := heq ▸ h
    rw [ohneBibliothekAnw_kein_bindLib] at same
    exact absurd same (by decide)

end Gabbro.Grammatik.Uebersetzung
