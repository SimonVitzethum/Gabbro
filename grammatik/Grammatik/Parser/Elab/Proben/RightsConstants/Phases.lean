module
public import Grammatik.Parser.Elab.Proben.RightsConstants.Scanning
public import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben2Basis
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

public section
namespace Gabbro.Grammatik.Parser.UebersetzeProben11.Phases
open Gabbro.Grammatik Gabbro.Grammatik.Parser
open Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2
open scoped Gabbro.Grammatik.Parser.UebersetzeProben11.Phases
set_option maxRecDepth 100000

/-- Only the actual frontend phases are replayed; the continuation remains symbolic. -/
theorem frontend {source : String} (input : Input source) {items : List SItemTief} {unit : UProg}
    (parsed : parseTopTief input.tokens = .ok items)
    (elaborated : elabU (pre108 items) = .ok unit) : UebersetzeProben.Frontend source unit := by
  intro after
  rw [input.text, lex_ofList, input.lexed]
  dsimp only
  rw [parsed]
  dsimp only
  rw [elaborated]

theorem elab_error {source : String} (input : Input source) {items : List SItemTief} {error : String}
    (parsed : parseTopTief input.tokens = .ok items)
    (rejected : elabU (pre108 items) = .error error) :
    UebersetzeProben.stufe source = "elab: " ++ error := by
  rw [input.text]
  unfold UebersetzeProben.stufe
  rw [lex_ofList, input.lexed]
  dsimp only
  rw [parsed]
  dsimp only
  rw [rejected]

theorem lower_ok {source : String} (input : Input source) {items : List SItemTief} {unit : UProg}
    (parsed : parseTopTief input.tokens = .ok items)
    (elaborated : elabU (pre108 items) = .ok unit) (invariants : unit.invs = [])
    (contracts : contractGate unit = true)
    (functions : ∀ f : Fin unit.fns.length,
      (lowerFnAt unit f).toOption.isSome = true ∧ (fnAt unit f).decreases = none) :
    UebersetzeProben.stufe source = "OK" :=
  UebersetzeProben.stufe_ok (frontend input parsed elaborated)
    (Gabbro.Grammatik.Uebersetzung.LibraryFixtureProofs.lowering_ok
      unit invariants contracts functions)

theorem lower_error {source : String} (input : Input source) {items : List SItemTief} {unit : UProg}
    {error : String} (parsed : parseTopTief input.tokens = .ok items)
    (elaborated : elabU (pre108 items) = .ok unit) (invariants : unit.invs = [])
    (outcomes : ∀ f : Fin unit.fns.length,
      lowerFnAt unit f = .error error ∨ (lowerFnAt unit f).toOption.isSome = true)
    (bad : ∃ f : Fin unit.fns.length, lowerFnAt unit f = .error error) :
    UebersetzeProben.stufe source = "lower: " ++ error := by
  apply UebersetzeProben.stufe_after (frontend input parsed elaborated)
  exact UebersetzeProben2.lowerStage_error unit error invariants outcomes bad

theorem stage_counts {source : String} (input : Input source) {items : List SItemTief} {unit : UProg}
    {expected : List Nat} (parsed : parseTopTief input.tokens = .ok items)
    (elaborated : elabU (pre108 items) = .ok unit)
    (counts : (List.finRange unit.marken.length).map ((declOf unit).stufen) = expected) :
    sourceMarkStageCounts source = some expected := by
  unfold sourceMarkStageCounts
  rw [input.text, lex_ofList, input.lexed]
  dsimp only [Except.toOption, bind, Option.bind]
  rw [parsed]
  dsimp only [Except.toOption, bind, Option.bind]
  rw [elaborated]
  change some ((List.finRange unit.marken.length).map ((declOf unit).stufen)) = some expected
  exact congrArg some counts

-- Classify the actual finite carrier only after the complete unit has been inferred.
-- The closed count equation is established independently of this caller index.
scoped macro "rights_members " step:tactic : tactic => `(tactic| (
  rintro ⟨index, bound⟩
  have small : index < 2 := by omega
  have choices : index = 0 ∨ index = 1 := by omega
  rcases choices with zero | one
  · subst index
    $step:tactic
  · subst index
    first | omega | $step:tactic))

scoped macro "rights_elab_error " supplied:term " with_reason " error:term : tactic => `(tactic| (
  let input := $supplied
  let items : List SItemTief := ?items
  have parsed : parseTopTief input.tokens = .ok items := by cbv <;> exact Eq.refl _
  have rejected : elabU (pre108 items) = .error $error := by cbv <;> exact Eq.refl _
  exact elab_error input parsed rejected))

scoped macro "rights_ok " supplied:term : tactic => `(tactic| (
  let input := $supplied
  let items : List SItemTief := ?items
  have parsed : parseTopTief input.tokens = .ok items := by cbv <;> exact Eq.refl _
  let unit : UProg := ?unit
  have elaborated : elabU (pre108 items) = .ok unit := by cbv <;> exact Eq.refl _
  let size : Nat := ?size
  have count : unit.fns.length = size := by cbv <;> exact Eq.refl _
  have small : size ≤ 2 := by cbv <;> omega
  apply lower_ok input parsed elaborated
  · cbv
  · cbv
  · rights_members (constructor <;> cbv)))

scoped macro "rights_lower_error " supplied:term " with_reason " error:term " at_member " number:term : tactic =>
  `(tactic| (
    let input := $supplied
    let items : List SItemTief := ?items
    have parsed : parseTopTief input.tokens = .ok items := by cbv <;> exact Eq.refl _
    let unit : UProg := ?unit
    have elaborated : elabU (pre108 items) = .ok unit := by cbv <;> exact Eq.refl _
    let size : Nat := ?size
    have count : unit.fns.length = size := by cbv <;> exact Eq.refl _
    have small : size ≤ 2 := by cbv <;> omega
    apply lower_error (error := $error) input parsed elaborated
    · cbv
    · rights_members (first | (left; cbv; done) | (right; cbv; done))
    · refine ⟨⟨$number, by omega⟩, ?_⟩
      cbv))

scoped macro "rights_counts " supplied:term : tactic => `(tactic| (
  let input := $supplied
  let items : List SItemTief := ?items
  have parsed : parseTopTief input.tokens = .ok items := by cbv <;> exact Eq.refl _
  let unit : UProg := ?unit
  have elaborated : elabU (pre108 items) = .ok unit := by cbv <;> exact Eq.refl _
  apply stage_counts input parsed elaborated
  cbv))

end Gabbro.Grammatik.Parser.UebersetzeProben11.Phases
