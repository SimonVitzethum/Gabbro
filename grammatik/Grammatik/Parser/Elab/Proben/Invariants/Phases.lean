module

public import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben3
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a

@[expose] public section

namespace Gabbro.Grammatik.Parser.InvariantPhases

open Gabbro.Grammatik Uebersetze UebersetzeAllg UebersetzeAllg2

/-- Observe the actual declaration, including its invariant-carrier guard. -/
def carrierLists (u : UProg) : List (List (Nat ⊕ Nat)) :=
  (List.finRange u.invs.length).map fun (i : Fin u.invs.length) =>
    ((declOf u).traeger i).map (Sum.map (fun (t : Fin u.tabs.length) => t.val)
      (fun (g : Fin u.globs.length) => g.val))

/-- The source-level declaration observer shared by table and static probes. -/
def traeger (source : String) : Option (List (List (Nat ⊕ Nat))) := do
  let tokens ← (lex source).toOption
  let items ← (parseTopTief tokens).toOption
  let unit ← (elabU (pre108 items)).toOption
  pure (carrierLists unit)

/-- Link carrier observations through the same certified frontend as `stufe`. -/
theorem traeger_after {source : String} {characters : List Char} {tokens : List Token}
    {items : List SItemTief} {unit : UProg} {expected : List (List (Nat ⊕ Nat))}
    (text : source = String.ofList characters) (lexed : lexL characters = .ok tokens)
    (parsed : parseTopTief tokens = .ok items) (elaborated : elabU (pre108 items) = .ok unit)
    (observed : carrierLists unit = expected) : traeger source = some expected := by
  rw [text]
  unfold traeger
  rw [lex_ofList, lexed]
  dsimp only [Except.toOption, bind, Option.bind]
  rw [parsed]
  dsimp only [Except.toOption, bind, Option.bind]
  rw [elaborated]
  exact congrArg some observed

/-- A failed invariant precedes function assembly and preserves its diagnostic. -/
theorem lowerStage_invariant_error (unit : UProg) (error : String)
    (failed : lowerInvs unit (List.finRange unit.invs.length) = .error error) :
    UebersetzeProben2.lowerStage unit = "lower: " ++ error := by
  have lowered : lowerAllg unit = .error error := by
    unfold lowerAllg
    split
    · rename_i reason found
      rw [failed] at found
      cases found
      rfl
    · rename_i value found
      rw [failed] at found
      cases found
  unfold UebersetzeProben2.lowerStage
  rw [lowered]

end Gabbro.Grammatik.Parser.InvariantPhases
