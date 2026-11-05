module
public import Stage0.Frontend.Witnesses.Constants.Input
public import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben2Basis
import Init.Data.String.Length

@[expose] public section
namespace Gabbro.Stage0.Frontend.ConstPhases
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- A certificate for a fragment of the actual scanner, with its suffix still symbolic. -/
structure ScanPiece (characters : List Char) where
  tokens : List Token
  steps : Nat
  equation : ∀ rest fuel, scan false (characters ++ rest) (fuel + steps) =
    tokens.foldr (fun token answer => Except.map (token :: ·) answer)
      (scan false rest fuel)

def ScanPiece.append {left right : List Char}
    (first : ScanPiece left) (second : ScanPiece right) : ScanPiece (left ++ right) where
  tokens := first.tokens ++ second.tokens
  steps := first.steps + second.steps
  equation := by
    intro rest fuel
    rw [List.append_assoc]
    have reassociate : fuel + (first.steps + second.steps) =
        (fuel + second.steps) + first.steps := by omega
    rw [reassociate, first.equation, second.equation, List.foldr_append]

theorem ScanPiece.lexed {characters : List Char} (piece : ScanPiece characters)
    (room : piece.steps ≤ characters.length + 1) :
    lexL characters = .ok (piece.tokens ++ [.ende]) := by
  have equation := piece.equation [] (characters.length + 1 - piece.steps)
  have fuel : characters.length + 1 - piece.steps + piece.steps = characters.length + 1 :=
    Nat.sub_add_cancel room
  simpa only [lexL, List.append_nil, fuel, Gabbro.Grammatik.Parser.UebersetzeProben2.token_maps,
    scan, Except.map] using equation

/-- The existing lowering theorem assembles all actual function certificates and measures. -/
theorem lowered {unit : UProg} (noInvs : unit.invs = [])
    (functions : ∀ f : Fin unit.fns.length,
      (lowerFnAt unit f).toOption.isSome = true ∧ (fnAt unit f).decreases = none)
    (contracts : contractGate unit = true) :
    ∃ raw fs, lowerAllg unit = .ok (raw, fs) := by
  have stage := Gabbro.Grammatik.Parser.UebersetzeProben2.lowerStage_ok
    unit noInvs functions contracts
  cases actual : lowerAllg unit with
  | error error =>
    unfold Gabbro.Grammatik.Parser.UebersetzeProben2.lowerStage at stage
    rw [actual] at stage
    have impossible := congrArg String.length stage
    rw [String.length_append] at impossible
    change 7 + error.length = 2 at impossible
    omega
  | ok pair => exact ⟨pair.1, pair.2, actual⟩

end Gabbro.Stage0.Frontend.ConstPhases

