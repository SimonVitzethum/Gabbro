module
public import Stage0.IRBild
import Stage0.Frontend.Witnesses.Constants.SourcePackets
import Stage0.Frontend.Witnesses.Constants.ProgramPackets
import all Grammatik.Parser.Lex.Lexer.Teil1
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
import all Grammatik.Parser.Elab.Konst.Ersetzung
import all Grammatik.Parser.Elab.Konst.ErsetzungTor
import all Grammatik.Parser.Elab.Konst.Scope
import all Grammatik.Parser.Elab.Konst.Replacement
import all Grammatik.Parser.Elab.Konst.Scalar.Model
import all Grammatik.Parser.Elab.Konst.Scalar.Expression
import all Grammatik.Parser.Elab.Konst.Scalar.Names
import all Grammatik.Parser.Elab.Konst.Scalar.Arguments
import all Grammatik.Parser.Elab.Konst.Scalar.KExpr
import all Grammatik.Parser.Elab.Konst.Scalar.Export
import all Grammatik.Parser.Elab.Konst.Values.Expression
import all Grammatik.Parser.Elab.Konst.Values.Quotation
import all Grammatik.Parser.Elab.Konst.Values.Export
import all Stage0.Profil
import all Stage0.Frontend.AliasOrder
import all Stage0.Frontend.Correctness
import all Stage0.Frontend.Environments
import all Stage0.Frontend.EnvironmentsPart1
import all Stage0.Frontend.DependentScopes
import all Stage0.Frontend.DependentScopesa
import all Stage0.Frontend.Functions
import all Stage0.Frontend.Guard
import all Stage0.Frontend.Constants.ConstantScopes
import all Stage0.Frontend.Constants.ConstantMeaning
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

namespace Gabbro.Stage0.ProfileMismatchWitness

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Frontend.ConstPhases

set_option maxRecDepth 2000
set_option maxHeartbeats 400000

def text : String :=
  "module profile_mismatch_probe { profile { arch x86_64; arch aarch64; }; impl fn main() -> u64 in 0 .. 100 { return 23; } }"

-- Each cut is an equation of the existing scanner with symbolic suffix and fuel.
private def scanPart0 : ScanPiece ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'p', 'r', 'o', 'f', 'i', 'l', 'e', '_', 'm', 'i', 's', 'm', 'a', 't', 'c', 'h', '_', 'p', 'r', 'o', 'b', 'e', ' ', '{', ' ', 'p', 'r', 'o', 'f', 'i', 'l', 'e', ' ', '{', ' '] := by
  let tokens := ((lexL ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'p', 'r', 'o', 'f', 'i', 'l', 'e', '_', 'm', 'i', 's', 'm', 'a', 't', 'c', 'h', '_', 'p', 'r', 'o', 'b', 'e', ' ', '{', ' ', 'p', 'r', 'o', 'f', 'i', 'l', 'e', ' ', '{', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 5, equation := ?_ }
  intro rest fuel
  cbv

private def scanPart1 : ScanPiece ['a', 'r', 'c', 'h', ' ', 'x', '8', '6', '_', '6', '4', ';', ' ', 'a', 'r', 'c', 'h', ' ', 'a', 'a', 'r', 'c', 'h', '6', '4', ';', ' ', '}', ';', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' '] := by
  let tokens := ((lexL ['a', 'r', 'c', 'h', ' ', 'x', '8', '6', '_', '6', '4', ';', ' ', 'a', 'r', 'c', 'h', ' ', 'a', 'a', 'r', 'c', 'h', '6', '4', ';', ' ', '}', ';', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 7, equation := ?_ }
  intro rest fuel
  cbv

private def scanPart2 : ScanPiece ['m', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'u', '6', '4', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', '0', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', '2', '3', ';', ' ', '}', ' ', '}'] := by
  let tokens := ((lexL ['m', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'u', '6', '4', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', '0', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', '2', '3', ';', ' ', '}', ' ', '}']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 11, equation := ?_ }
  intro rest fuel
  cbv

private def scanned := ((scanPart0).append scanPart1).append scanPart2

private theorem lexed : lex text = .ok (scanned.tokens ++ [.ende]) := by
  have characters : text = String.ofList ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'p', 'r', 'o', 'f', 'i', 'l', 'e', '_', 'm', 'i', 's', 'm', 'a', 't', 'c', 'h', '_', 'p', 'r', 'o', 'b', 'e', ' ', '{', ' ', 'p', 'r', 'o', 'f', 'i', 'l', 'e', ' ', '{', ' ', 'a', 'r', 'c', 'h', ' ', 'x', '8', '6', '_', '6', '4', ';', ' ', 'a', 'r', 'c', 'h', ' ', 'a', 'a', 'r', 'c', 'h', '6', '4', ';', ' ', '}', ';', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'u', '6', '4', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', '0', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', '2', '3', ';', ' ', '}', ' ', '}'] := by cbv
  rw [characters, lex_ofList]
  exact scanned.lexed (by cbv)

private theorem parsed : (parseTopTief (scanned.tokens ++ [.ende])).toOption.isSome = true := by
  cbv

private def items : List SItemTief :=
  (parseTopTief (scanned.tokens ++ [.ende])).toOption.get parsed

private theorem preparation_refused : Profil.prepareItems {} items =
    .error "ir: profile binding refused: modes, assumptions or library requirements are not consistent" := by
  cbv

private theorem source_refused : Frontend.source text =
    .error "ir: profile binding refused: modes, assumptions or library requirements are not consistent" := by
  unfold Frontend.source
  rw [lexed, except_ok_get parsed]
  dsimp only
  rw [preparation_refused]

private theorem compilation_refused : compile text =
    .error "ir: profile binding refused: modes, assumptions or library requirements are not consistent" := by
  unfold compile
  rw [source_refused]
  rfl

def candidate : Except String (Emitted text 64) := emit text 64

/-- Conflicting profile modes are refused by name: the checked binding is
    inconsistent, so no image is built for it. -/
theorem candidate_refused :
    (match candidate with | .error message => some message | .ok _ => none) =
      some "ir: profile binding refused: modes, assumptions or library requirements are not consistent" := by
  unfold candidate emit
  rw [compilation_refused]
  rfl

end Gabbro.Stage0.ProfileMismatchWitness
