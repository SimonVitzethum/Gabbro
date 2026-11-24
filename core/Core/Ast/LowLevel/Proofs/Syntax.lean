module

public import Core.Ast.LowLevel.Obligations

/-!
# Low-level lexical and grammatical proofs

Prove each statement for every `LowLevel.Form`. Use the shared lexical adapter
and canonical printer certificates. Invert `TypeReads` for the view's operand.

- `ParseAussage`
- `InversionAussage`
- `EindeutigAussage`
- `DruckAussage`
-/

namespace Gabbro.Core.Ast.LowLevel

open Text

theorem druckAussage_view : DruckAussage .view := by
  intro tree valid
  cases tree with
  | view region type =>
    have read : TypeReads (type.printPieces.map PrintedToken.value) type [] := by
      have prints := type.printReads (rest := []) valid (fun _ impossible => nomatch impossible)
      simpa only [List.append_nil] using prints
    have production : (Tree.view region type).production
        ((Tree.view region type).printPieces.map PrintedToken.value) :=
      ⟨_, List.map_append, read⟩
    obtain ⟨pieces, lexed, aligned⟩ := PrintedToken.renderLexed 0 (Tree.view region type).printPieces
    have symbols : ∀ ts : List LocatedToken,
        DerivesSymbols (tokenGrammar (fun tokens (tree : Tree .view) => tree.production tokens))
          (ts.map Symbol.terminal) ts := by
      intro ts
      induction ts with
      | nil => exact .nil
      | cons _ _ ih => exact .terminal ih
    refine ⟨production, True.intro, pieces, lexed, .production ?_ (symbols (semanticTokens pieces))⟩
    refine ⟨semanticTokens pieces, rfl, ?_⟩
    change (Tree.view region type).production (canonicalTokens pieces)
    rw [aligned]
    exact production

end Gabbro.Core.Ast.LowLevel
