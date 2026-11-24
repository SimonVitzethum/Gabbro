module

public import Core.Text.Grammar

@[expose] public section

namespace Gabbro.Core.Text

/-- Drop spans and trivia. Literal tokens already carry their decoded values. -/
def canonicalTokens (pieces : List Piece) : List Token :=
  (semanticTokens pieces).map LocatedToken.value

/-- The lexical equivalence used by round trips. Both texts have complete
    lexical derivations and the same ordered semantic tokens. -/
def Canonicalisation (written canonical : RawText) : Prop :=
  ∃ left right, Lexed written left ∧ Lexed canonical right ∧
    canonicalTokens left = canonicalTokens right

theorem Canonicalisation.symm {a b : RawText} (same : Canonicalisation a b) :
    Canonicalisation b a := by
  obtain ⟨left, right, lexLeft, lexRight, equality⟩ := same
  exact ⟨right, left, lexRight, lexLeft, equality.symm⟩

theorem Canonicalisation.refl {text pieces} (read : Lexed text pieces) :
    Canonicalisation text text :=
  ⟨pieces, pieces, read, read, rfl⟩

/-- Removing trivia relates different source texts. -/
theorem canonicalisation_erfuellbar :
    ∃ written canonical, written ≠ canonical ∧ Canonicalisation written canonical := by
  obtain ⟨written, pieces, nonempty, trivia, read⟩ := lexicalStep_erfuellbar 0
  have same : canonicalTokens pieces = canonicalTokens [] :=
    congrArg (List.map LocatedToken.value) trivia
  exact ⟨written, [], nonempty, pieces, [], read, .endOfText 0, same⟩

end Gabbro.Core.Text
