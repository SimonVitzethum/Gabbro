module

public import Core.Text.Printing

@[expose] public section

namespace Gabbro.Core.Text

/-- A declarative, deterministic token judgment and its canonical printing rules.
    The whole-source adapter supplies lexical coverage and locates the terminals. -/
structure Syntax (Tree : Type) where
  reads : List Token → Tree → Prop
  unique : ∀ {tokens a b}, reads tokens a → reads tokens b → a = b
  printPieces : Tree → List PrintedToken
  reads_print : ∀ tree, reads ((printPieces tree).map PrintedToken.value) tree

def tokenGrammar (reads : List Token → Tree → Prop) : Grammar Tree where
  root := fun _ => True
  production := fun tree symbols =>
    ∃ tokens : List LocatedToken, symbols = tokens.map Symbol.terminal ∧ reads (tokens.map LocatedToken.value) tree

def Syntax.grammar (rules : Syntax Tree) : Grammar Tree := tokenGrammar rules.reads

theorem Syntax.derives_iff (rules : Syntax Tree) :
    Derives rules.grammar tree tokens ↔ rules.reads (tokens.map LocatedToken.value) tree := by
  constructor
  · intro parsed
    cases parsed with
    | production production children =>
      obtain ⟨expected, rfl, reads⟩ := production
      rw [children.terminalTokens]
      exact reads
  · intro reads
    have symbols : ∀ (ts : List LocatedToken),
        DerivesSymbols rules.grammar (ts.map Symbol.terminal) ts := by
      intro ts
      induction ts with
      | nil => exact .nil
      | cons t ts ih => exact .terminal ih
    exact .production ⟨tokens, rfl, reads⟩ (symbols tokens)

theorem Syntax.parse_iff (rules : Syntax Tree) :
    Parse rules.grammar text tree ↔
      ∃ pieces, Lexed text pieces ∧ rules.reads (canonicalTokens pieces) tree := by
  constructor
  · rintro ⟨_, pieces, lexical, grammatical⟩
    exact ⟨pieces, lexical, rules.derives_iff.mp grammatical⟩
  · rintro ⟨pieces, lexical, grammatical⟩
    exact ⟨True.intro, pieces, lexical, rules.derives_iff.mpr grammatical⟩

def Syntax.print (rules : Syntax Tree) (tree : Tree) : RawText :=
  PrintedToken.render (rules.printPieces tree)

theorem Syntax.parse_print (rules : Syntax Tree) (tree : Tree) :
    Parse rules.grammar (rules.print tree) tree := by
  obtain ⟨pieces, lexical, align⟩ := PrintedToken.renderLexed 0 (rules.printPieces tree)
  exact rules.parse_iff.mpr ⟨pieces, lexical, align.symm ▸ rules.reads_print tree⟩

theorem Syntax.parse_deterministic (rules : Syntax Tree) (left : Parse rules.grammar text a)
    (right : Parse rules.grammar text b) : a = b := by
  obtain ⟨pieces, lex, reads⟩ := rules.parse_iff.mp left
  obtain ⟨pieces', lex', reads'⟩ := rules.parse_iff.mp right
  have same := LexedAt.deterministic lex lex'
  exact rules.unique reads (same.symm ▸ reads')

/-- Source normalization preserves the tree of the declarative production.
    This extends lexical canonicalisation to grammatical grouping and printing. -/
def Syntax.Canonicalisation (rules : Syntax Tree) (written canonical : RawText) : Prop :=
  ∃ left right tree, Lexed written left ∧ Lexed canonical right ∧
    rules.reads (canonicalTokens left) tree ∧
    canonicalTokens right = (rules.printPieces tree).map PrintedToken.value

theorem Syntax.print_parse (rules : Syntax Tree) (parsed : Parse rules.grammar text tree) :
    rules.Canonicalisation text (rules.print tree) := by
  obtain ⟨left, lex, reads⟩ := rules.parse_iff.mp parsed
  obtain ⟨right, lex', align⟩ := PrintedToken.renderLexed 0 (rules.printPieces tree)
  exact ⟨left, right, tree, lex, lex', reads, align⟩

/-- The composition used by M6 when the concrete elaboration relation is available. -/
def Bezeichnet (grammar : Grammar Tree) (elaborates : Tree → Meaning → Prop)
    (text : RawText) (meaning : Meaning) : Prop :=
  ∃ tree, Parse grammar text tree ∧ elaborates tree meaning

theorem Syntax.bezeichnet_deterministic (rules : Syntax Tree)
    (elabDet : ∀ {tree a b}, elaborates tree a → elaborates tree b → a = b)
    (left : Bezeichnet rules.grammar elaborates text a) (right : Bezeichnet rules.grammar elaborates text b) :
    a = b := by
  obtain ⟨tree, parsed, elaborated⟩ := left
  obtain ⟨tree', parsed', elaborated'⟩ := right
  obtain rfl := rules.parse_deterministic parsed parsed'
  exact elabDet elaborated elaborated'

/-- At every production boundary the consumed prefix and remaining suffix
    lift back to the exact located terminals of the source. -/
theorem locatedSplit {input : List LocatedToken} {taken rest : List Token}
    (aligned : input.map LocatedToken.value = taken ++ rest) :
    ∃ consumed remaining : List LocatedToken,
      input = consumed ++ remaining ∧ consumed.map LocatedToken.value = taken ∧
      remaining.map LocatedToken.value = rest := by
  refine ⟨input.take taken.length, input.drop taken.length, (List.take_append_drop _ _).symm, ?_, ?_⟩
  · rw [List.map_take, aligned, List.take_left]
  · rw [List.map_drop, aligned, List.drop_left]

end Gabbro.Core.Text
