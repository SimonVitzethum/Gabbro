module

public import Core.Text.Lexed

@[expose] public section

namespace Gabbro.Core.Text

universe u

/-- A production consumes these terminals and subordinate judgments in order.
    A terminal includes its source span. -/
inductive Symbol (Judgment : Type u) where
  | terminal (token : LocatedToken)
  | nonterminal (judgment : Judgment)

structure Grammar (Judgment : Type u) where
  production : Judgment → List (Symbol Judgment) → Prop
  root : Judgment → Prop

mutual

/-- Declarative grammar derivation. Instances of Judgment carry their own
    attributes and references to the source they describe. -/
inductive Derives {Judgment : Type u} (grammar : Grammar Judgment) :
    Judgment → List LocatedToken → Prop where
  | production :
      grammar.production conclusion symbols →
      DerivesSymbols grammar symbols tokens →
      Derives grammar conclusion tokens

/-- The token stream of a production is exactly the concatenation of the
    terminal spans of its symbols and child productions. -/
inductive DerivesSymbols {Judgment : Type u} (grammar : Grammar Judgment) :
    List (Symbol Judgment) → List LocatedToken → Prop where
  | nil : DerivesSymbols grammar [] []
  | terminal : DerivesSymbols grammar symbols rest →
      DerivesSymbols grammar (.terminal token :: symbols) (token :: rest)
  | nonterminal : Derives grammar judgment consumed → DerivesSymbols grammar symbols rest →
      DerivesSymbols grammar (.nonterminal judgment :: symbols) (consumed ++ rest)

end

theorem DerivesSymbols.noSymbols {grammar : Grammar J} {tokens}
    (derivation : DerivesSymbols grammar [] tokens) : tokens = [] := by
  cases derivation
  rfl

theorem DerivesSymbols.terminalTokens {grammar : Grammar J} {tokens expected}
    (derivation : DerivesSymbols grammar (expected.map Symbol.terminal) tokens) :
    tokens = expected := by
  induction expected generalizing tokens with
  | nil => exact derivation.noSymbols
  | cons token expected ih =>
    cases derivation with
    | terminal children => exact congrArg (token :: ·) (ih children)

/-- Whole-source parsing. There is no suffix accepted outside the derivation
    and no token projection other than the removal of trivia. The AST forms
    will instantiate the judgment type and the production relation. -/
def Parse (grammar : Grammar Judgment) (text : RawText) (tree : Judgment) : Prop :=
  grammar.root tree ∧ ∃ pieces, Lexed text pieces ∧ Derives grammar tree (semanticTokens pieces)

/-- Independent grammatical and typing predicates for elaborable raw text.
    The typing judgment ranges over the attributed surface syntax. -/
def WohlgeformterText (grammar : Grammar Judgment) (typing : Judgment → Prop)
    (text : RawText) : Prop :=
  ∃ tree pieces, grammar.root tree ∧ Lexed text pieces ∧
    Derives grammar tree (semanticTokens pieces) ∧ typing tree

theorem Parse.accounts {grammar : Grammar Judgment} {text tree}
    (parsed : Parse grammar text tree) :
    ∃ pieces, spellings pieces = text ∧
      Derives grammar tree (semanticTokens pieces) ∧
      ∀ p ∈ pieces, p.span.start < p.span.stop ∧ p.span.stop ≤ text.length := by
  obtain ⟨_, pieces, lexical, grammatical⟩ := parsed
  refine ⟨pieces, lexical.exact, grammatical, ?_⟩
  intro part member
  obtain ⟨_, positive, upper⟩ := lexical.spans part member
  exact ⟨positive, by simpa only [Nat.zero_add] using upper⟩

/-- Certification of the grammar interface using a single exact terminal
    production. The spelling premise is separate from the grammar premises. -/
theorem terminalProduction {grammar : Grammar Judgment} {tree tokens text pieces}
    (root : grammar.root tree) (lexical : Lexed text pieces)
    (production : grammar.production tree (tokens.map Symbol.terminal))
    (alignment : semanticTokens pieces = tokens) :
    ∃ tokens', Derives grammar tree tokens' ∧ tokens' = tokens ∧ Parse grammar text tree := by
  have matchTokens : ∀ items : List LocatedToken,
      DerivesSymbols grammar (items.map Symbol.terminal) items := by
    intro items
    induction items with
    | nil => exact .nil
    | cons token rest ih => exact .terminal ih
  have derivation := Derives.production production (matchTokens tokens)
  exact ⟨tokens, derivation, rfl, root, pieces, lexical, alignment ▸ derivation⟩

/-- A single located terminal suffices to realise the grammar and typing
    premises jointly. This is a lemma about the judgment interface. -/
theorem typedTerminal_erfuellbar :
    ∃ (grammar : Grammar LocatedToken) (typing : LocatedToken → Prop) (text : RawText) (token : LocatedToken),
      Parse grammar text token ∧ typing token ∧ WohlgeformterText grammar typing text := by
  obtain ⟨text, token, pieces, lexed, tokens, value, _⟩ := wordToken_erfuellbar
  let grammar : Grammar LocatedToken :=
    ⟨fun location symbols => symbols = [.terminal location], fun location => location.value = .word text⟩
  let typing := fun location : LocatedToken => location.value = .word text
  have rule : grammar.production token ([token].map Symbol.terminal) := rfl
  obtain ⟨_, _, _, parsed⟩ := terminalProduction (grammar := grammar) value lexed rule tokens
  refine ⟨grammar, typing, text, token, parsed, value, ?_⟩
  obtain ⟨root, pieces, lexed, derivation⟩ := parsed
  exact ⟨token, pieces, root, lexed, derivation, value⟩

end Gabbro.Core.Text
