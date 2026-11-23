module

public import Core.Text.Lexeme
public import Init.Data.List.Lemmas
public import Init.Data.List.TakeDrop

@[expose] public section

namespace Gabbro.Core.Text

/-- Longest match among the lexemes at the current position. -/
def Maximal (spelling rest : List Char) : Prop :=
  ∀ other suffix kind, spelling ++ rest = other ++ suffix → Lexeme other kind →
    other.length ≤ spelling.length

/-- A block opener cannot fall back to punctuation. A number cannot leave an
    attached word fragment. A decimal point must introduce a fraction or a range. -/
def Boundary (spelling rest : List Char) (kind : PieceKind) : Prop :=
  (∀ suffix, spelling ++ rest = '/' :: '*' :: suffix → kind = .trivia .blockComment) ∧
  (∀ n c tail, kind = .semantic (.natural n) → rest = c :: tail →
    (∀ ds, spelling ≠ '\'' :: ds) → ¬ isNamePart c) ∧
  (∀ n tail, kind = .semantic (.natural n) → rest = '.' :: tail →
    (∀ c ∈ spelling, ('0' ≤ c ∧ c ≤ '9') ∨ c = '_') → tail.head? = some '.')

/-- The source is partitioned from left to right, with no elided characters.
    The only empty stream is the one at the end of the source. -/
inductive LexedAt : Nat → RawText → List Piece → Prop where
  | endOfText (start : Nat) : LexedAt start [] []
  | next : spelling ≠ [] → Lexeme spelling kind → Maximal spelling rest →
      Boundary spelling rest kind →
      LexedAt (start + spelling.length) rest pieces →
      LexedAt start (spelling ++ rest) (⟨start, spelling, kind⟩ :: pieces)

def Lexed (text : RawText) (pieces : List Piece) : Prop := LexedAt 0 text pieces

theorem LexedAt.exact {start text pieces} (read : LexedAt start text pieces) :
    spellings pieces = text := by
  induction read with
  | endOfText start => rfl
  | next nonempty lexical maximal boundary read ih => simp only [spellings, ih]

theorem LexedAt.spans {start text pieces} (read : LexedAt start text pieces) :
    ∀ p ∈ pieces, start ≤ p.span.start ∧ p.span.start < p.span.stop ∧
      p.span.stop ≤ start + text.length := by
  induction read with
  | endOfText start =>
    intro p member
    exact (List.not_mem_nil member).elim
  | @next spelling kind rest start pieces nonempty lexical maximal boundary read ih =>
    intro p member
    rcases List.mem_cons.mp member with rfl | member
    · have positive := List.length_pos_iff.mpr nonempty
      exact ⟨Nat.le_refl _, Nat.lt_add_of_pos_right positive,
        by simp only [Piece.span, List.length_append, ← Nat.add_assoc]; exact Nat.le_add_right _ _⟩
    · obtain ⟨lower, positive, upper⟩ := ih p member
      exact ⟨Nat.le_trans (Nat.le_add_right _ _) lower, positive,
        by simpa only [List.length_append, ← Nat.add_assoc] using upper⟩

theorem LexedAt.endOnly {start text} (read : LexedAt start text []) : text = [] := by
  cases read
  rfl

theorem LexedAt.splitAtPiece {start text pieces} (read : LexedAt start text pieces) :
    ∀ p ∈ pieces, ∃ prior after, text = prior ++ p.spelling ++ after ∧
      p.span.start = start + prior.length := by
  induction read with
  | endOfText start =>
    intro p member
    exact (List.not_mem_nil member).elim
  | @next spelling kind rest start pieces nonempty lexical maximal boundary read ih =>
    intro p member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨[], rest, rfl, (Nat.add_zero start).symm⟩
    · obtain ⟨prior, after, split, offset⟩ := ih p member
      refine ⟨spelling ++ prior, after, ?_, ?_⟩
      · simp only [split, List.append_assoc]
      · simpa only [List.length_append, Nat.add_assoc] using offset

/-- Each span selects its exact spelling in the raw source. -/
theorem Lexed.spanSpelling {text pieces} (read : Lexed text pieces) {p} (member : p ∈ pieces) :
    ((text.drop p.span.start).take (p.span.stop - p.span.start)) = p.spelling := by
  obtain ⟨prior, after, split, offset⟩ := LexedAt.splitAtPiece read p member
  have start : p.span.start = prior.length := by simpa only [Nat.zero_add] using offset
  have width : p.span.stop - p.span.start = p.spelling.length :=
    Nat.add_sub_cancel_left p.start p.spelling.length
  rw [split, List.append_assoc, width, start, List.drop_left, List.take_left]

theorem singletonMaximal (c : Char) : Maximal [c] [] := by
  intro other suffix kind split lexical
  have length := congrArg List.length split
  simp only [List.append_nil, List.length_cons, List.length_nil, List.length_append] at length
  exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_eq length.symm)

theorem singletonBoundary (c : Char) (kind : PieceKind) : Boundary [c] [] kind := by
  refine ⟨?_, ?_, ?_⟩
  · intro suffix equality
    cases equality
  · intro n next tail _ equality
    cases equality
  · intro n tail _ equality
    cases equality

/-- The constraints on a lexical step hold jointly, at any source offset. -/
theorem lexicalStep_erfuellbar (start : Nat) :
    ∃ text pieces, text ≠ [] ∧ semanticTokens pieces = [] ∧ LexedAt start text pieces := by
  refine ⟨[' '], [⟨start, [' '], .trivia .whitespace⟩], List.cons_ne_nil _ _, rfl, ?_⟩
  have lexical : Lexeme [' '] (.trivia .whitespace) :=
    .whitespace List.mem_cons_self (fun _ member => (List.not_mem_nil member).elim)
  exact LexedAt.next (rest := []) (List.cons_ne_nil _ _) lexical
    (singletonMaximal ' ') (singletonBoundary ' ' _) (.endOfText _)

/-- A nonempty semantic stream satisfies the lexical premises with an exact span. -/
theorem wordToken_erfuellbar :
    ∃ text token pieces, Lexed text pieces ∧ semanticTokens pieces = [token] ∧
      token.value = .word text ∧ token.span = ⟨0, 1⟩ := by
  have initial : isNameStart 'a' :=
    Or.inl (Or.inl ⟨by decide, by decide⟩)
  have lexical : Lexeme ['a'] (.semantic (.word ['a'])) :=
    .word initial (fun _ member => (List.not_mem_nil member).elim)
  refine ⟨['a'], ⟨⟨0, 1⟩, .word ['a']⟩, [⟨0, ['a'], .semantic (.word ['a'])⟩], ?_, rfl, rfl, rfl⟩
  exact LexedAt.next (rest := []) (List.cons_ne_nil _ _) lexical
    (singletonMaximal 'a') (singletonBoundary 'a' _) (.endOfText _)

end Gabbro.Core.Text
