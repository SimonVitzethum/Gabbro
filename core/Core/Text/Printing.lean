module

public import Core.Text.LexicalValue
public import Core.Text.Canonical
import Init.Omega

@[expose] public section

namespace Gabbro.Core.Text

/-- A head for which a following space separates the two lexical pieces. -/
structure UnquotedStart (c : Char) : Prop where
  nonspace : ¬ isSpace c
  nonslash : c ≠ '/'
  nonchar : c ≠ '\''
  nonstring : c ≠ '"'

theorem UnquotedStart.ofCodepoint (high : 48 ≤ c.toNat) (space : ¬ isSpace c) : UnquotedStart c :=
  ⟨space, fun same => by subst c; exact (by omega : ¬ 48 ≤ 47) high,
    fun same => by subst c; exact (by omega : ¬ 48 ≤ 39) high,
    fun same => by subst c; exact (by omega : ¬ 48 ≤ 34) high⟩

theorem nameStart_unquoted (name : isNameStart c) : UnquotedStart c := by
  apply UnquotedStart.ofCodepoint _ (nameStartNotSpace name)
  rcases name with (⟨low, _⟩ | ⟨low, _⟩ | german) | rfl
  · have bound : 97 ≤ c.toNat := low
    omega
  · have bound : 65 ≤ c.toNat := low
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at german
    rcases german with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (simp only [Char.reduceToNat]; omega)
  · change 48 ≤ 95
    omega

theorem Lexeme.nonempty (lex : Lexeme raw kind) : raw ≠ [] := by
  cases lex
  case punctuation member => exact (punctuation_spelling member).2.2
  case decimalInteger read =>
    obtain ⟨_, _, rfl, _⟩ := read.decimalFirst
    exact List.cons_ne_nil _ _
  case decimal read _ _ =>
    obtain ⟨_, _, rfl, _⟩ := read.decimalFirst
    exact List.cons_ne_nil _ _
  all_goals exact List.cons_ne_nil _ _

private theorem Lexeme.noSpaceAfterUnquoted (lex : Lexeme raw kind)
    (head : raw.head? = some c) (normal : UnquotedStart c) : ' ' ∉ raw := by
  cases lex with
  | word start rest =>
    rintro member
    rcases List.mem_cons.mp member with same | member
    · exact (nameStartNotSpace (same ▸ start)) List.mem_cons_self
    · exact namePartNotSpace (rest _ member) List.mem_cons_self
  | punctuation member => exact (punctuation_spelling member).2.1
  | decimalInteger read => exact read.notSpace
  | hexInteger read => simpa only [List.mem_cons, Char.reduceEq, false_or] using read.notSpace
  | binaryInteger read => simpa only [List.mem_cons, Char.reduceEq, false_or] using read.notSpace
  | decimal left right exp =>
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, Char.reduceEq,
      or_self, left.notSpace, right.notSpace, exp.notSpace, not_false_eq_true]
  | character =>
    exact (normal.nonchar (Option.some.inj head).symm).elim
  | string =>
    exact (normal.nonstring (Option.some.inj head).symm).elim
  | whitespace space =>
    exact (normal.nonspace ((Option.some.inj head) ▸ space)).elim
  | line => exact (normal.nonslash (Option.some.inj head).symm).elim
  | doc => exact (normal.nonslash (Option.some.inj head).symm).elim
  | extendedLine => exact (normal.nonslash (Option.some.inj head).symm).elim
  | block => exact (normal.nonslash (Option.some.inj head).symm).elim

private theorem whitespaceChars (read : Lexeme raw (.trivia .whitespace)) :
    ∀ c ∈ raw, isSpace c := by
  cases read with
  | whitespace first rest =>
    intro c member
    rcases List.mem_cons.mp member with rfl | member
    · exact first
    · exact rest c member

private theorem spaceMaximal (headNotSpace : ∀ c, rest.head? = some c → ¬ isSpace c) :
    Maximal [' '] rest := by
  intro other suffix kind same lex
  cases other with
  | nil => exact Nat.zero_le _
  | cons first tail =>
    have equal : ' ' = first := (List.cons.inj same).1
    subst first
    have decodes := lex.decodes
    rw [lexicalTag_space (c := ' ') List.mem_cons_self] at decodes
    change kind = .trivia .whitespace at decodes
    have whitespace : Lexeme (' ' :: tail) (.trivia .whitespace) := decodes ▸ lex
    cases tail with
    | nil => exact Nat.le_refl _
    | cons next more =>
      have head : rest.head? = some next := congrArg List.head? (List.cons.inj same).2
      exact (headNotSpace next head (whitespaceChars whitespace next
        (List.mem_cons_of_mem _ List.mem_cons_self))).elim

private theorem spaceBoundary : Boundary [' '] rest (.trivia .whitespace) := by
  refine ⟨?_, ?_, ?_⟩
  · intro suffix bad
    cases bad
  · intro n c tail bad
    cases bad
  · intro n tail bad
    cases bad

/-- Local certificate for one canonical spelling in a whitespace-separated stream. -/
structure PrintedToken where
  value : Token
  spelling : RawText
  reads : Lexeme spelling (.semantic value)
  headNotSpace : ∀ c, spelling.head? = some c → ¬ isSpace c
  separated : ∀ rest, Maximal spelling (' ' :: rest) ∧ Boundary spelling (' ' :: rest) (.semantic value)

def PrintedToken.unquoted {value : Token} (spelling : RawText) (lex : Lexeme spelling (.semantic value))
    (normal : ∀ c, spelling.head? = some c → UnquotedStart c) : PrintedToken where
  value := value
  spelling := spelling
  reads := lex
  headNotSpace := fun c same => (normal c same).nonspace
  separated := by
    intro tail
    cases spelling with
    | nil => exact (lex.nonempty rfl).elim
    | cons c rest =>
      have head := normal c rfl
      refine ⟨?_, ?_⟩
      · intro other suffix kind same otherLex
        apply Nat.le_of_not_gt
        intro longer
        have otherHead : other.head? = some c := by
          cases other with
          | nil => exact (Nat.not_lt_zero _ longer).elim
          | cons first remaining => exact congrArg some (List.cons.inj same).1.symm
        apply otherLex.noSpaceAfterUnquoted otherHead head
        apply List.mem_of_getElem? (i := (c :: rest).length)
        have get := congrArg (fun raw : RawText => raw[(c :: rest).length]?) same
        simpa only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero,
          List.getElem?_append_left longer] using get.symm
      · refine ⟨?_, ?_, ?_⟩
        · intro suffix bad
          exact (head.nonslash (List.cons.inj bad).1).elim
        · intro _ ch _ _ same _
          have equal : ' ' = ch := (List.cons.inj same).1
          exact equal ▸ (fun part => namePartNotSpace part List.mem_cons_self)
        · intro _ _ _ bad
          cases bad

private theorem Lexeme.punctuationMember (lex : Lexeme raw kind)
    (tag : lexicalTag raw = .punctuation) : ∃ word : String, word ∈ Text.punctuation ∧ raw = word.toList := by
  cases lex with
  | word start _ =>
    simp only [lexicalTag, ite_eq_left start] at tag
    cases tag
  | punctuation member => exact ⟨_, member, rfl⟩
  | decimalInteger read => rw [read.lexicalTag] at tag; cases tag
  | hexInteger read => rw [lexicalTag_hex read] at tag; cases tag
  | binaryInteger read => rw [lexicalTag_binary read] at tag; cases tag
  | decimal left _ _ => rw [lexicalTag_decimal left] at tag; cases tag
  | character => rw [List.singleton_append, List.cons_append, lexicalTag_character] at tag; cases tag
  | string => rw [List.singleton_append, List.cons_append, lexicalTag_string] at tag; cases tag
  | whitespace space _ => rw [lexicalTag_space space] at tag; cases tag
  | line _ notSlash => rw [lexicalTag_line notSlash] at tag; cases tag
  | doc _ notSlash => rw [lexicalTag_doc notSlash] at tag; cases tag
  | extendedLine => rw [lexicalTag_longLine] at tag; cases tag
  | block => rw [List.cons_append, List.singleton_append, lexicalTag_block] at tag; cases tag

private theorem slashSpaceMaximal (rest : RawText) : Maximal ['/'] (' ' :: rest) := by
  intro other suffix kind same lex
  cases other with
  | nil => exact Nat.zero_le _
  | cons first tail =>
    obtain rfl := (List.cons.inj same).1
    cases tail with
    | nil => exact Nat.le_refl _
    | cons second tail =>
      obtain rfl := (List.cons.inj (List.cons.inj same).2).1
      obtain ⟨word, member, spelling⟩ := lex.punctuationMember rfl
      exact ((punctuation_spelling member).2.1
        (spelling ▸ List.mem_cons_of_mem _ List.mem_cons_self)).elim

/-- Division prints as a single slash. The following space excludes both comment openers. -/
def PrintedToken.slash : PrintedToken where
  value := .punctuation ['/']
  spelling := ['/']
  reads := Lexeme.punctuation (word := "/") (by
    simp only [punctuation, List.mem_cons, String.reduceEq, false_or, true_or])
  headNotSpace := by
    intro c head
    obtain rfl := Option.some.inj head
    simp only [isSpace, List.mem_cons, List.not_mem_nil, Char.reduceEq, or_self, not_false_eq_true]
  separated := by
    intro rest
    refine ⟨slashSpaceMaximal rest, ?_, ?_, ?_⟩
    · intro suffix bad
      cases bad
    · intro n c tail bad
      cases bad
    · intro n tail bad
      cases bad

/-- An immediately adjacent slash starts a comment, even before a body is read. -/
theorem slash_notMaximalAtLine (rest : RawText) : ¬ Maximal ['/'] ('/' :: rest) := by
  intro maximal
  have line : Lexeme ['/', '/'] (.trivia .lineComment) :=
    .line List.not_mem_nil (by intro bad; cases bad)
  have longer := maximal _ rest _ rfl line
  exact (by decide : ¬ 2 ≤ 1) longer

/-- A block opener cannot be read as division, including when its comment fails to close. -/
theorem slash_notBoundaryAtBlock (rest : RawText) :
    ¬ Boundary ['/'] ('*' :: rest) (.semantic PrintedToken.slash.value) := by
  intro boundary
  cases boundary.1 rest rfl

/-- Put one space after each token, including the last. This fixes a spelling
    without requiring token-pair proofs at grammar productions. -/
def PrintedToken.render : List PrintedToken → RawText
  | [] => []
  | token :: rest => token.spelling ++ ' ' :: render rest

private theorem PrintedToken.renderHead {tokens : List PrintedToken}
    (first : (render tokens).head? = some c) : ¬ isSpace c := by
  cases tokens with
  | nil => cases first
  | cons token rest =>
    have present : token.spelling.head? ≠ none := by
      intro empty
      have eq := List.head?_eq_none_iff.mp empty
      exact token.reads.nonempty eq
    cases head : token.spelling.head? with
    | none => exact (present head).elim
    | some a =>
      have same : a = c := by
        simpa only [render, List.head?_append, head, Option.some_or, Option.some.injEq] using first
      exact same ▸ token.headNotSpace a head

theorem PrintedToken.renderLexed (start : Nat) (tokens : List PrintedToken) :
    ∃ pieces, LexedAt start (render tokens) pieces ∧ canonicalTokens pieces = tokens.map (·.value) := by
  induction tokens generalizing start with
  | nil => exact ⟨[], .endOfText start, rfl⟩
  | cons token rest ih =>
    obtain ⟨pieces, lex, align⟩ := ih (start + token.spelling.length + [' '].length)
    have space : Lexeme [' '] (.trivia .whitespace) :=
      .whitespace List.mem_cons_self (fun _ member => (List.not_mem_nil member).elim)
    have nextSpace := LexedAt.next (List.cons_ne_nil _ _) space
      (spaceMaximal (fun _ first => renderHead first)) spaceBoundary lex
    have step := LexedAt.next token.reads.nonempty token.reads
      (token.separated _).1 (token.separated _).2 nextSpace
    refine ⟨_, step, ?_⟩
    exact congrArg (token.value :: ·) align

end Gabbro.Core.Text
