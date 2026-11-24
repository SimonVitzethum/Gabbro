module

public import Core.Text.LexicalTag
import Init.Omega

@[expose] public section

namespace Gabbro.Core.Text

private theorem splitAtMark {mark : Char} (leftFree : mark ∉ left) (rightFree : mark ∉ left')
    (leftStop : right = [] ∨ right.head? = some mark)
    (rightStop : right' = [] ∨ right'.head? = some mark)
    (same : left ++ right = left' ++ right') : left = left' ∧ right = right' := by
  have beforeMark (p s : List Char) (notMark : mark ∉ p)
      (stop : s = [] ∨ s.head? = some mark) : (p ++ s).takeWhile (· != mark) = p := by
    rw [List.takeWhile_append_of_pos (p := (· != mark)) (fun c member =>
      bne_iff_ne.mpr (fun equal => notMark (equal ▸ member)))]
    rcases stop with rfl | first
    · rw [List.takeWhile_nil, List.append_nil]
    · obtain ⟨suffix, rfl⟩ := List.head?_eq_some_iff.mp first
      rw [List.takeWhile_cons_of_neg (by simp only [bne_self_eq_false, Bool.false_eq_true,
        not_false_eq_true]), List.append_nil]
  have samePrefix := (beforeMark left right leftFree leftStop).symm.trans
    ((congrArg (List.takeWhile (· != mark)) same).trans (beforeMark left' right' rightFree rightStop))
  exact ⟨samePrefix, List.append_inj_right same (congrArg List.length samePrefix)⟩

theorem Exponent.unique (x : Exponent raw e) (y : Exponent raw e') : e = e' := by
  cases x with
  | absent => cases y; rfl
  | unsigned digits =>
    obtain ⟨c, rest, equal, digit⟩ := digits.1.decimalFirst
    subst_vars
    cases y with
    | unsigned other => exact congrArg Int.ofNat (digits.1.unique other.1).1
    | positive =>
      exact ((by omega : ¬ 48 ≤ 43) digit.1).elim
    | negative =>
      exact ((by omega : ¬ 48 ≤ 45) digit.1).elim
  | positive digits =>
    cases y with
    | unsigned other =>
      obtain ⟨c, rest, equality, digit⟩ := other.1.decimalFirst
      cases equality
      exact ((by omega : ¬ 48 ≤ 43) digit.1).elim
    | positive other => exact congrArg Int.ofNat (digits.1.unique other.1).1
  | negative digits =>
    cases y with
    | unsigned other =>
      obtain ⟨c, rest, equality, digit⟩ := other.1.decimalFirst
      cases equality
      exact ((by omega : ¬ 48 ≤ 45) digit.1).elim
    | negative other => exact congrArg (fun n => - Int.ofNat n) (digits.1.unique other.1).1

private theorem Exponent.starts (read : Exponent raw e) : raw = [] ∨ raw.head? = some 'e' := by
  cases read
  · exact Or.inl rfl
  all_goals exact Or.inr rfl

private theorem Numeral.notExponent (read : Numeral 10 raw n places) : 'e' ∉ raw := by
  intro member
  rcases read.decimalChars 'e' member with digit | equality
  · exact (by omega : ¬ 101 ≤ 57) digit.2
  · cases equality

theorem decimal_unique (left : Numeral 10 a whole leftWidth) (right : Numeral 10 b fraction places)
    (exponent : Exponent exp power) (left' : Numeral 10 a' whole' leftWidth')
    (right' : Numeral 10 b' fraction' places') (exponent' : Exponent exp' power')
    (same : a ++ ['.'] ++ b ++ exp = a' ++ ['.'] ++ b' ++ exp') :
    (⟨whole, fraction, places, power⟩ : Decimal) = ⟨whole', fraction', places', power'⟩ := by
  simp only [List.append_assoc, List.singleton_append] at same
  obtain ⟨rfl, suffix⟩ := splitAtMark left.notDot left'.notDot (Or.inr rfl) (Or.inr rfl) same
  obtain ⟨rfl, rfl⟩ := splitAtMark right.notExponent right'.notExponent exponent.starts
    exponent'.starts (List.cons.inj suffix).2
  obtain ⟨rfl, _⟩ := left.unique left'
  obtain ⟨rfl, rfl⟩ := right.unique right'
  obtain rfl := exponent.unique exponent'
  rfl

theorem Escape.unique (left : Escape delimiter code c) (right : Escape delimiter code c')
    (newline : delimiter ≠ 'n') (tab : delimiter ≠ 't') (carriage : delimiter ≠ 'r')
    (zero : delimiter ≠ '0') (slash : delimiter ≠ '\\') : c = c' := by
  cases left <;> cases right <;> first | rfl | contradiction

theorem CharacterContent.unique (left : CharacterContent raw c) (right : CharacterContent raw c') :
    c = c' := by
  cases left <;> cases right
  · rfl
  · apply Escape.unique <;> first | assumption | intro h; cases h

theorem StringContent.unique (left : StringContent raw decoded) (right : StringContent raw decoded') :
    decoded = decoded' := by
  induction left generalizing decoded' with
  | nil => cases right; rfl
  | plain _ noSlash _ _ ih =>
    cases right with
    | plain _ _ _ rest => exact congrArg (_ :: ·) (ih rest)
    | escaped => exact (noSlash rfl).elim
  | escaped escape _ ih =>
    cases right with
    | plain _ noSlash => exact (noSlash rfl).elim
    | escaped escape' rest =>
      have same := escape.unique escape' (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
      rw [same, ih rest]

/-- Decoding at a fixed lexical tag. Tagging uses raw spelling alone. -/
def LexicalTag.Decodes : LexicalTag → RawText → PieceKind → Prop
  | .word, raw, kind => kind = .semantic (.word raw)
  | .punctuation, raw, kind => kind = .semantic (.punctuation raw)
  | .integer, raw, kind =>
      ∃ value count, Numeral 10 raw value count ∧ kind = .semantic (.natural value)
  | .hex, raw, kind =>
      ∃ digits value count, raw = '0' :: 'x' :: digits ∧
        Numeral 16 digits value count ∧ kind = .semantic (.natural value)
  | .binary, raw, kind =>
      ∃ digits value count, raw = '0' :: 'b' :: digits ∧
        Numeral 2 digits value count ∧ kind = .semantic (.natural value)
  | .decimal, raw, kind =>
      ∃ left right exp whole leftWidth fraction width power,
        raw = left ++ ['.'] ++ right ++ exp ∧ Numeral 10 left whole leftWidth ∧
        Numeral 10 right fraction width ∧ Exponent exp power ∧
        kind = .semantic (.decimal ⟨whole, fraction, width, power⟩)
  | .character, raw, kind =>
      ∃ inner c, raw = ['\''] ++ inner ++ ['\''] ∧ CharacterContent inner c ∧
        kind = .semantic (.natural c.toNat)
  | .string, raw, kind =>
      ∃ inner decoded, raw = ['"'] ++ inner ++ ['"'] ∧ StringContent inner decoded ∧
        kind = .semantic (.string decoded)
  | .whitespace, _, kind => kind = .trivia .whitespace
  | .line, _, kind => kind = .trivia .lineComment
  | .doc, _, kind => kind = .trivia .docComment
  | .block, _, kind => kind = .trivia .blockComment

theorem Lexeme.decodes (read : Lexeme raw kind) : (lexicalTag raw).Decodes raw kind := by
  cases read with
  | word start _ => simp only [lexicalTag, ite_eq_left start, LexicalTag.Decodes]
  | punctuation member => rw [(punctuation_spelling member).1]; rfl
  | decimalInteger value => rw [value.lexicalTag]; exact ⟨_, _, value, rfl⟩
  | hexInteger value => rw [lexicalTag_hex value]; exact ⟨_, _, _, rfl, value, rfl⟩
  | binaryInteger value => rw [lexicalTag_binary value]; exact ⟨_, _, _, rfl, value, rfl⟩
  | decimal left right exp =>
    rw [lexicalTag_decimal left]
    exact ⟨_, _, _, _, _, _, _, _, rfl, left, right, exp, rfl⟩
  | character content => rw [List.singleton_append, List.cons_append, lexicalTag_character]; exact ⟨_, _, rfl, content, rfl⟩
  | string content => rw [List.singleton_append, List.cons_append, lexicalTag_string]; exact ⟨_, _, rfl, content, rfl⟩
  | whitespace space _ => rw [lexicalTag_space space]; rfl
  | line _ notSlash => rw [lexicalTag_line notSlash]; rfl
  | doc _ notSlash => rw [lexicalTag_doc notSlash]; rfl
  | extendedLine => rw [lexicalTag_longLine]; rfl
  | block => rw [List.cons_append, List.singleton_append, lexicalTag_block]; rfl

theorem LexicalTag.Decodes.unique {tag : LexicalTag} (left : tag.Decodes raw kind) (right : tag.Decodes raw kind') :
    kind = kind' := by
  cases tag with
  | word => exact left.trans right.symm
  | punctuation => exact left.trans right.symm
  | whitespace => exact left.trans right.symm
  | line => exact left.trans right.symm
  | doc => exact left.trans right.symm
  | block => exact left.trans right.symm
  | integer =>
    obtain ⟨_, _, number, rfl⟩ := left
    obtain ⟨_, _, number', rfl⟩ := right
    rw [(number.unique number').1]
  | hex =>
    obtain ⟨_, _, _, rfl, number, rfl⟩ := left
    obtain ⟨_, _, _, same, number', rfl⟩ := right
    obtain rfl := (List.cons.inj (List.cons.inj same).2).2
    rw [(number.unique number').1]
  | binary =>
    obtain ⟨_, _, _, rfl, number, rfl⟩ := left
    obtain ⟨_, _, _, same, number', rfl⟩ := right
    obtain rfl := (List.cons.inj (List.cons.inj same).2).2
    rw [(number.unique number').1]
  | decimal =>
    obtain ⟨_, _, _, _, _, _, _, _, rfl, numeral, fraction, power, rfl⟩ := left
    obtain ⟨_, _, _, _, _, _, _, _, same, numeral', fraction', power', rfl⟩ := right
    rw [decimal_unique numeral fraction power numeral' fraction' power' same]
  | character =>
    obtain ⟨_, _, rfl, content, rfl⟩ := left
    obtain ⟨_, _, same, content', rfl⟩ := right
    obtain rfl := (List.cons.inj (List.append_inj_left' same rfl)).2
    rw [content.unique content']
  | string =>
    obtain ⟨_, _, rfl, content, rfl⟩ := left
    obtain ⟨_, _, same, content', rfl⟩ := right
    obtain rfl := (List.cons.inj (List.append_inj_left' same rfl)).2
    rw [content.unique content']

theorem Lexeme.unique (left : Lexeme raw kind) (right : Lexeme raw kind') : kind = kind' :=
  left.decodes.unique right.decodes

/-- Maximality fixes the split, and a lexeme's spelling fixes its kind and value. -/
theorem LexedAt.deterministic (left : LexedAt start raw pieces)
    (right : LexedAt start raw pieces') : pieces = pieces' := by
  induction left generalizing pieces' with
  | endOfText =>
    generalize same : ([] : RawText) = raw at right
    cases right with
    | endOfText => rfl
    | next nonempty =>
      exact (nonempty (List.append_eq_nil_iff.mp same.symm).1).elim
  | @next spelling kind rest start pieces nonempty lex maximal _ tail ih =>
    generalize same : spelling ++ rest = raw at right
    cases right with
    | endOfText => exact (nonempty (List.append_eq_nil_iff.mp same).1).elim
    | @next spelling' kind' rest' _ pieces' _ lex' maximal' _ tail' =>
      have length := Nat.le_antisymm (maximal' _ _ _ same.symm lex) (maximal _ _ _ same lex')
      obtain ⟨rfl, rfl⟩ := List.append_inj same length
      obtain rfl := lex.unique lex'
      rw [ih tail']

end Gabbro.Core.Text
