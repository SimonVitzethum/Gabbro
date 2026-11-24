module

public import Core.Text.LexicalClass
import Init.Omega

@[expose] public section

namespace Gabbro.Core.Text

inductive LexicalTag where
  | word | punctuation | integer | hex | binary | decimal | character | string
  | whitespace | line | doc | block

def slashTag (rest : List Char) : LexicalTag :=
  if rest.head? = some '*' then .block
  else if rest.head? = some '/' then
    if (rest.drop 1).head? = some '/' ∧ (rest.drop 2).head? ≠ some '/' then .doc else .line
  else .punctuation

def lexicalTag (raw : RawText) : LexicalTag :=
  match raw with
  | [] => .punctuation
  | c :: rest =>
    haveI : Decidable (isNameStart c) := by
      unfold isNameStart isLetter
      infer_instance
    haveI : Decidable (isSpace c) := by unfold isSpace; infer_instance
    haveI : Decidable (IsDecimalDigit c) := by unfold IsDecimalDigit; infer_instance
    if isNameStart c then .word
    else if isSpace c then .whitespace
    else if IsDecimalDigit c then
      if '.' ∈ rest then .decimal
      else if c = '0' ∧ rest.head? = some 'x' then .hex
      else if c = '0' ∧ rest.head? = some 'b' then .binary
      else .integer
    else if c = '/' then slashTag rest
    else if c = '\'' then .character
    else if c = '"' then .string
    else .punctuation

theorem lexicalTag_digit (digit : IsDecimalDigit c) :
    lexicalTag (c :: rest) =
      (if '.' ∈ rest then .decimal
       else if c = '0' ∧ rest.head? = some 'x' then .hex
       else if c = '0' ∧ rest.head? = some 'b' then .binary
       else .integer) := by
  have notName : ¬ isNameStart c := fun name => nameStart_notDigit name digit
  simp only [lexicalTag, ite_eq_right notName, ite_eq_right (digitNotSpace digit), ite_eq_left digit]

theorem punctuation_spelling {word : String} (member : word ∈ punctuation) :
    lexicalTag word.toList = .punctuation ∧ ' ' ∉ word.toList ∧ word.toList ≠ [] := by
  simp only [punctuation, List.mem_cons, List.not_mem_nil, or_false] at member
  repeat first
    | (subst word; refine ⟨rfl, ?_, List.cons_ne_nil _ _⟩;
       simp only [String.reduceToList, List.mem_cons, List.not_mem_nil, Char.reduceEq, or_self, not_false_eq_true])
    | (rcases member with member | member)
private theorem decimal_not_letter {rest : List Char} (chars : ∀ a ∈ rest, IsDecimalDigit a ∨ a = '_') :
    rest.head? ≠ some 'x' ∧ rest.head? ≠ some 'b' := by
  constructor <;> intro head
  · have member := List.mem_of_head? head
    rcases chars 'x' member with digit | equal
    · exact (by omega : ¬ 120 ≤ 57) digit.2
    · cases equal
  · have member := List.mem_of_head? head
    rcases chars 'b' member with digit | equal
    · exact (by omega : ¬ 98 ≤ 57) digit.2
    · cases equal

theorem Numeral.lexicalTag (number : Numeral 10 raw value width) : lexicalTag raw = .integer := by
  obtain ⟨c, rest, rfl, first⟩ := number.decimalFirst
  have notDot : '.' ∉ rest := fun member => number.notDot (List.mem_cons_of_mem _ member)
  have noLetter := decimal_not_letter (fun a member =>
    number.decimalChars a (List.mem_cons_of_mem _ member))
  rw [lexicalTag_digit first]
  simp only [notDot, noLetter.1, noLetter.2, and_false, ite_false]

theorem lexicalTag_hex (number : Numeral 16 raw value width) :
    lexicalTag ('0' :: 'x' :: raw) = .hex := by
  rw [lexicalTag_digit (c := '0') ⟨by exact Nat.le_refl 48, by change 48 ≤ 57; omega⟩]
  simp only [List.mem_cons, Char.reduceEq, false_or, number.notDot, List.head?_cons, Option.some.injEq,
    and_self, ite_true, ite_false]

theorem lexicalTag_binary (number : Numeral 2 raw value width) :
    lexicalTag ('0' :: 'b' :: raw) = .binary := by
  rw [lexicalTag_digit (c := '0') ⟨by exact Nat.le_refl 48, by change 48 ≤ 57; omega⟩]
  simp only [List.mem_cons, Char.reduceEq, false_or, number.notDot, List.head?_cons, Option.some.injEq,
    and_false, and_self, ite_true, ite_false]

theorem lexicalTag_decimal (number : Numeral 10 left value width) :
    lexicalTag (left ++ ['.'] ++ right ++ exp) = .decimal := by
  obtain ⟨c, rest, rfl, first⟩ := number.decimalFirst
  simp only [List.cons_append]
  rw [lexicalTag_digit first, ite_eq_left]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self))

theorem lexicalTag_space (space : isSpace c) : lexicalTag (c :: rest) = .whitespace := by
  have notName : ¬ isNameStart c := fun name => nameStartNotSpace name space
  simp only [lexicalTag, ite_eq_right notName, ite_eq_left space]

theorem lexicalTag_line (notSlash : rest.head? ≠ some '/') :
    lexicalTag ('/' :: '/' :: rest) = .line := by
  change slashTag ('/' :: rest) = .line
  simp only [slashTag, List.head?_cons, Option.some.injEq, Char.reduceEq, ite_false, ite_true,
    List.drop_succ_cons, List.drop_zero, notSlash, false_and]

theorem lexicalTag_doc (notSlash : rest.head? ≠ some '/') :
    lexicalTag ('/' :: '/' :: '/' :: rest) = .doc := by
  change slashTag ('/' :: '/' :: rest) = .doc
  simp only [slashTag, List.head?_cons, Option.some.injEq, Char.reduceEq, ite_false, ite_true,
    List.drop_succ_cons, List.drop_zero, true_and, ite_eq_left notSlash]

theorem lexicalTag_longLine : lexicalTag ('/' :: '/' :: '/' :: '/' :: rest) = .line := by
  change slashTag ('/' :: '/' :: '/' :: rest) = .line
  simp only [slashTag, List.head?_cons, Option.some.injEq, Char.reduceEq, ite_false, ite_true,
    List.drop_succ_cons, List.drop_zero, true_and, ne_self_iff_false, ite_false]

theorem lexicalTag_block : lexicalTag ('/' :: '*' :: rest) = .block := rfl
theorem lexicalTag_character : lexicalTag ('\'' :: rest) = .character := rfl
theorem lexicalTag_string : lexicalTag ('"' :: rest) = .string := rfl

end Gabbro.Core.Text
