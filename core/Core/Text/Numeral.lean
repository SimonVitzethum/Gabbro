module

public import Core.Text.Lexeme
import Init.Data.Nat.ToString
import Init.Data.Char.Lemmas
import Init.Omega

@[expose] public section

namespace Gabbro.Core.Text

def IsDecimalDigit (c : Char) : Prop := '0' ≤ c ∧ c ≤ '9'

theorem digitValue_unique (left : digitValue c a) (right : digitValue c b) : a = b := by
  unfold digitValue at left right
  have charLE {x y : Char} : x ≤ y ↔ x.toNat ≤ y.toNat := Iff.rfl
  rcases left with ⟨la, ha, rfl⟩ | ⟨la, ha, rfl⟩ | ⟨la, ha, rfl⟩ <;>
    rcases right with ⟨lb, hb, rfl⟩ | ⟨lb, hb, rfl⟩ | ⟨lb, hb, rfl⟩ <;>
    first | rfl | (simp only [charLE, Char.reduceToNat] at la lb ha hb; omega)

theorem digitValue_notUnderscore (read : digitValue c value) : c ≠ '_' := by
  rintro rfl
  rcases read with ⟨lo, hi, _⟩ | ⟨lo, hi, _⟩ | ⟨lo, hi, _⟩ <;>
    first | exact (by omega : ¬ 97 ≤ 95) lo | exact (by omega : ¬ 95 ≤ 57) hi |
      exact (by omega : ¬ 95 ≤ 70) hi

theorem Digits.unique (left : Digits base spelling value count) (right : Digits base spelling value' count') :
    value = value' ∧ count = count' := by
  induction left generalizing value' count' with
  | nil => cases right; exact ⟨rfl, rfl⟩
  | digit digit bound tail ih =>
    cases right with
    | digit digit' _ tail' =>
      obtain ⟨rfl, rfl⟩ := ih tail'
      obtain rfl := digitValue_unique digit digit'
      exact ⟨rfl, rfl⟩
    | separator => exact (digitValue_notUnderscore digit rfl).elim
  | separator tail ih =>
    cases right with
    | digit digit _ _ => exact (digitValue_notUnderscore digit rfl).elim
    | separator tail' => exact ih tail'

theorem Numeral.unique (left : Numeral base spelling value count)
    (right : Numeral base spelling value' count') : value = value' ∧ count = count' :=
  left.choose_spec.choose_spec.choose_spec.2.2.2.unique
    right.choose_spec.choose_spec.choose_spec.2.2.2

theorem digitValue_decimal (read : digitValue c value) (bound : value < 10) : IsDecimalDigit c := by
  rcases read with ⟨lo, hi, _⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
  · exact ⟨lo, hi⟩
  · omega
  · omega

theorem Digits.decimalChars (digits : Digits 10 spelling value count) :
    ∀ c ∈ spelling, IsDecimalDigit c ∨ c = '_' := by
  induction digits with
  | nil => intro c h; nomatch h
  | digit read bound _ ih =>
    intro c member
    rcases List.mem_cons.mp member with rfl | member
    · exact Or.inl (digitValue_decimal read bound)
    · exact ih c member
  | separator _ ih =>
    intro c member
    rcases List.mem_cons.mp member with rfl | member
    · exact Or.inr rfl
    · exact ih c member

theorem Numeral.decimalFirst (read : Numeral 10 spelling value count) :
    ∃ c rest, spelling = c :: rest ∧ IsDecimalDigit c := by
  obtain ⟨c, rest, d, rfl, digit, bound, _⟩ := read
  exact ⟨c, rest, rfl, digitValue_decimal digit bound⟩

theorem Numeral.decimalChars (read : Numeral 10 spelling value count) :
    ∀ c ∈ spelling, IsDecimalDigit c ∨ c = '_' :=
  read.choose_spec.choose_spec.choose_spec.2.2.2.decimalChars

private theorem digitsOfDecimalChars (all : ∀ c ∈ spelling, c.isDigit) :
    Digits 10 spelling (Nat.ofDigitChars 10 spelling 0) spelling.length := by
  induction spelling with
  | nil => rw [Nat.ofDigitChars_nil]; exact .nil
  | cons c rest ih =>
    have digit := all c List.mem_cons_self
    have bounds : IsDecimalDigit c := by
      simpa only [IsDecimalDigit, Char.le_def, Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] using digit
    have bound : c.toNat - '0'.toNat < 10 := by
      have lo : 48 ≤ c.toNat := bounds.1
      have hi : c.toNat ≤ 57 := bounds.2
      change c.toNat - 48 < 10
      omega
    have read : digitValue c (c.toNat - '0'.toNat) := Or.inl ⟨bounds.1, bounds.2, rfl⟩
    have tail := ih (fun d member => all d (List.mem_cons_of_mem _ member))
    have calculate : Nat.ofDigitChars 10 (c :: rest) 0 =
        (c.toNat - '0'.toNat) * 10 ^ rest.length + Nat.ofDigitChars 10 rest 0 := by
      rw [Nat.ofDigitChars_cons, Nat.mul_zero, Nat.zero_add, Nat.ofDigitChars_eq_ofDigitChars_zero, Nat.mul_comm]
    exact calculate.symm ▸ Digits.digit read bound tail

theorem Numeral.print (value : Nat) :
    Numeral 10 (Nat.toDigits 10 value) value (Nat.toDigits 10 value).length := by
  generalize h : Nat.toDigits 10 value = spelling
  have nonempty := Nat.toDigits_ne_nil (n := value) (b := 10)
  have all : ∀ c ∈ spelling, c.isDigit := by
    simpa only [← h] using
      (fun c member => Nat.isDigit_of_mem_toDigits (n := value) (b := 10)
        (Nat.zero_lt_succ _) (Nat.le_refl _) (c := c) member)
  have calculate : Nat.ofDigitChars 10 spelling 0 = value :=
    h ▸ Nat.ofDigitChars_ten_toDigits
  cases spelling with
  | nil => exact ((h ▸ nonempty) rfl).elim
  | cons c rest =>
    have bounds : IsDecimalDigit c := by
      simpa only [IsDecimalDigit, Char.le_def, Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] using (all c List.mem_cons_self)
    have bound : c.toNat - '0'.toNat < 10 := by
      have lo : 48 ≤ c.toNat := bounds.1
      have hi : c.toNat ≤ 57 := bounds.2
      change c.toNat - 48 < 10
      omega
    exact ⟨c, rest, _, rfl, Or.inl ⟨bounds.1, bounds.2, rfl⟩, bound,
      calculate ▸ digitsOfDecimalChars all⟩

end Gabbro.Core.Text
