module

public import Core.Text.Numeral
public import Core.Text.Lexed
import Init.Omega

@[expose] public section

namespace Gabbro.Core.Text

theorem charLE {a b : Char} : a ≤ b ↔ a.toNat ≤ b.toNat := Iff.rfl

theorem nameStart_notDigit (start : isNameStart c) : ¬ IsDecimalDigit c := by
  rintro ⟨low, high⟩
  have upper : c.toNat ≤ 57 := high
  have lower : 48 ≤ c.toNat := low
  rcases start with (⟨l, _⟩ | ⟨l, _⟩ | inList) | rfl
  · have bound : 97 ≤ c.toNat := l
    omega
  · have bound : 65 ≤ c.toNat := l
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at inList
    rcases inList with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp only [Char.reduceToNat] at *; omega)
  · simp only [Char.reduceToNat] at upper; omega

theorem digitNotSpace (digit : IsDecimalDigit c) : ¬ isSpace c := by
  intro blank
  have lower : 48 ≤ c.toNat := digit.1
  simp only [isSpace, List.mem_cons, List.not_mem_nil, or_false] at blank
  rcases blank with rfl | rfl | rfl | rfl <;> (simp only [Char.reduceToNat] at *; omega)

theorem nameStartNotSpace (start : isNameStart c) : ¬ isSpace c := by
  intro blank
  simp only [isSpace, List.mem_cons, List.not_mem_nil, or_false] at blank
  rcases start with (⟨l, _⟩ | ⟨l, _⟩ | inList) | rfl
  · have bound : 97 ≤ c.toNat := l
    rcases blank with rfl | rfl | rfl | rfl <;> (simp only [Char.reduceToNat] at *; omega)
  · have bound : 65 ≤ c.toNat := l
    rcases blank with rfl | rfl | rfl | rfl <;> (simp only [Char.reduceToNat] at *; omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at inList
    rcases blank with rfl | rfl | rfl | rfl <;> simp only [Char.reduceEq, or_self] at inList
  · simp only [Char.reduceEq, or_self] at blank

theorem namePartNotSpace (part : isNamePart c) : ¬ isSpace c := by
  rcases part with name | digit
  · exact nameStartNotSpace name
  · exact digitNotSpace digit

theorem digitValue_namePart (read : digitValue c value) : isNamePart c := by
  rcases read with ⟨lo, hi, _⟩ | ⟨lo, hi, _⟩ | ⟨lo, hi, _⟩
  · exact Or.inr ⟨lo, hi⟩
  · have upper : c.toNat ≤ 102 := hi
    exact Or.inl (Or.inl (Or.inl ⟨lo, by change c.toNat ≤ 122; omega⟩))
  · have upper : c.toNat ≤ 70 := hi
    exact Or.inl (Or.inl (Or.inr (Or.inl ⟨lo, by change c.toNat ≤ 90; omega⟩)))

theorem Digits.nameChars (digits : Digits base spelling value count) :
    ∀ c ∈ spelling, isNamePart c := by
  induction digits with
  | nil => intro c h; nomatch h
  | digit read _ _ ih =>
    intro c member
    rcases List.mem_cons.mp member with rfl | member
    · exact digitValue_namePart read
    · exact ih c member
  | separator _ ih =>
    intro c member
    rcases List.mem_cons.mp member with rfl | member
    · exact Or.inl (Or.inr rfl)
    · exact ih c member

theorem Numeral.nameChars (read : Numeral base spelling value count) :
    ∀ c ∈ spelling, isNamePart c :=
  read.choose_spec.choose_spec.choose_spec.2.2.2.nameChars

theorem Numeral.notDot (read : Numeral base spelling value count) : '.' ∉ spelling := by
  intro member
  rcases read.nameChars '.' member with ((⟨lo, _⟩ | ⟨lo, _⟩ | german) | under) | ⟨lo, _⟩
  · exact (by omega : ¬ 97 ≤ 46) lo
  · exact (by omega : ¬ 65 ≤ 46) lo
  · simp only [List.mem_cons, List.not_mem_nil, Char.reduceEq, or_self] at german
  · cases under
  · exact (by omega : ¬ 48 ≤ 46) lo

theorem Numeral.notSpace (read : Numeral base spelling value count) : ' ' ∉ spelling :=
  fun member => namePartNotSpace (read.nameChars ' ' member) List.mem_cons_self

theorem Exponent.notSpace (read : Exponent spelling value) : ' ' ∉ spelling := by
  cases read with
  | absent => exact List.not_mem_nil
  | unsigned digits =>
    simpa only [List.mem_cons, Char.reduceEq, false_or] using digits.1.notSpace
  | positive digits =>
    simpa only [List.mem_cons, Char.reduceEq, false_or] using digits.1.notSpace
  | negative digits =>
    simpa only [List.mem_cons, Char.reduceEq, false_or] using digits.1.notSpace

theorem Exponent.notDot (read : Exponent spelling value) : '.' ∉ spelling := by
  cases read with
  | absent => exact List.not_mem_nil
  | unsigned digits =>
    simpa only [List.mem_cons, Char.reduceEq, false_or] using digits.1.notDot
  | positive digits =>
    simpa only [List.mem_cons, Char.reduceEq, false_or] using digits.1.notDot
  | negative digits =>
    simpa only [List.mem_cons, Char.reduceEq, false_or] using digits.1.notDot

end Gabbro.Core.Text
