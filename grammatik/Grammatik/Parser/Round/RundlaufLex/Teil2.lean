module

public import Grammatik.Parser.Lex.Lexer
import all Init.Data.Repr
import all Init.Data.String.Defs
public import Grammatik.Parser.Round.RundlaufLex.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000

theorem scan_zeichen (b : Bool) (s : String) (rest : List Char) (m : Nat)
    (h : s.toList ∈ markTafel) :
    scan b (s.toList ++ ' ' :: rest) (m + 2) =
      Except.map (Token.zeichen s :: ·) (scan b rest m) := by
  have hk : markKopfGut s.toList = true := List.all_eq_true.mp markTafel_koepfe _ h
  have hn := nimmZeichen_mark s.toList rest h
  rw [String.ofList_toList] at hn
  generalize s.toList = l at h hk hn
  match l, hk with
  | c :: cs, hk =>
    simp only [markKopfGut, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq,
      Bool.or_eq_true, List.isEmpty_iff] at hk
    obtain ⟨⟨⟨⟨hl, hz⟩, ha⟩, hq⟩, hs⟩ := hk
    rw [List.cons_append, scan.eq_7]
    · simp only [hl, hz, ha, Bool.false_eq_true, ite_false]
      rw [← List.cons_append, hn]
      simp only [scan_leer]
    · intro r e e2
      rcases hs with hs | hs
      · exact hs e
      · subst hs; simp only [↓Char.isValue, List.nil_append, List.cons.injEq, Char.reduceEq, false_and] at e2
    · intro r e e2
      rcases hs with hs | hs
      · exact hs e
      · subst hs; simp only [↓Char.isValue, List.nil_append, List.cons.injEq, Char.reduceEq, false_and] at e2
    · intro r e e2
      rcases hs with hs | hs
      · exact hs e
      · subst hs; simp only [↓Char.isValue, List.nil_append, List.cons.injEq, Char.reduceEq, false_and] at e2
    · intro r e e2
      rcases hs with hs | hs
      · exact hs e
      · subst hs; simp only [↓Char.isValue, List.nil_append, List.cons.injEq, Char.reduceEq, false_and] at e2
    · exact hq

/-! ### The list -/

theorem scan_token (b : Bool) (t : Token) (rest : List Char) (m : Nat) (h : TokGut t) :
    scan b (spell t ++ ' ' :: rest) (m + 2) = Except.map (t :: ·) (scan b rest m) := by
  cases t with
  | ident s =>
    simp only [TokGut] at h
    simp only [spell, scan_name b s rest m h.1, h.2]
    rfl
  | wort s =>
    simp only [TokGut] at h
    simp only [spell, scan_name b s rest m h.1, h.2]
    rfl
  | num n => exact scan_zahl b n rest m
  | float s => exact scan_gleit b s rest m h
  | text s => exact scan_text b s rest m h
  | zeichen s => exact scan_zeichen b s rest m h
  | doku _ => exact absurd h id
  | ende => exact absurd h id

theorem scan_render : ∀ (ts : List Token) (n : Nat), (∀ t ∈ ts, TokGut t) →
    2 * ts.length ≤ n → scan false (render ts) n = .ok (ts ++ [.ende]) := by
  intro ts
  induction ts with
  | nil => intro n _ _; simp only [render, scan, List.nil_append]
  | cons t ts ih =>
    intro n h hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by simp only [List.length_cons] at hn; omega⟩
    simp only [render]
    rw [scan_token false t _ m (h t (by simp only [List.mem_cons, true_or])),
      ih m (fun x hx => h x (by simp only [List.mem_cons, hx, or_true])) (by simp only [List.length_cons] at hn; omega)]
    rfl

theorem spell_ne_nil (t : Token) (h : TokGut t) : spell t ≠ [] := by
  cases t with
  | ident s =>
    simp only [TokGut, nameForm] at h
    simp only [spell]
    intro e; rw [e] at h; simp only [Bool.false_eq_true, false_and] at h
  | wort s =>
    simp only [TokGut, nameForm] at h
    simp only [spell]
    intro e; rw [e] at h; simp only [Bool.false_eq_true, false_and] at h
  | num n => exact Nat.toDigits_ne_nil
  | float s =>
    obtain ⟨v, frac, ex, rfl, _⟩ := h
    simp only [spell, Nat.toString_eq_repr, String.toList_append, Nat.toList_repr, String.reduceToList,
  ↓Char.isValue, String.toList_ofList, List.append_assoc, List.cons_append, List.nil_append, ne_eq,
  List.append_eq_nil_iff, Nat.toDigits_ne_nil, reduceCtorEq, and_self, not_false_eq_true]
  | text s => simp only [spell, ↓Char.isValue, ne_eq, reduceCtorEq, not_false_eq_true]
  | zeichen s =>
    simp only [TokGut] at h
    simp only [spell]
    intro e; rw [e] at h; simp only [markTafel, ↓Char.isValue, List.mem_cons, List.nil_eq, reduceCtorEq, List.ne_cons_self,
  List.not_mem_nil, or_self] at h
  | doku _ => exact absurd h id
  | ende => exact absurd h id

theorem render_laenge : ∀ (ts : List Token), (∀ t ∈ ts, TokGut t) →
    2 * ts.length ≤ (render ts).length := by
  intro ts
  induction ts with
  | nil => simp only [List.not_mem_nil, false_implies, implies_true, List.length_nil, Nat.mul_zero, render, Std.le_refl,
  imp_self]
  | cons t ts ih =>
    intro h
    have h1 := spell_ne_nil t (h t (by simp only [List.mem_cons, true_or]))
    have h2 := ih (fun x hx => h x (by simp only [List.mem_cons, hx, or_true]))
    have h3 : 1 ≤ (spell t).length := by
      cases e : spell t with
      | nil => exact absurd e h1
      | cons _ _ => simp only [List.length_cons, Nat.le_add_left]
    simp only [render, List.length_append, List.length_cons, List.length_cons]
    omega

/-- A decidable sufficient test for `TokGut` (floats excepted: the test refuses them, `GleitKanon`
    is stated over the existential spelling). For witnesses over concrete token lists. -/
def tokGutB : Token → Bool
  | .ident s => nameForm s && !istSchluessel s
  | .wort s => nameForm s && istSchluessel s
  | .num _ => true
  | .float _ => false
  | .text s => s.toList.all (fun c => c != '"' && c != '\n')
  | .zeichen s => markTafel.contains s.toList
  | .doku _ => false
  | .ende => false

theorem tokGutB_gut : ∀ (t : Token), tokGutB t = true → TokGut t := by
  intro t h
  cases t with
  | ident s =>
    simp only [tokGutB, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact h
  | wort s =>
    simp only [tokGutB, Bool.and_eq_true] at h
    exact h
  | num n => trivial
  | float s => simp only [tokGutB, Bool.false_eq_true] at h
  | text s =>
    simp only [tokGutB, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    exact h
  | zeichen s =>
    simp only [tokGutB, List.contains_iff_mem] at h
    exact h
  | doku _ => simp only [tokGutB, Bool.false_eq_true] at h
  | ende => simp only [tokGutB, Bool.false_eq_true] at h

theorem tokGut_of_all : ∀ (ts : List Token), ts.all tokGutB = true → ∀ t ∈ ts, TokGut t := by
  intro ts h t ht
  exact tokGutB_gut t (List.all_eq_true.mp h t ht)

/-- **L1: the lexer reads the rendered text back.** For every lexically clean token list, lexing
    the rendered text returns the list with the end marker. -/
theorem lex_render (ts : List Token) (h : ∀ t ∈ ts, TokGut t) :
    lex (renderText ts) = .ok (ts ++ [.ende]) := by
  unfold renderText
  rw [lex_ofList]
  unfold lexL
  exact scan_render ts _ h (by have := render_laenge ts h; omega)

/-- Witness of `lex_render` on a list with every token class: a keyword, an identifier, a number
    with several digits, a float with an exponent, a string, a three-character mark and a
    single mark. -/
theorem lex_render_zeuge :
    let ts := [Token.wort "fn", .ident "lies", .zeichen "(", .num 4096, .zeichen "<<%",
      .float "1.5e-3", .text "a b", .zeichen ")"]
    (∀ t ∈ ts, TokGut t) ∧ lex (renderText ts) = .ok (ts ++ [.ende]) := by
  intro ts
  have h : ∀ t ∈ ts, TokGut t := by
    intro t ht
    simp only [ts, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, by decide⟩
    · exact ⟨by decide, by decide⟩
    · show ['('] ∈ markTafel; decide
    · trivial
    · show ['<', '<', '%'] ∈ markTafel; decide
    · exact ⟨1, ['5'], ['e', '-', '3'], by decide, by decide, by decide,
        Or.inr ⟨['e', '-'], ['3'], Or.inr (Or.inr rfl), rfl, by decide, by decide⟩⟩
    · intro c hc
      have : c ∈ ['a', ' ', 'b'] := hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with rfl | rfl | rfl <;> decide
    · show [')'] ∈ markTafel; decide
  exact ⟨h, lex_render ts h⟩

/-- The class is not vacuous in the other direction either: an identifier token spelling a
    keyword is outside it, and the lexer indeed reads its rendering as the keyword. -/
theorem lex_render_ident_wort :
    ¬ TokGut (.ident "x") ∧ lex (renderText [.ident "x"]) = .ok [.wort "x", .ende] := by
  refine ⟨?_, by decide⟩
  intro h; exact absurd h.2 (by decide)

end Gabbro.Grammatik.Parser

#print axioms Gabbro.Grammatik.Parser.lex_render
#print axioms Gabbro.Grammatik.Parser.lex_render_zeuge
#print axioms Gabbro.Grammatik.Parser.lex_render_ident_wort
