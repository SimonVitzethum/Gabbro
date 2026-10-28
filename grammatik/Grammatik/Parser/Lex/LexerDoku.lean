/-
  File:      Grammatik/Parser/Lex/LexerDoku.lean
  Subject:   Doc comments change no program: the token stream `lex` (the one
             the parser reads) never holds a `Token.doku`; only `lexDoku`
             keeps the `///` trivia. The theorem is over EVERY source text,
             with a witness (`lex_ohne_doku_beispiel` in `Lexer.lean` shows
             a source whose `lexDoku` holds doc tokens and whose `lex` does
             not, so the statement is not vacuous).
-/
import Grammatik.Parser.Lex.Lexer

namespace Gabbro.Grammatik.Parser

theorem map_cons_ohne_doku (a : Token) (ha : ∀ t, a ≠ Token.doku t)
    (r : Except LexFehler (List Token)) (ts : List Token)
    (h : Except.map (a :: ·) r = .ok ts)
    (ih : ∀ ts, r = .ok ts → ∀ t, Token.doku t ∉ ts) :
    ∀ t, Token.doku t ∉ ts := by
  cases r with
  | error e => simp only [Except.map, reduceCtorEq] at h
  | ok x =>
    simp only [Except.map, Except.ok.injEq] at h
    subst h
    intro t hm
    rcases List.mem_cons.mp hm with h1 | h1
    · exact ha t h1.symm
    · exact ih x rfl t h1

theorem zahlWeiter_kein_doku (v : Nat) (cs : List Char) (t : Token) (r : List Char)
    (h : zahlWeiter v cs = .ok (t, r)) : ∀ s, t ≠ Token.doku s := by
  intro s
  unfold zahlWeiter at h
  split at h <;> (try split at h) <;>
    (first | (obtain ⟨rfl, -⟩ := h; simp only [ne_eq, reduceCtorEq, not_false_eq_true]) | (simp at h; obtain ⟨rfl, -⟩ := h; simp) | simp_all)

theorem zahlBasis_kein_doku (b : Nat) (cs : List Char) (t : Token) (r : List Char)
    (h : zahlBasis b cs = .ok (t, r)) : ∀ s, t ≠ Token.doku s := by
  intro s
  unfold zahlBasis at h
  split at h
  split at h
  · simp only [reduceCtorEq] at h
  · split at h <;> (try split at h) <;> (try split at h) <;>
      first | exact zahlWeiter_kein_doku _ _ _ _ h s | (first | (obtain ⟨rfl, -⟩ := h; simp only [Nat.toString_eq_repr, ↓Char.isValue, ne_eq, reduceCtorEq, not_false_eq_true]) | (simp at h; obtain ⟨rfl, -⟩ := h; simp) | simp_all)

theorem scanZahlKopf_kein_doku (cs : List Char) (t : Token) (r : List Char)
    (h : scanZahlKopf cs = .ok (t, r)) : ∀ s, t ≠ Token.doku s := by
  intro s
  unfold scanZahlKopf at h
  split at h <;> first | exact zahlBasis_kein_doku _ _ _ _ h s | simp only [reduceCtorEq] at h

theorem scan_ohne_doku (cs : List Char) (n : Nat) :
    ∀ ts, scan false cs n = .ok ts → ∀ t, Token.doku t ∉ ts := by
  induction n generalizing cs with
  | zero =>
    intro ts h t
    cases cs with
    | nil => simp only [scan, Except.ok.injEq] at h; subst h; simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, not_false_eq_true]
    | cons c cs => simp only [scan, reduceCtorEq] at h
  | succ n ih =>
    intro ts h t
    unfold scan at h
    split at h
    all_goals (try (obtain rfl := Nat.succ.inj ‹n + 1 = Nat.succ _›))
    · simp only [Except.ok.injEq] at h; subst h; simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, not_false_eq_true]
    · exact ih _ _ h t
    · simp only [Bool.false_eq_true, ↓reduceIte] at h; exact ih _ _ h t
    · exact ih _ _ h t
    · split at h
      · exact ih _ _ h t
      · simp only [reduceCtorEq] at h
    · split at h
      · exact map_cons_ohne_doku _ (by intro _; simp only [ne_eq, reduceCtorEq, not_false_eq_true]) _ _ h (fun _ h' => ih _ _ h') t
      · simp only [reduceCtorEq] at h
    · split at h
      · exact ih _ _ h t
      · split at h
        · split at h
          · exact map_cons_ohne_doku _ (scanZahlKopf_kein_doku _ _ _ ‹_›) _ _ h (fun _ h' => ih _ _ h') t
          · simp only [reduceCtorEq] at h
        · split at h
          · exact map_cons_ohne_doku _ (by intro t; split <;> simp only [String.ofList_cons, ne_eq, reduceCtorEq, not_false_eq_true]) _ _ h
              (fun _ h' => ih _ _ h') t
          · split at h
            · exact map_cons_ohne_doku _ (by intro _; simp only [ne_eq, reduceCtorEq, not_false_eq_true]) _ _ h (fun _ h' => ih _ _ h') t
            · simp only [String.ofList_cons, String.ofList_nil, String.append_empty, reduceCtorEq] at h
    · simp only [reduceCtorEq] at h

/-- **`lex` NEVER HOLDS A DOC TOKEN**, for every source text: a `///` comment
    cannot change what the parser reads. -/
theorem lex_ohne_doku (s : String) :
    ∀ ts, lex s = .ok ts → ∀ t, Token.doku t ∉ ts :=
  fun ts h t => scan_ohne_doku _ _ ts h t

/-- Witness that the premise is inhabited and the doc stream differs: a
    source with a doc comment lexes, and its `lexDoku` has the `doku` token
    that `lex` lacks. -/
theorem lex_ohne_doku_zeuge :
    ∃ ts, lex "/// d\nfn" = .ok ts ∧
      lexDoku "/// d\nfn" ≠ .ok ts := by
  refine ⟨[Token.wort "fn", Token.ende], ?_, ?_⟩ <;> decide

end Gabbro.Grammatik.Parser

#print axioms Gabbro.Grammatik.Parser.lex_ohne_doku
