/-
  File:      Grammatik/Parser/Round/RundlaufLex.lean
  Subject:   Layer L1 of the syntax round trip: a token renderer and the theorem that the lexer
             reads the rendered text back, token for token.

  `render ts` writes every token in its canonical spelling followed by one space. `lex_render`:
  for every token list in the class `TokGut` (below), `lex (String.ofList (render ts)) =
  .ok (ts ++ [.ende])` -- the lexer returns exactly the list, with the end marker it always emits.

  The class, token by token (`TokGut`), and what it excludes:
  - `ident s`: `s` is name-shaped (a `istAnfang` head, `istFolge` tail) and NOT a table word
    (`istSchluessel s = false`). Excluded: an identifier token that spells a keyword (`x`, `r`,
    `Some`, ...): the lexer reads every table word as `wort`, so such a token cannot come back as
    `ident` (the parsers read names through `nameText`, which takes both; the class is about the
    LEXER, which has no such freedom).
  - `wort s`: name-shaped and a table word.
  - `num n`: every `n`, spelled by `Nat.toDigits 10` (the spelling of `toString n`).
  - `float s`: the canonical float spelling the lexer itself builds: `toString v ++ "." ++ frac
    ++ exp` with a non-empty digit fraction and an exponent that is empty or `e`/`e+`/`e-`
    followed by digits (`GleitKanon`). Excluded: `_` separators, leading zeros, uppercase `E`,
    and any text that is not a float literal at all (`"1.0 rounded"`, see the CUTS).
  - `text s`: no `"` and no newline in `s` (the lexer has no escapes).
  - `zeichen s`: one of the marks the lexer cuts (`markTafel`, the 47 spellings of
    `nimmZeichen`).
  - `doku`, `ende`: excluded (`lex` drops doc comments and emits `ende` itself).

  The proof is one lemma per token class (`scan_name`, `scan_zahl`, `scan_gleit`, `scan_text`,
  `scan_zeichen`): the scanner reads the token's spelling plus the separating space in exactly two
  fuel steps and continues on the rest. List induction (`scan_render`) and the fuel count
  (`render_laenge`) give `lex_render`.
-/
module

public import Grammatik.Parser.Round.RundlaufLex.Teil1a

public import Grammatik.Parser.Lex.Lexer
import all Init.Data.Repr
import all Init.Data.String.Defs

@[expose] public section



namespace Gabbro.Grammatik.Parser

set_option maxRecDepth 100000

theorem toDigits_ziffern : ∀ (n : Nat), (Nat.toDigits 10 n).all istZiffer = true := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [Nat.toDigits_eq_ite (by decide)]
    have hd : ∀ k, k < 10 → istZiffer (Nat.digitChar k) = true := by decide
    split
    · simp only [List.all_cons, hd n (by omega), List.all_nil, Bool.and_self]
    · simp only [List.all_append, Bool.and_eq_true, List.all_cons, List.all_nil, Bool.and_true]
      exact ⟨ih (n / 10) (by omega), hd (n % 10) (Nat.mod_lt _ (by decide))⟩

theorem nimmZiffern_kanon (ds : List Char) (c : Char) (r : List Char) (hne : ds ≠ [])
    (hd : ds.all istZiffer = true) (hz : istZiffer c = false) (hu : c ≠ '_') :
    nimmZiffern (ds ++ c :: r) 10 = (Nat.ofDigitChars 10 ds 0, true, c :: r) := by
  unfold nimmZiffern
  rw [nimmZiffern_go _ _ _ _ hd, nimmZiffern_go_stop c r _ _ hz hu]
  cases ds with
  | nil => exact absurd rfl hne
  | cons _ _ => rfl

/-- Two characters that are not a base prefix: the number head is decimal. -/
theorem scanZahlKopf_dez (c1 c2 : Char) (r : List Char)
    (h : c2 ≠ 'x' ∧ c2 ≠ 'b' ∧ c2 ≠ 'X' ∧ c2 ≠ 'B') :
    scanZahlKopf (c1 :: c2 :: r) = zahlBasis 10 (c1 :: c2 :: r) := by
  unfold scanZahlKopf
  split <;> simp_all

theorem scanZahlKopf_eins (c1 : Char) : scanZahlKopf [c1] = zahlBasis 10 [c1] := by
  unfold scanZahlKopf
  split <;> simp_all

theorem ziffer_kein_praefix {c : Char} (h : istZiffer c = true) :
    c ≠ 'x' ∧ c ≠ 'b' ∧ c ≠ 'X' ∧ c ≠ 'B' :=
  ⟨istZiffer_ne h _ (by decide), istZiffer_ne h _ (by decide), istZiffer_ne h _ (by decide),
   istZiffer_ne h _ (by decide)⟩

/-- A digit run (non-empty, all digits) followed by a character that is no base prefix: the
    scanner's number arm takes the decimal reader. -/
theorem scan_ziffer_kopf (b : Bool) (c : Char) (cs : List Char) (n : Nat)
    (hc : istZiffer c = true) :
    scan b (c :: cs) (n + 1) =
      match scanZahlKopf (c :: cs) with
      | .ok (t, rest) => Except.map (t :: ·) (scan b rest n)
      | .error e => .error e := by
  rw [scan.eq_7]
  · simp only [istZiffer_nicht_leer hc, hc, ite_true, Bool.false_eq_true, ite_false]
    rfl
  · intro _ e _; exact istZiffer_ne hc '/' (by decide) e
  · intro _ e _; exact istZiffer_ne hc '/' (by decide) e
  · intro _ e _; exact istZiffer_ne hc '/' (by decide) e
  · intro _ e _; exact istZiffer_ne hc '/' (by decide) e
  · intro e; exact istZiffer_ne hc '"' (by decide) e

theorem scanZahlKopf_lauf (ds : List Char) (c : Char) (r : List Char) (hne : ds ≠ [])
    (hd : ds.all istZiffer = true) (hc : c ≠ 'x' ∧ c ≠ 'b' ∧ c ≠ 'X' ∧ c ≠ 'B') :
    scanZahlKopf (ds ++ c :: r) = zahlBasis 10 (ds ++ c :: r) := by
  match ds, hne, hd with
  | [d], _, _ => exact scanZahlKopf_dez d c r hc
  | d :: e :: ds, _, hd =>
    simp only [List.all_cons, Bool.and_eq_true] at hd
    exact scanZahlKopf_dez d e _ (ziffer_kein_praefix hd.2.1)

theorem scan_zahl (b : Bool) (n : Nat) (rest : List Char) (m : Nat) :
    scan b (Nat.toDigits 10 n ++ ' ' :: rest) (m + 2) =
      Except.map (Token.num n :: ·) (scan b rest m) := by
  have hd := toDigits_ziffern n
  have hne : Nat.toDigits 10 n ≠ [] := Nat.toDigits_ne_nil
  obtain ⟨c, cs, hcs⟩ : ∃ c cs, Nat.toDigits 10 n = c :: cs := by
    cases h : Nat.toDigits 10 n with
    | nil => exact absurd h hne
    | cons c cs => exact ⟨c, cs, rfl⟩
  have hc : istZiffer c = true := by rw [hcs] at hd; simp only [List.all_cons, Bool.and_eq_true, List.all_eq_true] at hd; exact hd.1
  have hk := scanZahlKopf_lauf (Nat.toDigits 10 n) ' ' rest hne hd (by decide)
  have hz := nimmZiffern_kanon _ ' ' rest hne hd (by decide) (by decide)
  rw [hcs, List.cons_append, scan_ziffer_kopf b c _ _ hc, ← List.cons_append, ← hcs, hk]
  simp only [zahlBasis, hz, Nat.ofDigitChars_ten_toDigits]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, BEq.rfl, ↓Char.isValue, List.cons.injEq,
  Char.reduceEq, false_and, imp_self, implies_true, zahlWeiter, istAnfang, Char.reduceToNat, Nat.reduceLeDiff,
  decide_false, decide_true, Bool.and_true, Bool.or_self, istZiffer, scan_leer]

/-! ### Floats -/

theorem nimmDez_ziffern : ∀ (ds : List Char) (c : Char) (r : List Char),
    ds.all istZiffer = true → istZiffer c = false → c ≠ '_' →
    nimmDez (ds ++ c :: r) = (ds, c :: r) := by
  intro ds c r hd hz hu
  induction ds with
  | nil =>
    have : (c == '_') = false := by simpa using hu
    simp only [List.nil_append, nimmDez, ↓Char.isValue, this, Bool.false_eq_true, ↓reduceIte, hz]
  | cons d ds ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hd
    have : (d == '_') = false := by
      cases e : (d == '_')
      · rfl
      · simp only [beq_iff_eq] at e; subst e; simp only [istZiffer, ↓Char.isValue, Char.reduceToNat, Nat.reduceLeDiff, decide_true, decide_false,
  Bool.and_false, Bool.false_eq_true, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, false_and] at hd
    simp only [List.cons_append, nimmDez, ↓Char.isValue, this, Bool.false_eq_true, ↓reduceIte, hd.1, ih hd.2]

theorem nimmDezStreng_ziffern : ∀ (ds : List Char) (r : List Char),
    ds.all istZiffer = true →
    nimmDezStreng (ds ++ ' ' :: r) = (ds, ' ' :: r) := by
  intro ds r hd
  induction ds with
  | nil => simp only [↓Char.isValue, List.nil_append, nimmDezStreng, istZiffer, Char.reduceToNat, Nat.reduceLeDiff,
  decide_false, decide_true, Bool.and_true, Bool.false_eq_true, ↓reduceIte]
  | cons d ds ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hd
    simp only [↓Char.isValue, List.cons_append, nimmDezStreng, hd.1, ↓reduceIte, ih hd.2]

theorem nimmExponent_kanon (ex r : List Char) (h : ExpForm ex) :
    nimmExponent (ex ++ ' ' :: r) = (String.ofList ex, ' ' :: r) := by
  rcases h with rfl | ⟨p, ds, hp, rfl, hne, hd⟩
  · simp only [nimmExponent, ↓Char.isValue, List.nil_append, List.cons.injEq, Char.reduceEq, false_and, imp_self,
  implies_true, String.ofList_nil]
  · obtain ⟨d, ds', rfl⟩ : ∃ d ds', ds = d :: ds' := by
      cases ds with
      | nil => exact absurd rfl hne
      | cons d ds' => exact ⟨d, ds', rfl⟩
    have hdz : istZiffer d = true := by simp only [List.all_cons, Bool.and_eq_true, List.all_eq_true] at hd; exact hd.1
    rcases hp with rfl | rfl | rfl
    · have h1 : d ≠ '+' := istZiffer_ne hdz _ (by decide)
      have h2 : d ≠ '-' := istZiffer_ne hdz _ (by decide)
      simp only [List.cons_append, List.nil_append]
      rw [nimmExponent.eq_3]
      · rw [← List.cons_append, nimmDezStreng_ziffern _ _ hd]
        simp only
        rw [show ("e" : String) = String.ofList ['e'] from rfl, ← String.ofList_append]
        rfl
      · intro _ e; simp_all
      · intro _ e; simp_all
    · simp only [List.cons_append, List.nil_append, nimmExponent]
      rw [← List.cons_append, nimmDezStreng_ziffern _ _ hd]
      simp only
      rw [show ("e+" : String) = String.ofList ['e', '+'] from rfl, ← String.ofList_append]
      rfl
    · simp only [List.cons_append, List.nil_append, nimmExponent]
      rw [← List.cons_append, nimmDezStreng_ziffern _ _ hd]
      simp only
      rw [show ("e-" : String) = String.ofList ['e', '-'] from rfl, ← String.ofList_append]
      rfl

theorem expForm_kopf (ex r : List Char) (h : ExpForm ex) :
    ∃ c r', ex ++ ' ' :: r = c :: r' ∧ istZiffer c = false ∧ c ≠ '_' := by
  rcases h with rfl | ⟨p, ds, hp, rfl, _, _⟩
  · exact ⟨' ', r, rfl, by decide, by decide⟩
  · rcases hp with rfl | rfl | rfl <;> exact ⟨'e', _, rfl, by decide, by decide⟩

theorem scan_gleit (b : Bool) (s : String) (rest : List Char) (m : Nat) (h : GleitKanon s) :
    scan b (s.toList ++ ' ' :: rest) (m + 2) =
      Except.map (Token.float s :: ·) (scan b rest m) := by
  obtain ⟨v, frac, ex, rfl, hfne, hfd, hex⟩ := h
  have hd := toDigits_ziffern v
  have hne : Nat.toDigits 10 v ≠ [] := Nat.toDigits_ne_nil
  obtain ⟨f, fs, rfl⟩ : ∃ f fs, frac = f :: fs := by
    cases frac with
    | nil => exact absurd rfl hfne
    | cons f fs => exact ⟨f, fs, rfl⟩
  have hfz : istZiffer f = true := by simp only [List.all_cons, Bool.and_eq_true, List.all_eq_true] at hfd; exact hfd.1
  have hfsd : fs.all istZiffer = true := by simp only [List.all_cons, Bool.and_eq_true, List.all_eq_true] at hfd ⊢; exact fun x hx => hfd.2 x hx
  have hl : (toString v ++ "." ++ String.ofList (f :: fs) ++ String.ofList ex).toList ++
      ' ' :: rest = Nat.toDigits 10 v ++ '.' :: (f :: fs ++ (ex ++ ' ' :: rest)) := by
    simp only [Nat.toString_eq_repr, String.ofList_cons, String.toList_append, Nat.toList_repr,
  String.reduceToList, ↓Char.isValue, String.toList_singleton, String.toList_ofList, List.cons_append, List.nil_append,
  List.append_assoc]
  rw [hl]
  obtain ⟨c, cs, hcs⟩ : ∃ c cs, Nat.toDigits 10 v = c :: cs := by
    cases h : Nat.toDigits 10 v with
    | nil => exact absurd h hne
    | cons c cs => exact ⟨c, cs, rfl⟩
  have hc : istZiffer c = true := by rw [hcs] at hd; simp only [List.all_cons, Bool.and_eq_true, List.all_eq_true] at hd; exact hd.1
  have hk := scanZahlKopf_lauf (Nat.toDigits 10 v) '.' (f :: fs ++ (ex ++ ' ' :: rest)) hne hd
    (by decide)
  have hz := nimmZiffern_kanon _ '.' (f :: fs ++ (ex ++ ' ' :: rest)) hne hd (by decide)
    (by decide)
  rw [hcs, List.cons_append, scan_ziffer_kopf b c _ _ hc, ← List.cons_append, ← hcs, hk]
  simp only [zahlBasis, hz, Nat.ofDigitChars_ten_toDigits]
  obtain ⟨c2, r2, he, hz2, hu2⟩ := expForm_kopf ex rest hex
  have hnd : nimmDez (f :: fs ++ (ex ++ ' ' :: rest)) = (f :: fs, ex ++ ' ' :: rest) := by
    rw [he]; exact nimmDez_ziffern _ c2 r2 hfd hz2 hu2
  simp only [Bool.not_true, Bool.false_eq_true, ite_false, beq_self_eq_true, ite_true,
    List.cons_append, hfz]
  rw [← List.cons_append, hnd]
  simp only
  rw [nimmExponent_kanon ex rest hex]
  simp only [Nat.toString_eq_repr, String.ofList_cons, ↓Char.isValue, scan_leer]

/-! ### Strings -/

theorem nimmText_kanon : ∀ (cs r : List Char), (∀ c ∈ cs, c ≠ '"' ∧ c ≠ '\n') →
    nimmText (cs ++ '"' :: r) = some (cs, r) := by
  intro cs r h
  induction cs with
  | nil => simp only [↓Char.isValue, List.nil_append, nimmText]
  | cons c cs ih =>
    have hc := h c (by simp only [List.mem_cons, true_or])
    have ih' := ih (fun x hx => h x (by simp only [List.mem_cons, hx, or_true]))
    simp only [List.cons_append]
    rw [nimmText.eq_4]
    · simp only [↓Char.isValue, ih']
    · simp_all
    · simp_all

theorem scan_text (b : Bool) (s : String) (rest : List Char) (m : Nat)
    (h : ∀ c ∈ s.toList, c ≠ '"' ∧ c ≠ '\n') :
    scan b (('"' :: (s.toList ++ ['"'])) ++ ' ' :: rest) (m + 2) =
      Except.map (Token.text s :: ·) (scan b rest m) := by
  simp only [List.cons_append, List.append_assoc, List.nil_append]
  rw [scan.eq_6, nimmText_kanon _ _ h]
  simp only [String.ofList_toList, ↓Char.isValue, scan_leer]

/-! ### Marks -/

/-- The head of a mark: no whitespace, digit, name start or quote, and a `/` only alone (so no
    comment opener). -/
def markKopfGut : List Char → Bool
  | c :: cs => !istLeer c && !istZiffer c && !istAnfang c && c != '"' && (c != '/' || cs.isEmpty)
  | [] => false

theorem markTafel_koepfe : markTafel.all markKopfGut = true := by decide

theorem nimmZeichen_mark (l rest : List Char) (h : l ∈ markTafel) :
    nimmZeichen (l ++ ' ' :: rest) = some (String.ofList l, ' ' :: rest) := by
  simp only [markTafel, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h <;> subst h <;> simp only [nimmZeichen, ↓Char.isValue, List.cons_append, List.nil_append, String.ofList_cons, String.reduceSingleton, String.ofList_nil, String.append_empty, String.reduceAppend, List.cons.injEq, Char.reduceEq, false_and, imp_self, implies_true, istEinfach, ↓reduceIte] <;> rfl

end Gabbro.Grammatik.Parser
