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
import Grammatik.Parser.Lex.Lexer

namespace Gabbro.Grammatik.Parser

set_option maxRecDepth 100000

/-- The marks the lexer cuts (`nimmZeichen`): the 22 multi-character marks and the 25 single
    characters of `istEinfach`. -/
def markTafel : List (List Char) :=
  [['<','<','%'], ['.','.','<'], [':',':'], ['.','.'], ['-','>'], ['=','>'], ['=','='],
   ['!','='], ['<','='], ['>','='], ['<','<'], ['>','>'], ['+','='], ['+','%'], ['+','|'],
   ['-','='], ['-','%'], ['*','%'], ['&','&'], ['&','='], ['|','|'], ['|','='],
   [':'], [';'], [','], ['.'], ['='], ['<'], ['>'], ['+'], ['-'], ['*'], ['/'], ['%'], ['&'],
   ['|'], ['^'], ['!'], ['~'], ['@'], ['#'], ['('], [')'], ['['], [']'], ['{'], ['}']]

/-- A name-shaped spelling: a name start, then name continuations. -/
def nameForm (s : String) : Bool :=
  match s.toList with
  | c :: cs => istAnfang c && cs.all istFolge
  | [] => false

/-- The exponent part of a canonical float: empty, or `e`, `e+`, `e-` followed by digits. -/
def ExpForm (ex : List Char) : Prop :=
  ex = [] ∨
  ∃ (p : List Char) (ds : List Char), (p = ['e'] ∨ p = ['e', '+'] ∨ p = ['e', '-']) ∧
    ex = p ++ ds ∧ ds ≠ [] ∧ ds.all istZiffer = true

/-- The canonical float spelling: the text the lexer builds for a float literal
    (`zahlBasis`: `toString v ++ "." ++ fraction ++ exponent`). -/
def GleitKanon (s : String) : Prop :=
  ∃ (v : Nat) (frac ex : List Char),
    s = toString v ++ "." ++ String.ofList frac ++ String.ofList ex ∧
    frac ≠ [] ∧ frac.all istZiffer = true ∧ ExpForm ex

/-- The lexically clean tokens: the class over which `render` is read back (see the header). -/
def TokGut : Token → Prop
  | .ident s => nameForm s = true ∧ istSchluessel s = false
  | .wort s => nameForm s = true ∧ istSchluessel s = true
  | .num _ => True
  | .float s => GleitKanon s
  | .text s => ∀ c ∈ s.toList, c ≠ '"' ∧ c ≠ '\n'
  | .zeichen s => s.toList ∈ markTafel
  | .doku _ => False
  | .ende => False

/-- The canonical spelling of one token. -/
def spell : Token → List Char
  | .ident s => s.toList
  | .wort s => s.toList
  | .num n => Nat.toDigits 10 n
  | .float s => s.toList
  | .text s => '"' :: (s.toList ++ ['"'])
  | .zeichen s => s.toList
  | .doku _ => []
  | .ende => []

/-- The renderer: every token in its canonical spelling, followed by one space. -/
def render : List Token → List Char
  | [] => []
  | t :: ts => spell t ++ ' ' :: render ts

/-- The rendered source text. -/
def renderText (ts : List Token) : String := String.ofList (render ts)

/-! ### Character facts -/

theorem istLeer_wahr {c : Char} (h : istLeer c = true) :
    c = ' ' ∨ c = '\t' ∨ c = '\r' ∨ c = '\n' := by
  unfold istLeer at h
  split at h <;> simp_all

theorem istZiffer_nicht_leer {c : Char} (h : istZiffer c = true) : istLeer c = false := by
  cases hl : istLeer c
  · rfl
  · rcases istLeer_wahr hl with rfl | rfl | rfl | rfl <;> simp_all [istZiffer]

theorem istAnfang_nicht_leer {c : Char} (h : istAnfang c = true) : istLeer c = false := by
  cases hl : istLeer c
  · rfl
  · rcases istLeer_wahr hl with rfl | rfl | rfl | rfl <;> simp_all [istAnfang]

theorem istZiffer_nicht_anfang {c : Char} (h : istZiffer c = true) : istAnfang c = false := by
  unfold istAnfang
  split <;> simp_all [istZiffer] <;> omega

theorem istZiffer_ne {c : Char} (h : istZiffer c = true) (d : Char) (hd : istZiffer d = false) :
    c ≠ d := by
  intro e; subst e; simp_all

theorem istAnfang_ne {c : Char} (h : istAnfang c = true) (d : Char) (hd : istAnfang d = false) :
    c ≠ d := by
  intro e; subst e; simp_all

theorem hexWert_ziffer {c : Char} (h : istZiffer c = true) :
    hexWert c 10 = some (c.toNat - 48) := by
  simp only [istZiffer, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [hexWert, Bool.and_eq_true, decide_eq_true_eq]
  rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true (by omega))]

theorem hexWert_nicht {c : Char} (h : istZiffer c = false) (b : Nat) : hexWert c b = none ∨ b == 16 := by
  simp only [istZiffer, Bool.and_eq_false_iff, decide_eq_false_iff_not] at h
  unfold hexWert
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  split
  · right; assumption
  · left; rfl

/-! ### Names -/

theorem nimmFolge_name : ∀ (cs rest : List Char), cs.all istFolge = true →
    nimmFolge (cs ++ ' ' :: rest) = (cs, ' ' :: rest) := by
  intro cs rest h
  induction cs with
  | nil => simp only [↓Char.isValue, List.nil_append, nimmFolge, istFolge, istAnfang, Char.reduceEq, imp_self,
  Char.reduceToNat, Nat.reduceLeDiff, decide_false, decide_true, Bool.and_true, Bool.or_self, istZiffer,
  Bool.false_eq_true, ↓reduceIte]
  | cons c cs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [List.cons_append, nimmFolge, h.1, ite_true, ih h.2]

theorem scan_leer (b : Bool) (rest : List Char) (m : Nat) :
    scan b (' ' :: rest) (m + 1) = scan b rest m := by
  simp [scan, istLeer]

theorem scan_name (b : Bool) (s : String) (rest : List Char) (m : Nat) (h : nameForm s = true) :
    scan b (s.toList ++ ' ' :: rest) (m + 2) =
      Except.map ((if istSchluessel s = true then Token.wort s else Token.ident s) :: ·)
        (scan b rest m) := by
  unfold nameForm at h
  generalize hs : s.toList = l at h
  match l, h with
  | c :: cs, h =>
    simp only [Bool.and_eq_true] at h
    have hl := istAnfang_nicht_leer h.1
    have hz : istZiffer c = false := by
      cases hz : istZiffer c
      · rfl
      · have := istZiffer_nicht_anfang hz; simp_all
    have hsl : (String.ofList (c :: cs)) = s := by rw [← hs, String.ofList_toList]
    rw [List.cons_append, scan.eq_7]
    · simp only [hl, hz, h.1, ite_true, Bool.false_eq_true, ite_false]
      rw [nimmFolge_name cs rest h.2]
      simp only [hsl, scan_leer]
    · intro _ e _; exact istAnfang_ne h.1 '/' (by decide) e
    · intro _ e _; exact istAnfang_ne h.1 '/' (by decide) e
    · intro _ e _; exact istAnfang_ne h.1 '/' (by decide) e
    · intro _ e _; exact istAnfang_ne h.1 '/' (by decide) e
    · intro e; exact istAnfang_ne h.1 '"' (by decide) e

/-! ### Numbers -/

theorem nimmZiffern_go : ∀ (ds r : List Char) (acc : Nat) (g : Bool),
    ds.all istZiffer = true →
    nimmZiffern.go 10 (ds ++ r) acc g =
      nimmZiffern.go 10 r (Nat.ofDigitChars 10 ds acc) (g || !ds.isEmpty) := by
  intro ds r acc g h
  induction ds generalizing acc g with
  | nil => simp only [List.nil_append, Nat.ofDigitChars_nil, List.isEmpty_nil, Bool.not_true, Bool.or_false]
  | cons c ds ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    have hc : (c == '_') = false := by
      cases e : (c == '_')
      · rfl
      · simp only [beq_iff_eq] at e; subst e; simp only [istZiffer, ↓Char.isValue, Char.reduceToNat, Nat.reduceLeDiff, decide_true, decide_false,
  Bool.and_false, Bool.false_eq_true, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, false_and] at h
    simp only [List.cons_append, nimmZiffern.go, hc, Bool.false_eq_true, ite_false,
      hexWert_ziffer h.1]
    rw [ih _ _ h.2, Nat.ofDigitChars_cons]
    simp only [Bool.true_or, Nat.mul_comm, ↓Char.isValue, Char.reduceToNat, List.isEmpty_cons, Bool.not_false,
  Bool.or_true]

theorem nimmZiffern_go_stop (c : Char) (r : List Char) (acc : Nat) (g : Bool)
    (hz : istZiffer c = false) (hu : c ≠ '_') :
    nimmZiffern.go 10 (c :: r) acc g = (acc, g, c :: r) := by
  have hc : (c == '_') = false := by simpa using hu
  rcases hexWert_nicht hz 10 with h | h
  · simp only [nimmZiffern.go, ↓Char.isValue, hc, Bool.false_eq_true, ↓reduceIte, h]
  · simp only [Nat.reduceBEq, Bool.false_eq_true] at h

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
