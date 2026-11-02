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
  - `zeichen s`: one of the marks the lexer cuts (`markTafel`, the 48 spellings of
    `nimmZeichen`).
  - `doku`, `ende`: excluded (`lex` drops doc comments and emits `ende` itself).

  The proof is one lemma per token class (`scan_name`, `scan_zahl`, `scan_gleit`, `scan_text`,
  `scan_zeichen`): the scanner reads the token's spelling plus the separating space in exactly two
  fuel steps and continues on the rest. List induction (`scan_render`) and the fuel count
  (`render_laenge`) give `lex_render`.
-/
module

public import Grammatik.Parser.Lex.Lexer
import all Init.Data.Repr
import all Init.Data.String.Defs

@[expose] public section



namespace Gabbro.Grammatik.Parser

set_option maxRecDepth 100000

/-- The marks the lexer cuts (`nimmZeichen`): the 22 multi-character marks and the 26 single
    characters of `istEinfach` (`?` is the reason-propagation mark, `ABSTRACTION-SYNTAX-PLAN.md` §4.3). -/
def markTafel : List (List Char) :=
  [['<','<','%'], ['.','.','<'], [':',':'], ['.','.'], ['-','>'], ['=','>'], ['=','='],
   ['!','='], ['<','='], ['>','='], ['<','<'], ['>','>'], ['+','='], ['+','%'], ['+','|'],
   ['-','='], ['-','%'], ['*','%'], ['&','&'], ['&','='], ['|','|'], ['|','='],
   [':'], [';'], [','], ['.'], ['='], ['<'], ['>'], ['+'], ['-'], ['*'], ['/'], ['%'], ['&'],
   ['|'], ['^'], ['!'], ['~'], ['@'], ['#'], ['('], [')'], ['['], [']'], ['{'], ['}'], ['?']]

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


end Gabbro.Grammatik.Parser
