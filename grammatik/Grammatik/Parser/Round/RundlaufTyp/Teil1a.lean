/-
  File:      Grammatik/Parser/Round/RundlaufTyp.lean
  Subject:   Layer L2b, part one: the pieces under the statements -- raw header texts, bare names that
             the printer re-lexes, and surface types (`druckTyp` read back by `parseTyp`).

  Raw texts. The reader keeps several headers as text (`retry`/`forever` headers, `traverse`
  `decreases`/`touches` words, `narrow` ranges, `publishes`/`awaits` payloads, `exchange` tails); the
  printer re-lexes the text (`rohToks`). A text read back is the rendered token list (L1's
  `renderText`), so the round-trip class of a raw field is: the field IS `renderText ts` for a
  lexically clean `ts` that holds none of the collector's stop tokens (`roh_*` below). Each
  collector (`traverseRest`, `schleifenKopf`, `nimmBisWort`, `nimmBisZeichen`) returns exactly that
  text (`renderText_cons`: one token, one space).

  Bare names. A call head and a `start` root ride as text (`rohToks f`); `rohToks_name`: a
  name-shaped `f` re-lexes to the one token the lexer reads for it (`nameTok f`).

  Types (`TypGut`): atoms (not one of the type-head words), paths of two or more segments,
  `range`/`wrapping` suffix chains over them, `ptr<space, right> T` with a single right,
  `[option] index into t`, arrays, `string max e`. `parse_druckTyp`: every `TypGut` type reads back
  before a type follow (`TypFolge`: no suffix word, no `::`, benign for expressions), with fuel
  `fbT t = 8 * #tokens + 30`. Excluded (recorded): `embeds` fields, raw brace groups and `fn(..)`
  types (`.raw`), `entry fn(..)` types, rights lists `rw+own`/`own@h`, suffix chains over a
  non-chain base (`[T; n] wrapping` reads `[T; n]` and leaves `wrapping`).

  Names print as `nameTok`, the token the lexer reads (`u32`, `bool`, `dma` are table words); the
  reader takes both. A path type's head is no type-head word (`typKopf`), as an atom.
-/
module
public import Grammatik.Parser.Round.RundlaufTyp.Teil1

public import Grammatik.Parser.Round.RundlaufTok.Teil4
public import Grammatik.Parser.Round.Statements.RundlaufAnw3
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic

@[expose] public section



namespace Gabbro.Grammatik.Parser

set_option maxRecDepth 100000

/-! ### Bare names -/

theorem nimmFolge_alle : ∀ (cs : List Char), cs.all istFolge = true → nimmFolge cs = (cs, []) := by
  intro cs h
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [nimmFolge, h.1, ite_true, ih h.2]

/-- A name-shaped text alone lexes to the one token the lexer reads for it. -/
theorem lex_name_allein (s : String) (h : nameForm s = true) :
    lex s = .ok [nameTok s, .ende] := by
  have hs : s = String.ofList s.toList := (String.ofList_toList).symm
  unfold lex
  unfold nameForm at h
  generalize hl : s.toList = l at h hs
  match l, h with
  | c :: cs, h =>
    simp only [Bool.and_eq_true] at h
    have hle := istAnfang_nicht_leer h.1
    have hz : istZiffer c = false := by
      cases hz : istZiffer c
      · rfl
      · have := istZiffer_nicht_anfang hz; simp_all
    have hlen : s.length = cs.length + 1 := by
      rw [← String.length_toList, hl]; rfl
    rw [hlen, scan.eq_7]
    · simp only [hle, hz, h.1, ite_true, Bool.false_eq_true, ite_false]
      rw [nimmFolge_alle cs h.2]
      simp only [scan, ← hs, nameTok]
      split <;> rfl
    · intro _ e _; exact istAnfang_ne h.1 '/' (by decide) e
    · intro _ e _; exact istAnfang_ne h.1 '/' (by decide) e
    · intro _ e _; exact istAnfang_ne h.1 '/' (by decide) e
    · intro _ e _; exact istAnfang_ne h.1 '/' (by decide) e
    · intro e; exact istAnfang_ne h.1 '"' (by decide) e

theorem rohToks_name (s : String) (h : nameForm s = true) : rohToks s = [nameTok s] := by
  unfold rohToks
  rw [lex_name_allein s h]
  cases hk : istSchluessel s <;> simp only [nameTok, hk, Bool.false_eq_true, ↓reduceIte, List.filter_cons_of_pos, not_false_eq_true, List.filter_cons_of_neg, List.filter_nil]

theorem nimmName_nameTok (s : String) (r : List Token) :
    nimmName (nameTok s :: r) = .ok (s, r) := by
  simp only [nimmName, nameText_nameTok]

/-! ### Types -/

/-- The words that open a type form of their own (never an atom). -/
def typKopf (a : String) : Bool :=
  strEq a "ptr" || strEq a "option" || strEq a "index" || strEq a "entry" || strEq a "fn" ||
    strEq a "string" || strEq a "dyn"

/-- One suffix of a type chain: `in lo .. hi` (`..<` when exclusive) or `wrapping`. -/
inductive TSuff
  | rng (lo hi : SExpr) (x : Bool)
  | wrp

def tsStep : STyp → TSuff → STyp
  | b, .rng lo hi x => .range b lo hi x
  | b, .wrp => .wrap b

/-- A chain: the base with its suffixes applied left to right. -/
def applyTS (b : STyp) : List TSuff → STyp
  | [] => b
  | s :: ss => applyTS (tsStep b s) ss

def tsToks : List TSuff → List Token
  | [] => []
  | .rng lo hi x :: ss =>
    [.wort "in"] ++ druckToks lo ++ [.zeichen (if x then "..<" else "..")] ++ druckToks hi ++ tsToks ss
  | .wrp :: ss => [.wort "wrapping"] ++ tsToks ss

theorem druckTyp_applyTS : ∀ (ss : List TSuff) (b : STyp),
    druckTyp (applyTS b ss) = druckTyp b ++ tsToks ss := by
  intro ss
  induction ss with
  | nil => intro b; simp only [applyTS, tsToks, List.append_nil]
  | cons s ss ih =>
    intro b
    cases s with
    | rng lo hi x => simp only [applyTS, tsStep, ih, druckTyp, List.append_assoc, List.cons_append, List.nil_append, tsToks]
    | wrp => simp only [applyTS, tsStep, ih, druckTyp, List.append_assoc, List.cons_append, List.nil_append, tsToks]

/-- The range bounds of a chain are printable. -/
def TsGut (ss : List TSuff) : Prop :=
  ∀ lo hi x, TSuff.rng lo hi x ∈ ss → gut lo = true ∧ gut hi = true

/-- The root of a chain: an atom that opens no type form, or a path of two or more segments. -/
inductive WurzelGut : STyp → Prop
  | atom (a : String) : typKopf a = false → WurzelGut (.atom a)
  | path (segs : List String) : 2 ≤ segs.length → typKopf (segs.headD "") = false →
      WurzelGut (.path segs)

/-- The printable types (see the header). -/
inductive TypGut : STyp → Prop
  | kette (root : STyp) (ss : List TSuff) : WurzelGut root → TsGut ss → TypGut (applyTS root ss)
  | ptr (r w : String) (t : STyp) : nameForm w = true → TypGut t → TypGut (.ptr r w t)
  | index (o : Bool) (t : String) : TypGut (.index o t)
  | array (t : STyp) (n : SExpr) : TypGut t → gut n = true → TypGut (.array t n)
  | str (e : SExpr) : gut e = true → TypGut (.str e)

/-- What may follow a type: no suffix word, no `::`, and benign for an expression in front. -/
def TypFolge (rest : List Token) : Prop :=
  (∀ r, rest ≠ .wort "in" :: r) ∧ (∀ r, rest ≠ .wort "wrapping" :: r) ∧
  (∀ r, rest ≠ .wort "embeds" :: r) ∧ (∀ r, rest ≠ .zeichen "::" :: r) ∧
  ruhig rest = true ∧ ruhigSuff rest = true ∧ ruhigGleit rest = true

/-- The fuel bound of a type. -/
def fbT (t : STyp) : Nat := 8 * (druckTyp t).length + 30

/-- The suffix loop stops before a type follow. -/
theorem parseTypNach_stop (F : Nat) (b : STyp) (rest : List Token) (h : TypFolge rest) :
    parseTypNach (F + 1) b rest = .ok (b, rest) := by
  obtain ⟨h1, h2, h3, -⟩ := h
  rcases rest with _ | ⟨t, r⟩
  · rfl
  · cases t with
    | wort s =>
      have n1 : s ≠ "in" := fun e => h1 r (by rw [e])
      have n2 : s ≠ "wrapping" := fun e => h2 r (by rw [e])
      have n3 : s ≠ "embeds" := fun e => h3 r (by rw [e])
      have e1 : strEq s "in" = false := by
        cases e : strEq s "in"
        · rfl
        · exact absurd ((strEq_eq _ _).mp e) n1
      have e2 : strEq s "wrapping" = false := by
        cases e : strEq s "wrapping"
        · rfl
        · exact absurd ((strEq_eq _ _).mp e) n2
      have e3 : strEq s "embeds" = false := by
        cases e : strEq s "embeds"
        · rfl
        · exact absurd ((strEq_eq _ _).mp e) n3
      simp only [parseTypNach, e1, Bool.false_eq_true, ↓reduceIte, e2, e3]
    | _ => rfl

theorem typFolge_ruhig {rest : List Token} (h : TypFolge rest) :
    ruhig rest = true ∧ ruhigSuff rest = true ∧ ruhigGleit rest = true := h.2.2.2.2

theorem tsToks_kopf (ss : List TSuff) (rest : List Token) (h : TypFolge rest) :
    ruhig (tsToks ss ++ rest) = true ∧ ruhigSuff (tsToks ss ++ rest) = true ∧
      ruhigGleit (tsToks ss ++ rest) = true := by
  cases ss with
  | nil => simpa [tsToks] using typFolge_ruhig h
  | cons s _ => cases s <;> exact ⟨rfl, rfl, rfl⟩

/-- The suffix loop over a chain's suffixes. -/
theorem parseTypNach_ts : ∀ (ss : List TSuff) (b : STyp) (rest : List Token) (F : Nat),
    TsGut ss → TypFolge rest → 8 * (tsToks ss).length + 31 ≤ F →
    parseTypNach F b (tsToks ss ++ rest) = .ok (applyTS b ss, rest) := by
  intro ss
  induction ss with
  | nil =>
    intro b rest F _ hr hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simpa [tsToks, applyTS] using parseTypNach_stop F' b rest hr
  | cons s ss ih =>
    intro b rest F hg hr hF
    have hg' : TsGut ss := fun lo hi x hm => hg lo hi x (List.mem_cons_of_mem _ hm)
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    cases s with
    | wrp =>
      simp only [tsToks, List.length_append, List.length_singleton] at hF
      simp only [tsToks, List.cons_append, List.nil_append, applyTS, tsStep]
      have e1 : strEq "wrapping" "in" = false := by decide
      have e2 : strEq "wrapping" "wrapping" = true := by decide
      simp only [parseTypNach, e1, e2, Bool.false_eq_true, ite_false, ite_true]
      exact ih _ rest F' hg' hr (by omega)
    | rng lo hi x =>
      obtain ⟨hlo, hhi⟩ := hg lo hi x (by simp only [List.mem_cons, true_or])
      simp only [tsToks, List.length_append, List.length_singleton] at hF
      have hT := ih (.range b lo hi x) rest F' hg' hr (by omega)
      obtain ⟨hr1, hr2, hr3⟩ := tsToks_kopf ss rest hr
      have hHi := parse_druck_tok hi (tsToks ss ++ rest) F' hhi hr1 hr2 hr3 (by simp only [fb]; omega)
      have hLo := parse_druck_tok lo
        (.zeichen (if x then "..<" else "..") :: (druckToks hi ++ (tsToks ss ++ rest))) F' hlo
        (by cases x <;> rfl) (by cases x <;> rfl) (by cases x <;> rfl) (by simp only [fb]; omega)
      simp only [tsToks, List.cons_append, List.nil_append, List.append_assoc, applyTS, tsStep]
      have e1 : strEq "in" "in" = true := by decide
      simp only [parseTypNach, e1, ite_true, hLo]
      cases x
      · have e3 : strEq ".." ".." = true := by decide
        have e4 : strEq ".." "..<" = false := by decide
        simp only [Bool.false_eq_true, ite_false, e3, e4, Bool.true_or, ite_true, hHi]
        exact hT
      · have e3 : strEq "..<" ".." = false := by decide
        have e4 : strEq "..<" "..<" = true := by decide
        simp only [ite_true, e3, e4, Bool.or_true, hHi]
        exact hT

theorem sammleSeg_stop2 (acc : List String) (rest : List Token)
    (hs : ∀ x, rest ≠ .zeichen "::" :: x) : sammleSegmente rest acc = (acc, rest) := by
  rcases rest with _ | ⟨t, r⟩
  · rfl
  · cases t with
    | zeichen s =>
      by_cases hs' : s = "::"
      · subst hs'; exact absurd rfl (hs r)
      · rcases r with _ | ⟨t2, r2⟩
        · simp only [sammleSegmente]
        · simp only [List.cons.injEq, Token.zeichen.injEq, hs', false_and, imp_self, implies_true, sammleSegmente]
    | _ => rfl

theorem sammleSeg_schritt (a : String) (R : List Token) (acc : List String) :
    sammleSegmente (.zeichen "::" :: nameTok a :: R) acc = sammleSegmente R (acc ++ [a]) := by
  simp only [sammleSegmente, nameText_nameTok]

/-- `sammleSegmente` reads a printed path tail and stops before a non-`::` follow. -/
theorem sammleSeg_pfad : ∀ (segs : List String) (acc : List String) (rest : List Token),
    segs ≠ [] → (∀ r, rest ≠ .zeichen "::" :: r) →
    sammleSegmente (.zeichen "::" :: (pfadToks segs ++ rest)) acc = (acc ++ segs, rest) := by
  intro segs
  induction segs with
  | nil => intro _ _ h; exact absurd rfl h
  | cons a segs ih =>
    intro acc rest _ hr
    cases segs with
    | nil =>
      show sammleSegmente (.zeichen "::" :: nameTok a :: rest) acc = (acc ++ [a], rest)
      rw [sammleSeg_schritt]
      exact sammleSeg_stop2 _ rest hr
    | cons b segs' =>
      show sammleSegmente (.zeichen "::" :: nameTok a :: .zeichen "::" ::
        (pfadToks (b :: segs') ++ rest)) acc = _
      rw [sammleSeg_schritt, ih (acc ++ [a]) rest (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) hr]
      simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- `parseTyp` on an identifier head that does not open `string max`: the path arm. -/
theorem parseTyp_ident (F : Nat) (a : String) (rest : List Token)
    (h : a ≠ "string" ∨ ∀ r', rest ≠ .wort "max" :: r') :
    parseTyp (F + 1) (.ident a :: rest) = match nimmPfad (.ident a :: rest) with
      | .error e => .error e
      | .ok (segs, r) => match segs with
        | [] => .error "type expected"
        | [x] => parseTypNach F (.atom x) r
        | _ => parseTypNach F (.path segs) r := by
  rw [parseTyp.eq_def]
  simp only
  split
  next _ _ _ heq => simp only [List.cons.injEq, reduceCtorEq, false_and] at heq
  next _ _ heq =>
    simp only [List.cons.injEq, Token.ident.injEq] at heq
    rcases h with h | h
    · exact absurd heq.1 h
    · exact absurd heq.2 (h _)
  next _ _ _ _ heq => simp only [List.cons.injEq, Token.ident.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq; rfl
  all_goals first
    | exact absurd rfl
        (‹∀ (a_1 : String) (tail : List Token), Token.ident a :: rest = Token.ident a_1 :: tail → False›
          a rest)
    | (rename_i heq; simp only [List.cons.injEq, reduceCtorEq, false_and] at heq; done)

end Gabbro.Grammatik.Parser
