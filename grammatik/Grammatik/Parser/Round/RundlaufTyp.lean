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
import Grammatik.Parser.Round.RundlaufTok
import Grammatik.Parser.Round.RundlaufAnw3

namespace Gabbro.Grammatik.Parser

set_option maxRecDepth 100000

/-! ### Rendered text, token by token -/

theorem zeigeTok_spell (t : Token) (h : TokGut t) : zeigeTok t = String.ofList (spell t) := by
  cases t with
  | ident s => simp [zeigeTok, spell, String.ofList_toList]
  | wort s => simp [zeigeTok, spell, String.ofList_toList]
  | num n => rfl
  | float s => simp [zeigeTok, spell, String.ofList_toList]
  | text s =>
    simp only [zeigeTok, spell]
    rw [show ('"' :: (s.toList ++ ['"'])) = ['"'] ++ s.toList ++ ['"'] by simp,
      String.ofList_append, String.ofList_append, String.ofList_toList]
  | zeichen s => simp [zeigeTok, spell, String.ofList_toList]
  | doku _ => exact absurd h id
  | ende => exact absurd h id

theorem renderText_nil : renderText [] = "" := rfl

theorem renderText_cons (t : Token) (ts : List Token) (h : TokGut t) :
    renderText (t :: ts) = zeigeTok t ++ " " ++ renderText ts := by
  unfold renderText
  rw [zeigeTok_spell t h]
  simp only [render]
  rw [show spell t ++ ' ' :: render ts = spell t ++ [' '] ++ render ts by simp,
    String.ofList_append, String.ofList_append]

/-- The re-lexed rendered text is the token list. -/
theorem filter_ende : ∀ (ts : List Token), (∀ t ∈ ts, TokGut t) →
    (ts ++ [Token.ende]).filter (fun t => match t with | .ende => false | _ => true) = ts := by
  intro ts h
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    have ht := h t (by simp)
    have ih' := ih (fun x hx => h x (by simp [hx]))
    cases t <;> simp_all [TokGut]

theorem rohToks_render (ts : List Token) (h : ∀ t ∈ ts, TokGut t) :
    rohToks (renderText ts) = ts := by
  unfold rohToks
  rw [lex_render ts h]
  exact filter_ende ts h

/-! ### The collectors return the rendered text -/

theorem traverseRest_roh : ∀ (ts rest : List Token),
    (∀ t ∈ ts, TokGut t ∧ t ≠ .zeichen "{" ∧ t ≠ .wort "invariant") →
    traverseRest (ts ++ .zeichen "{" :: rest) = .ok (renderText ts, .zeichen "{" :: rest) := by
  intro ts rest
  induction ts with
  | nil => intro _; simp [traverseRest, renderText_nil]
  | cons t ts ih =>
    intro h
    obtain ⟨hg, h1, h2⟩ := h t (by simp)
    have ih' := ih (fun x hx => h x (by simp [hx]))
    rw [renderText_cons t ts hg]
    cases t with
    | wort s =>
      have hs : strEq s "invariant" = false := by
        cases e : strEq s "invariant"
        · rfl
        · exact absurd (by rw [(strEq_eq _ _).mp e]) h2
      simp [traverseRest, hs, ih', zeigeTok]
    | zeichen s =>
      have hs : s ≠ "{" := fun e => h1 (by rw [e])
      simp [traverseRest, hs, ih', zeigeTok]
    | _ => simp [traverseRest, ih']

theorem schleifenKopf_schritt (t : Token) (rest : List Token) (n : Nat)
    (h1 : t ≠ .zeichen "{") (h2 : ∀ s r, t = .wort s → rest ≠ .zeichen "{" :: r) :
    schleifenKopf (t :: rest) (n + 1) = match schleifenKopf rest n with
      | .ok (h, r) => .ok (zeigeTok t ++ " " ++ h, r)
      | .error e => .error e := by
  rw [schleifenKopf.eq_5 t rest n (fun s r e1 e2 => h2 s r e1 e2) h1]
  rfl

theorem schleifenKopf_roh : ∀ (ts rest : List Token) (n : Nat),
    (∀ t ∈ ts, TokGut t ∧ t ≠ .zeichen "{" ∧ t ≠ .wort "effects") → ts.length < n →
    schleifenKopf (ts ++ .zeichen "{" :: rest) n = .ok (renderText ts, .zeichen "{" :: rest) := by
  intro ts rest
  induction ts with
  | nil =>
    intro n _ hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
    simp [schleifenKopf, renderText_nil]
  | cons t ts ih =>
    intro n h hn
    obtain ⟨hg, h1, h2⟩ := h t (by simp)
    have ih' := ih (n - 1) (fun x hx => h x (by simp [hx])) (by simp at hn; omega)
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
    simp only [Nat.add_sub_cancel] at ih'
    rw [renderText_cons t ts hg]
    cases ts with
    | nil =>
      cases t with
      | wort s =>
        have hs : strEq s "effects" = false := by
          cases e : strEq s "effects"
          · rfl
          · exact absurd (by rw [(strEq_eq _ _).mp e]) h2
        simp [schleifenKopf, hs, zeigeTok, renderText_nil]
      | _ =>
        simp only [List.nil_append, List.cons_append] at ih' ⊢
        rw [schleifenKopf_schritt _ _ _ h1 (by intro s r e; cases e), ih']
    | cons t2 ts2 =>
      have h3 : t2 ≠ .zeichen "{" := (h t2 (by simp)).2.1
      simp only [List.cons_append] at ih' ⊢
      rw [schleifenKopf_schritt _ _ _ h1 (by intro s r _ e; injection e with e1; exact h3 e1), ih']

theorem nimmBisWort_roh : ∀ (w : String) (ts rest : List Token),
    (∀ t ∈ ts, TokGut t ∧ t ≠ .zeichen "{" ∧ t ≠ .zeichen "}" ∧ t ≠ .wort w) →
    nimmBisWort w (ts ++ .wort w :: rest) 0 = .ok (renderText ts, .wort w :: rest) := by
  intro w ts rest
  induction ts with
  | nil => intro _; simp [nimmBisWort, strEq_self, renderText_nil]
  | cons t ts ih =>
    intro h
    obtain ⟨hg, h1, h2, h3⟩ := h t (by simp)
    have ih' := ih (fun x hx => h x (by simp [hx]))
    rw [renderText_cons t ts hg]
    cases t with
    | wort s =>
      have hs : strEq s w = false := by
        cases e : strEq s w
        · rfl
        · exact absurd (by rw [(strEq_eq _ _).mp e]) h3
      simp [nimmBisWort, hs, ih', zeigeTok]
    | zeichen s =>
      have hs1 : s ≠ "{" := fun e => h1 (by rw [e])
      have hs2 : s ≠ "}" := fun e => h2 (by rw [e])
      simp [nimmBisWort, hs1, hs2, ih', zeigeTok]
    | _ => simp [nimmBisWort, ih']

theorem nimmBisZeichen_roh : ∀ (z : String) (ts rest : List Token),
    (∀ t ∈ ts, TokGut t ∧ t ≠ .zeichen "{" ∧ t ≠ .zeichen "}" ∧ t ≠ .zeichen z) →
    nimmBisZeichen z (ts ++ .zeichen z :: rest) 0 = .ok (renderText ts, .zeichen z :: rest) := by
  intro z ts rest
  induction ts with
  | nil => intro _; simp [nimmBisZeichen, strEq_self, renderText_nil]
  | cons t ts ih =>
    intro h
    obtain ⟨hg, h1, h2, h3⟩ := h t (by simp)
    have ih' := ih (fun x hx => h x (by simp [hx]))
    rw [renderText_cons t ts hg]
    cases t with
    | zeichen s =>
      have hs : strEq s z = false := by
        cases e : strEq s z
        · rfl
        · exact absurd (by rw [(strEq_eq _ _).mp e]) h3
      have hs1 : strEq s "{" = false := by
        cases e : strEq s "{"
        · rfl
        · exact absurd (by rw [(strEq_eq _ _).mp e]) h1
      have hs2 : strEq s "}" = false := by
        cases e : strEq s "}"
        · rfl
        · exact absurd (by rw [(strEq_eq _ _).mp e]) h2
      simp [nimmBisZeichen, hs, hs1, hs2, ih', zeigeTok]
    | _ => simp [nimmBisZeichen, ih']

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
  cases hk : istSchluessel s <;> simp [nameTok, hk]

theorem nimmName_nameTok (s : String) (r : List Token) :
    nimmName (nameTok s :: r) = .ok (s, r) := by
  simp [nimmName, nameText_nameTok]

/-! ### Types -/

/-- The words that open a type form of their own (never an atom). -/
def typKopf (a : String) : Bool :=
  strEq a "ptr" || strEq a "option" || strEq a "index" || strEq a "entry" || strEq a "fn" ||
    strEq a "string"

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
  | nil => intro b; simp [applyTS, tsToks]
  | cons s ss ih =>
    intro b
    cases s with
    | rng lo hi x => simp [applyTS, tsStep, ih, druckTyp, tsToks, List.append_assoc]
    | wrp => simp [applyTS, tsStep, ih, druckTyp, tsToks, List.append_assoc]

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
      simp [parseTypNach, e1, e2, e3]
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
      obtain ⟨hlo, hhi⟩ := hg lo hi x (by simp)
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
        · simp [sammleSegmente, hs']
        · simp [sammleSegmente, hs']
    | _ => rfl

theorem sammleSeg_schritt (a : String) (R : List Token) (acc : List String) :
    sammleSegmente (.zeichen "::" :: nameTok a :: R) acc = sammleSegmente R (acc ++ [a]) := by
  simp [sammleSegmente]

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
      rw [sammleSeg_schritt, ih (acc ++ [a]) rest (by simp) hr]
      simp

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
  next _ _ _ heq => simp at heq
  next _ _ heq =>
    simp at heq
    rcases h with h | h
    · exact absurd heq.1 h
    · exact absurd heq.2 (h _)
  next _ _ _ _ heq => simp at heq; obtain ⟨rfl, rfl⟩ := heq; rfl
  next _ _ heq => simp at heq
  next _ _ heq => simp at heq
  next _ _ _ x _ _ => exact absurd rfl (x a rest)

/-- The root of a chain read by `parseTyp`, handing its rest to the suffix loop. -/
theorem parseTyp_wurzel (r : STyp) (hr : WurzelGut r) (rest : List Token) (F : Nat)
    (hs : ∀ x, rest ≠ .zeichen "::" :: x) :
    parseTyp (F + 1) (druckTyp r ++ rest) = parseTypNach F r rest := by
  cases hr with
  | atom a hk =>
    simp only [typKopf, Bool.or_eq_false_iff] at hk
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hk
    have hseg := sammleSeg_stop2 [a] rest hs
    simp only [druckTyp, nameTok, List.singleton_append]
    split
    · simp [parseTyp, h1, h2, h3, h4, h5, nimmPfad, hseg]
    · have hne : a ≠ "string" := fun e => by rw [e] at h6; exact absurd h6 (by decide)
      rw [parseTyp_ident F a rest (Or.inl hne)]
      simp [nimmPfad, hseg]
  | path segs h2 hk =>
    match segs, h2, hk with
    | a :: b :: cs, _, hk =>
      simp only [List.headD, typKopf, Bool.or_eq_false_iff] at hk
      obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hk
      have hseg := sammleSeg_pfad (b :: cs) [a] rest (by simp) hs
      show parseTyp (F + 1) (nameTok a :: .zeichen "::" :: (pfadToks (b :: cs) ++ rest)) = _
      unfold nameTok
      split
      · simp [parseTyp, h1, h2, h3, h4, h5, nimmPfad, hseg]
      · rw [parseTyp_ident F a _ (Or.inr (by intro r' e; cases e))]
        simp only [nimmPfad, nameText_ident, hseg]
        rfl

/-- A single right before `>`. -/
theorem parseRechte_name (F : Nat) (w : String) (r : List Token) :
    parseRechte (F + 1) (nameTok w :: .zeichen ">" :: r) = .ok (w, .zeichen ">" :: r) := by
  have e1 : (">" == "@") = false := by decide
  have e2 : (">" == "+") = false := by decide
  simp [parseRechte, nimmName, nameText_nameTok, bind, Except.bind, pure, Except.pure]

/-- **Types read back.** Every printable type parses back before a type follow. -/
theorem parse_druckTyp : ∀ (t : STyp), TypGut t → ∀ (rest : List Token) (F : Nat), TypFolge rest →
    fbT t ≤ F → parseTyp F (druckTyp t ++ rest) = .ok (t, rest) := by
  intro t ht
  induction ht with
  | kette root ss hw hs =>
    intro rest F hr hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp only [fbT] at hF; omega⟩
    rw [druckTyp_applyTS, List.append_assoc]
    have hsr : ∀ x, tsToks ss ++ rest ≠ .zeichen "::" :: x := by
      intro x e
      cases ss with
      | nil => exact hr.2.2.2.1 x (by simpa [tsToks] using e)
      | cons s _ => cases s <;> simp [tsToks] at e
    rw [parseTyp_wurzel root hw _ F' hsr]
    apply parseTypNach_ts ss root rest F' hs hr
    have hl : 1 ≤ (druckTyp root).length := by
      cases hw with
      | atom a _ => simp [druckTyp]
      | path segs h2 _ =>
        match segs, h2 with
        | a :: b :: cs, _ => simp [druckTyp, pfadToks]
    simp only [fbT, druckTyp_applyTS, List.length_append] at hF
    omega
  | ptr r w t hw ht ih =>
    intro rest F hr hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp only [fbT] at hF; omega⟩
    simp only [fbT, druckTyp, rohToks_name w hw, List.length_append, List.length_cons,
      List.length_nil, List.length_singleton] at hF
    simp only [druckTyp, rohToks_name w hw, List.cons_append, List.nil_append, List.append_assoc,
      List.singleton_append]
    have hT := ih rest F' hr (by simp only [fbT]; omega)
    obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
    have hR := parseRechte_name F'' w (druckTyp t ++ rest)
    have hp : strEq "ptr" "ptr" = true := by decide
    rw [parseTyp.eq_def]
    simp only [hp, ite_true, fordereZeichen, strEq_self, nimmName, nameText_nameTok, hR, hT]

  | index o t =>
    intro rest F hr hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp only [fbT] at hF; omega⟩
    cases o
    · have e1 : strEq "index" "ptr" = false := by decide
      have e2 : strEq "index" "option" = false := by decide
      simp [druckTyp, parseTyp, e1, e2, nimmWort, nimmName, strEq_self]
    · have e1 : strEq "option" "ptr" = false := by decide
      simp [druckTyp, parseTyp, e1, nimmWort, nimmName, strEq_self]
  | array t n ht hn ih =>
    intro rest F hr hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp only [fbT] at hF; omega⟩
    simp only [fbT, druckTyp, List.length_append, List.length_cons, List.length_nil,
      List.length_singleton] at hF
    have hfs : TypFolge (.zeichen ";" :: (druckToks n ++ (.zeichen "]" :: rest))) :=
      ⟨(by intro r e; simp at e), (by intro r e; simp at e), (by intro r e; simp at e),
        (by intro r e; simp at e), rfl, rfl, rfl⟩
    have hT := ih _ F' hfs (by simp only [fbT]; omega)
    have hN := parse_druck_tok n (.zeichen "]" :: rest) F' hn rfl rfl rfl (by simp only [fb]; omega)
    simp only [druckTyp, List.cons_append, List.nil_append, List.append_assoc,
      List.singleton_append] at hT ⊢
    simp [parseTyp, hT, fordereZeichen, strEq_self, hN]
  | str e he =>
    intro rest F hr hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp only [fbT] at hF; omega⟩
    obtain ⟨hr1, hr2, hr3⟩ := typFolge_ruhig hr
    simp only [fbT, druckTyp, List.length_append, List.length_cons, List.length_nil] at hF
    have hE := parse_druck_tok e rest F' he hr1 hr2 hr3 (by simp only [fb]; omega)
    simp [druckTyp, parseTyp, hE]

/-! ### Expressions and places by name (used by the predicate and statement readers) -/

/-- The expression legs before a follow, by name. -/
theorem ausdruck (e : SExpr) (hg : gut e = true) (rest : List Token) (F : Nat)
    (h1 : ruhig rest = true) (h2 : ruhigSuff rest = true) (h3 : ruhigGleit rest = true)
    (hF : 6 * (druckToks e).length + 34 ≤ F) : parseOr F (druckToks e ++ rest) = .ok (e, rest) :=
  parse_druck_tok e rest F hg h1 h2 h3 (by simp only [fb]; omega)

/-- The payload legs of a place's suffix chain, from printability. -/
theorem suffLegs_gut (suff : List SuffFrag) (h : suffGut suff = true) : SuffLegs suff := by
  intro i hi
  exact legs_tok i (suff_idx_mem suff i hi h).2

/-- Places through `parseOrt` from printability. -/
theorem ortP (p : SExpr) (hp : gutPlatz p = true) (rest : List Token) (F : Nat)
    (hr : ruhigSuff rest = true) (hF : 6 * (druckToks p).length + 30 ≤ F) :
    parseOrt F (druckToks p ++ rest) = .ok (p, rest) := by
  obtain ⟨a, suff, rfl, hka, hgs, _⟩ := zerlege (groesse p) p (Nat.le_refl _) hp
  apply ortM a suff rest F hka (suffLegs_gut suff hgs) hr
  rw [druckToks_applySuff] at hF
  simp only [druckToks, List.length_append, List.length_singleton] at hF
  omega

/-- Places through `parseKopf` (the statement head of an assignment or a publication). -/
theorem kopfP (p : SExpr) (hp : gutPlatz p = true) (rest : List Token) (F : Nat)
    (hr : ruhigSuff rest = true) (hF : 6 * (druckToks p).length + 30 ≤ F) :
    parseKopf F (druckToks p ++ rest) = .ok (p, rest) := by
  obtain ⟨a, suff, rfl, hka, hgs, _⟩ := zerlege (groesse p) p (Nat.le_refl _) hp
  rw [druckToks_applySuff] at hF ⊢
  simp only [druckToks, List.length_append, List.length_singleton] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [druckToks, List.cons_append, List.nil_append, List.append_assoc, parseKopf, nameText_nameTok, nameText_ident, nameText_wort, nameText_zeichen, nameText_num, nameText_ende]
  simp only [sammleSeg_suffToks, hr]
  have hmiss : ∀ (R : List Token), suffToks suff ++ rest ≠ .zeichen "(" :: R := by
    intro R hcon
    exact suffToks_nopar suff rest R hr hcon
  simp only [hmiss]
  exact suffM suff (.variable a) rest F' (suffLegs_gut suff hgs) hr (by omega)

/-- A place prints with an identifier head. -/
theorem platz_kopf (p : SExpr) (hp : gutPlatz p = true) :
    ∃ a ts, druckToks p = nameTok a :: ts ∧ istKopfWort a = false :=
  platz_kopf_aux (groesse p) p (Nat.le_refl _) hp

end Gabbro.Grammatik.Parser
