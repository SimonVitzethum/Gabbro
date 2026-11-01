module

public import Grammatik.Parser.Round.RundlaufTok.Teil4
public import Grammatik.Parser.Round.RundlaufAnw3
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic

@[expose] public section



namespace Gabbro.Grammatik.Parser

set_option maxRecDepth 100000

/-! ### Rendered text, token by token -/

theorem zeigeTok_spell (t : Token) (h : TokGut t) : zeigeTok t = String.ofList (spell t) := by
  cases t with
  | ident s => simp only [zeigeTok, spell, String.ofList_toList]
  | wort s => simp only [zeigeTok, spell, String.ofList_toList]
  | num n => rfl
  | float s => simp only [zeigeTok, spell, String.ofList_toList]
  | text s =>
    simp only [zeigeTok, spell]
    rw [show ('"' :: (s.toList ++ ['"'])) = ['"'] ++ s.toList ++ ['"'] by simp only [↓Char.isValue, List.cons_append, List.nil_append],
      String.ofList_append, String.ofList_append, String.ofList_toList]
  | zeichen s => simp only [zeigeTok, spell, String.ofList_toList]
  | doku _ => exact absurd h id
  | ende => exact absurd h id

theorem renderText_nil : renderText [] = "" := by rfl

theorem renderText_cons (t : Token) (ts : List Token) (h : TokGut t) :
    renderText (t :: ts) = zeigeTok t ++ " " ++ renderText ts := by
  unfold renderText
  rw [zeigeTok_spell t h]
  simp only [render]
  rw [show spell t ++ ' ' :: render ts = spell t ++ [' '] ++ render ts by simp only [↓Char.isValue, List.append_assoc, List.cons_append, List.nil_append],
    String.ofList_append, String.ofList_append]

/-- The re-lexed rendered text is the token list. -/
theorem filter_ende : ∀ (ts : List Token), (∀ t ∈ ts, TokGut t) →
    (ts ++ [Token.ende]).filter (fun t => match t with | .ende => false | _ => true) = ts := by
  intro ts h
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    have ht := h t (by simp only [List.mem_cons, true_or])
    have ih' := ih (fun x hx => h x (by simp only [List.mem_cons, hx, or_true]))
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
  | nil => intro _; simp only [List.nil_append, traverseRest, renderText_nil]
  | cons t ts ih =>
    intro h
    obtain ⟨hg, h1, h2⟩ := h t (by simp only [List.mem_cons, true_or])
    have ih' := ih (fun x hx => h x (by simp only [List.mem_cons, hx, or_true]))
    rw [renderText_cons t ts hg]
    cases t with
    | wort s =>
      have hs : strEq s "invariant" = false := by
        cases e : strEq s "invariant"
        · rfl
        · exact absurd (by rw [(strEq_eq _ _).mp e]) h2
      simp only [List.cons_append, traverseRest, hs, Bool.false_eq_true, ↓reduceIte, ih', zeigeTok]
    | zeichen s =>
      have hs : s ≠ "{" := fun e => h1 (by rw [e])
      simp only [List.cons_append, traverseRest, ih', zeigeTok]
    | _ => simp only [List.cons_append, traverseRest, ih']

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
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [List.length_nil] at hn; omega⟩
    simp only [List.nil_append, schleifenKopf, renderText_nil]
  | cons t ts ih =>
    intro n h hn
    obtain ⟨hg, h1, h2⟩ := h t (by simp only [List.mem_cons, true_or])
    have ih' := ih (n - 1) (fun x hx => h x (by simp only [List.mem_cons, hx, or_true])) (by simp only [List.length_cons] at hn; omega)
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [List.length_cons] at hn; omega⟩
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
        simp only [List.cons_append, List.nil_append, schleifenKopf, hs, Bool.false_eq_true, ↓reduceIte, zeigeTok,
  renderText_nil, String.append_empty]
      | _ =>
        simp only [List.nil_append, List.cons_append] at ih' ⊢
        rw [schleifenKopf_schritt _ _ _ h1 (by intro s r e; cases e), ih']
    | cons t2 ts2 =>
      have h3 : t2 ≠ .zeichen "{" := (h t2 (by simp only [List.mem_cons, true_or, or_true])).2.1
      simp only [List.cons_append] at ih' ⊢
      rw [schleifenKopf_schritt _ _ _ h1 (by intro s r _ e; injection e with e1; exact h3 e1), ih']

theorem nimmBisWort_roh : ∀ (w : String) (ts rest : List Token),
    (∀ t ∈ ts, TokGut t ∧ t ≠ .zeichen "{" ∧ t ≠ .zeichen "}" ∧ t ≠ .wort w) →
    nimmBisWort w (ts ++ .wort w :: rest) 0 = .ok (renderText ts, .wort w :: rest) := by
  intro w ts rest
  induction ts with
  | nil => intro _; simp only [List.nil_append, nimmBisWort, strEq_self, BEq.rfl, Bool.and_self, ↓reduceIte, renderText_nil]
  | cons t ts ih =>
    intro h
    obtain ⟨hg, h1, h2, h3⟩ := h t (by simp only [List.mem_cons, true_or])
    have ih' := ih (fun x hx => h x (by simp only [List.mem_cons, hx, or_true]))
    rw [renderText_cons t ts hg]
    cases t with
    | wort s =>
      have hs : strEq s w = false := by
        cases e : strEq s w
        · rfl
        · exact absurd (by rw [(strEq_eq _ _).mp e]) h3
      simp only [List.cons_append, nimmBisWort, hs, BEq.rfl, Bool.and_true, Bool.false_eq_true, ↓reduceIte, ih',
  zeigeTok]
    | zeichen s =>
      have hs1 : s ≠ "{" := fun e => h1 (by rw [e])
      have hs2 : s ≠ "}" := fun e => h2 (by rw [e])
      simp only [List.cons_append, nimmBisWort, ih', zeigeTok]
    | _ => simp only [List.cons_append, nimmBisWort, ih']

theorem nimmBisZeichen_roh : ∀ (z : String) (ts rest : List Token),
    (∀ t ∈ ts, TokGut t ∧ t ≠ .zeichen "{" ∧ t ≠ .zeichen "}" ∧ t ≠ .zeichen z) →
    nimmBisZeichen z (ts ++ .zeichen z :: rest) 0 = .ok (renderText ts, .zeichen z :: rest) := by
  intro z ts rest
  induction ts with
  | nil => intro _; simp only [List.nil_append, nimmBisZeichen, BEq.rfl, strEq_self, Bool.and_self, ↓reduceIte, renderText_nil]
  | cons t ts ih =>
    intro h
    obtain ⟨hg, h1, h2, h3⟩ := h t (by simp only [List.mem_cons, true_or])
    have ih' := ih (fun x hx => h x (by simp only [List.mem_cons, hx, or_true]))
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
      simp only [List.cons_append, nimmBisZeichen, BEq.rfl, hs, Bool.and_false, Bool.false_eq_true, ↓reduceIte, hs1,
  hs2, ih', zeigeTok]
    | _ => simp only [List.cons_append, nimmBisZeichen, ih']

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
  next _ _ heq => simp only [List.cons.injEq, reduceCtorEq, false_and] at heq
  next _ _ heq => simp only [List.cons.injEq, reduceCtorEq, false_and] at heq
  next _ _ _ x _ _ => exact absurd rfl (x a rest)

/-- The root of a chain read by `parseTyp`, handing its rest to the suffix loop. -/
end Gabbro.Grammatik.Parser
