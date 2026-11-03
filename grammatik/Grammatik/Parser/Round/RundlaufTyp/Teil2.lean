module

public import Grammatik.Parser.Round.RundlaufTok.Teil4
public import Grammatik.Parser.Round.Statements.RundlaufAnw3
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Round.RundlaufTyp.Teil1
public import Grammatik.Parser.Round.RundlaufTyp.Teil1a

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000

/-- The root of a chain read by `parseTyp`, handing its rest to the suffix loop. -/
theorem parseTyp_wurzel (r : STyp) (hr : WurzelGut r) (rest : List Token) (F : Nat)
    (hs : ∀ x, rest ≠ .zeichen "::" :: x) :
    parseTyp (F + 1) (druckTyp r ++ rest) = parseTypNach F r rest := by
  cases hr with
  | atom a hk =>
    simp only [typKopf, Bool.or_eq_false_iff] at hk
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hk
    have hseg := sammleSeg_stop2 [a] rest hs
    simp only [druckTyp, nameTok, List.singleton_append]
    split
    · simp only [parseTyp, h7, h1, Bool.false_eq_true, ↓reduceIte, h2, h3, h4, h5, nimmPfad, nameText_wort, hseg]
    · have hne : a ≠ "string" := fun e => by rw [e] at h6; exact absurd h6 (by decide)
      rw [parseTyp_ident F a rest (Or.inl hne)]
      simp only [nimmPfad, nameText_ident, hseg]
  | path segs h2 hk =>
    match segs, h2, hk with
    | a :: b :: cs, _, hk =>
      simp only [List.headD, typKopf, Bool.or_eq_false_iff] at hk
      obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hk
      have hseg := sammleSeg_pfad (b :: cs) [a] rest (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) hs
      show parseTyp (F + 1) (nameTok a :: .zeichen "::" :: (pfadToks (b :: cs) ++ rest)) = _
      unfold nameTok
      split
      · simp only [parseTyp, h7, h1, Bool.false_eq_true, ↓reduceIte, h2, h3, h4, h5, nimmPfad, nameText_wort, hseg,
  List.cons_append, List.nil_append]
      · rw [parseTyp_ident F a _ (Or.inr (by intro r' e; cases e))]
        simp only [nimmPfad, nameText_ident, hseg]
        rfl

/-- A single right before `>`. -/
theorem parseRechte_name (F : Nat) (w : String) (r : List Token) :
    parseRechte (F + 1) (nameTok w :: .zeichen ">" :: r) = .ok (w, .zeichen ">" :: r) := by
  have e1 : (">" == "@") = false := by decide
  have e2 : (">" == "+") = false := by decide
  simp only [parseRechte, bind, Except.bind, nimmName, nameText_nameTok, List.cons.injEq, Token.zeichen.injEq,
  String.reduceEq, false_and, imp_self, implies_true, pure, Except.pure]

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
      | cons s _ => cases s <;> simp only [tsToks, List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq, reduceCtorEq, false_and] at e
    rw [parseTyp_wurzel root hw _ F' hsr]
    apply parseTypNach_ts ss root rest F' hs hr
    have hl : 1 ≤ (druckTyp root).length := by
      cases hw with
      | atom a _ => simp only [druckTyp, List.length_cons, List.length_nil, Nat.zero_add, Std.le_refl]
      | path segs h2 _ =>
        match segs, h2 with
        | a :: b :: cs, _ => simp only [druckTyp, pfadToks, List.cons_append, List.nil_append, List.length_cons, Nat.le_add_left]
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
    have hdyn : strEq "ptr" "dyn" = false := by decide
    rw [parseTyp.eq_def]
    simp only [hdyn, Bool.false_eq_true, ite_false, hp, ite_true, fordereZeichen, strEq_self, nimmName, nameText_nameTok, hR, hT]

  | index o t =>
    intro rest F hr hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp only [fbT] at hF; omega⟩
    cases o
    · have e1 : strEq "index" "ptr" = false := by decide
      have e2 : strEq "index" "option" = false := by decide
      simp only [parseTyp, druckTyp, (by decide : strEq "index" "dyn" = false), Bool.false_eq_true, ↓reduceIte, List.nil_append, List.cons_append, e1, e2,
  strEq_self, nimmWort, nimmName, nameText_nameTok]
    · have e1 : strEq "option" "ptr" = false := by decide
      simp only [parseTyp, druckTyp, (by decide : strEq "option" "dyn" = false), ↓reduceIte, List.cons_append, List.nil_append, e1, Bool.false_eq_true,
  strEq_self, nimmWort, nimmName, nameText_nameTok]
  | array t n ht hn ih =>
    intro rest F hr hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp only [fbT] at hF; omega⟩
    simp only [fbT, druckTyp, List.length_append, List.length_cons, List.length_nil,
      List.length_singleton] at hF
    have hfs : TypFolge (.zeichen ";" :: (druckToks n ++ (.zeichen "]" :: rest))) :=
      ⟨(by intro r e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e), (by intro r e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e), (by intro r e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e),
        (by intro r e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e), rfl, rfl, rfl⟩
    have hT := ih _ F' hfs (by simp only [fbT]; omega)
    have hN := parse_druck_tok n (.zeichen "]" :: rest) F' hn rfl rfl rfl (by simp only [fb]; omega)
    simp only [druckTyp, List.cons_append, List.nil_append, List.append_assoc,
      List.singleton_append] at hT ⊢
    simp only [parseTyp, hT, fordereZeichen, strEq_self, ↓reduceIte, hN]
  | str e he =>
    intro rest F hr hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp only [fbT] at hF; omega⟩
    obtain ⟨hr1, hr2, hr3⟩ := typFolge_ruhig hr
    simp only [fbT, druckTyp, List.length_append, List.length_cons, List.length_nil] at hF
    have hE := parse_druck_tok e rest F' he hr1 hr2 hr3 (by simp only [fb]; omega)
    simp only [parseTyp, druckTyp, List.cons_append, List.nil_append, hE]

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
  simp only [rufKopf_ohne, suffToks_nogeneric suff rest hr, hmiss]
  exact suffM suff (.variable a) rest F' (suffLegs_gut suff hgs) hr (by omega)

/-- A place prints with an identifier head. -/
theorem platz_kopf (p : SExpr) (hp : gutPlatz p = true) :
    ∃ a ts, druckToks p = nameTok a :: ts ∧ istKopfWort a = false :=
  platz_kopf_aux (groesse p) p (Nat.le_refl _) hp

end Gabbro.Grammatik.Parser
