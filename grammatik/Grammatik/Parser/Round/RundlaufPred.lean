/-
  File:      Grammatik/Parser/Round/RundlaufPred.lean
  Subject:   Layer L2c, part one: the predicate reader (`parsePred`) and the predicate lists over the
             printed expressions, and `::` paths printed as text.

  `pred_druck`: every printable expression (`gut`) reads back through `parsePred` -- the reader of
  contracts (`requires`/`ensures`), invariants, `where` predicates and place lists -- before a
  predicate follow (`PredFolge`: benign for expressions, no `=>`, no `in`, no `reaches`). The
  printed tree goes through `parsePredNot` (a `!` prefix is taken there, the operand read by
  `parsePredAtom`) and `parsePredAtom` (the comparison level, `parseCmp`). Predicate-only forms
  (`forall`, `exists`, `in`, `reaches`, `=>`: the `ext` trees) are outside `gut`; the quantifiers,
  `=>` and `&&`/`||`/`!` over them read back in `RundlaufQuant` (`pred_voll`).

  `lex_pfad`: a `::` path of name-shaped words, written without spaces
  (`String.intercalate "::"`), lexes to its path tokens (`pfadToks`); so `rohToks` of a path text is
  the path, and the printers that re-lex a path (`module`, `concurrent`, `start`, call heads)
  print it.
-/
import Grammatik.Parser.Round.RundlaufTyp
import Grammatik.Parser.Print.Item

namespace Gabbro.Grammatik.Parser

set_option maxRecDepth 100000

/-! ### A parenthesised expression up to the comparison level -/

theorem cmp_aus_unary (m : Nat) (x : SExpr) (T rest : List Token) (hr : ruhig rest = true)
    (hU : ∀ G, m + 2 ≤ G → parseUnary G (T ++ rest) = .ok (x, rest)) :
    ∀ G, m + 6 ≤ G → parseCmp G (T ++ rest) = .ok (x, rest) := by
  have hM : ∀ G, m + 3 ≤ G → parseMul G (T ++ rest) = .ok (x, rest) := by
    intro G hG
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 2 := ⟨G - 2, by omega⟩
    have := hU (G' + 1) (by omega)
    simp only [parseMul, parseMulL, this, stopMul rest hr]
  have hA : ∀ G, m + 4 ≤ G → parseAdd G (T ++ rest) = .ok (x, rest) := by
    intro G hG
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 2 := ⟨G - 2, by omega⟩
    have := hM (G' + 1) (by omega)
    simp only [parseAdd, parseAddL, this, stopAdd rest hr]
  have hB : ∀ G, m + 5 ≤ G → parseBit G (T ++ rest) = .ok (x, rest) := by
    intro G hG
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 2 := ⟨G - 2, by omega⟩
    have := hA (G' + 1) (by omega)
    simp only [parseBit, parseBitL, this, stopBit rest hr]
  intro G hG
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
  have := hB G' (by omega)
  simp only [parseCmp, this, stopVgl rest hr]

/-- `( x )` read at the comparison level. -/
theorem cmp_klammer (x : SExpr) (hx : gut x = true) (rest : List Token) (hr : ruhig rest = true)
    (G : Nat) (hG : fb x + 8 + 8 ≤ G) :
    parseCmp G (.zeichen "(" :: (druckToks x ++ .zeichen ")" :: rest)) = .ok (x, rest) := by
  have hU : ∀ G, fb x + 8 + 2 ≤ G →
      parseUnary G ([.zeichen "("] ++ (druckToks x ++ [.zeichen ")"]) ++ rest) = .ok (x, rest) := by
    intro G hG
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 2 := ⟨G - 2, by omega⟩
    have hO := (legs_tok x hx).2.2.2.2.2.2.2 ([.zeichen ")"] ++ rest) G' (hr_paren rest)
      (hrs_paren rest) (hrg_paren rest) (by omega)
    have hP := paren_arm _ _ _ _ hO
    have := un_paren_fall _ _ _ _ hP
    simpa only [List.append_assoc] using this
  have := cmp_aus_unary (fb x + 8) x ([.zeichen "("] ++ (druckToks x ++ [.zeichen ")"])) rest hr hU G
    (by omega)
  simpa only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] using this

/-! ### The predicate reader -/

/-- What may follow a predicate: benign for an expression, and no `=>`, `in`, `reaches`. -/
def PredFolge (rest : List Token) : Prop :=
  ruhig rest = true ∧ ruhigSuff rest = true ∧ ruhigGleit rest = true ∧
  (∀ r, rest ≠ .zeichen "=>" :: r) ∧ (∀ r, rest ≠ .wort "in" :: r) ∧ (∀ r, rest ≠ .wort "reaches" :: r)

/-- The head of a printed expression: never a quantifier word, and `!` only for a `!` tree. -/
def KopfPred (t : Token) : Prop := t ≠ .wort "forall" ∧ t ≠ .wort "exists"

theorem druck_kopf_pred (e : SExpr) (hg : gut e = true) :
    ∃ t ts, druckToks e = t :: ts ∧ KopfPred t ∧ (t = .zeichen "!" → ∃ x, e = .un "!" x) := by
  have kw : ∀ w, w ≠ "forall" → w ≠ "exists" → KopfPred (.wort w) := by
    intro w h1 h2; exact ⟨fun e => h1 (by injection e), fun e => h2 (by injection e)⟩
  have ki : ∀ a, istKopfWort a = false → KopfPred (nameTok a) := by
    intro a h
    obtain ⟨-, -, -, -, -, -, -, -, -, -⟩ := kopf_ne h
    have hf : a ≠ "forall" := by intro e; subst e; revert h; decide
    have he : a ≠ "exists" := by intro e; subst e; revert h; decide
    unfold nameTok; split
    · exact ⟨fun e => hf (by injection e), fun e => he (by injection e)⟩
    · exact ⟨by simp, by simp⟩
  have platz : ∀ p, gutPlatz p = true → ∃ t ts, druckToks p = t :: ts ∧ KopfPred t ∧
      (t = .zeichen "!" → ∃ x, p = .un "!" x) := by
    intro p hp
    obtain ⟨a, ts, h, ak⟩ := platz_kopf p hp
    exact ⟨_, ts, h, ki a ak, by simp⟩
  cases e with
  | lit n => exact ⟨_, _, rfl, ⟨by simp, by simp⟩, by simp⟩
  | float s => exact ⟨_, _, rfl, ⟨by simp, by simp⟩, by simp⟩
  | tru => exact ⟨_, _, rfl, kw _ (by decide) (by decide), by simp⟩
  | fls => exact ⟨_, _, rfl, kw _ (by decide) (by decide), by simp⟩
  | «variable» s => exact ⟨_, _, rfl, ki s (by simpa [gut] using hg), by simp⟩
  | field x f => exact platz _ hg
  | index x i => exact platz _ hg
  | arrow x f => exact platz _ hg
  | un o x =>
    by_cases hs0 : strEq o "-()" = true
    · refine ⟨.zeichen "-", .zeichen "(" :: (druckToks x ++ [.zeichen ")"]), by simp [druckToks, hs0],
        ⟨by simp, by simp⟩, ?_⟩
      intro h; injection h with h; exact absurd h (by decide)
    refine ⟨.zeichen o, _, by simp [druckToks, hs0]; rfl, ⟨by simp, by simp⟩, ?_⟩
    intro h; injection h with h; subst h; exact ⟨x, rfl⟩
  | bin o l r => exact ⟨_, _, rfl, ⟨by simp, by simp⟩, by simp⟩
  | call f xs =>
    exact ⟨_, _, rfl, ki f (by simp only [gut, Bool.and_eq_true] at hg; simpa using hg.1), by simp⟩
  | fnref p => exact ⟨_, _, rfl, ⟨by simp, by simp⟩, by simp⟩
  | built w xs =>
    rcases gut_built_faelle w xs hg with ⟨x, hw, rfl, -, -⟩ | ⟨a, b, rfl, rfl, -, -⟩
    · rcases hw with rfl | rfl
      · exact ⟨_, _, rfl, kw _ (by decide) (by decide), by simp⟩
      · exact ⟨_, _, rfl, kw _ (by decide) (by decide), by simp⟩
    · exact ⟨_, _, rfl, kw _ (by decide) (by decide), by simp⟩
  | old x => exact ⟨_, _, rfl, kw _ (by decide) (by decide), by simp⟩
  | res => exact ⟨_, _, rfl, kw _ (by decide) (by decide), by simp⟩
  | why g f =>
    exact ⟨_, _, rfl, ki g (by simp only [gut, Bool.and_eq_true] at hg; simpa using hg.1.1.1), by simp⟩
  | ext k ns xs =>
    obtain ⟨rfl, rfl, c, ys, rfl, hc, hv, -⟩ := gut_ruf_faelle k ns xs hg
    obtain ⟨t, ts, h, hk, h3⟩ := platz c hc
    refine ⟨t, ts ++ ([.zeichen "("] ++ druckToksListe ys ++ [.zeichen ")"]), by rw [druck_ruf, h]; rfl, hk,
      fun ht => ?_⟩
    obtain ⟨x, rfl⟩ := h3 ht
    simp [gutPlatz] at hc

/-- After `parseCmp`, the atom's tail checks. -/
theorem predAtom_aus (H : Nat) (toks rest : List Token) (e : SExpr)
    (hq : ∀ x r, toks ≠ .wort "forall" :: x :: .wort "in" :: r)
    (hq2 : ∀ x r, toks ≠ .wort "exists" :: x :: .wort "in" :: r)
    (hC : parseCmp H toks = .ok (e, rest)) (hf : PredFolge rest) :
    parsePredAtom (H + 1) toks = .ok (e, rest) := by
  obtain ⟨-, -, -, -, hin, hre⟩ := hf
  rw [parsePredAtom.eq_def]
  simp only [hC]

theorem quant_frei (t : Token) (ts : List Token) (h : KopfPred t) :
    (∀ x r, t :: ts ≠ .wort "forall" :: x :: .wort "in" :: r) ∧
    (∀ x r, t :: ts ≠ .wort "exists" :: x :: .wort "in" :: r) :=
  ⟨fun x r e => h.1 (by injection e), fun x r e => h.2 (by injection e)⟩

theorem predNot_bang (G : Nat) (R rest : List Token) (a : SExpr)
    (hA : parsePredAtom G R = .ok (a, rest)) (hpf : ∀ r, rest ≠ .zeichen "=>" :: r) :
    parsePredNot (G + 1) (.zeichen "!" :: R) = .ok (.un "!" a, rest) := by
  simp only [parsePredNot, hA, ite_true]

theorem predNot_plain (G : Nat) (t : Token) (R rest : List Token) (a : SExpr) (ht : t ≠ .zeichen "!")
    (hA : parsePredAtom G (t :: R) = .ok (a, rest)) (hpf : ∀ r, rest ≠ .zeichen "=>" :: r) :
    parsePredNot (G + 1) (t :: R) = .ok (a, rest) := by
  cases t with
  | zeichen z =>
    have hz : ∀ r, Token.zeichen z :: R ≠ .zeichen "!" :: r := by
      intro r e; injection e with e1; exact ht e1
    simp only [parsePredNot, hz, hA]
    simp
  | _ => simp only [parsePredNot, hA]; simp

/-- **Predicates read back**: a printable expression through `parsePred`. -/
theorem pred_druck (e : SExpr) (hg : gut e = true) (rest : List Token) (hf : PredFolge rest)
    (F : Nat) (hF : fb e + 20 ≤ F) : parsePred F (druckToks e ++ rest) = .ok (e, rest) := by
  obtain ⟨hr1, hr2, hr3, hpf, -, -⟩ := id hf
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 4 := ⟨F - 4, by omega⟩
  -- the atom (with its `!`, when there is one)
  have hAtom : parsePredNot (F' + 2) (druckToks e ++ rest) = .ok (e, rest) := by
    obtain ⟨t, ts, hd, hk, hbang⟩ := druck_kopf_pred e hg
    by_cases hb : t = .zeichen "!"
    · obtain ⟨x, rfl⟩ := hbang hb
      have hx : gut x = true := by
        simp only [gut, strEq_bang_klammer, Bool.false_and, Bool.or_false, Bool.and_eq_true] at hg; exact hg.2
      cases hat : istAtom x with
      | true =>
        have hdx : druckToks (.un "!" x) = .zeichen "!" :: druckToks x := by simp [druckToks, hat]
        obtain ⟨t2, ts2, hd2, hk2, -⟩ := druck_kopf_pred x hx
        have hC := (legs_tok x hx).2.2.2.2.2.1 rest F' hr1 hr2 hr3 (by
          simp only [fb, hdx, List.length_cons] at hF ⊢; omega)
        have hA := predAtom_aus F' (druckToks x ++ rest) rest x
          (by rw [hd2]; exact (quant_frei _ _ hk2).1) (by rw [hd2]; exact (quant_frei _ _ hk2).2) hC hf
        rw [hdx, List.cons_append]
        exact predNot_bang _ _ _ _ hA hpf
      | false =>
        have hdx : druckToks (.un "!" x) = .zeichen "!" :: .zeichen "(" :: (druckToks x ++ [.zeichen ")"]) := by
          simp [druckToks, hat]
        have hC := cmp_klammer x hx rest hr1 F' (by
          simp only [fb, hdx, List.length_cons, List.length_append, List.length_singleton] at hF ⊢; omega)
        have hA := predAtom_aus F' (.zeichen "(" :: (druckToks x ++ .zeichen ")" :: rest)) rest x
          (by intro x r e; injection e with e; cases e) (by intro x r e; injection e with e; cases e) hC hf
        rw [hdx]
        simp only [List.cons_append, List.append_assoc, List.singleton_append]
        exact predNot_bang _ _ _ _ hA hpf
    · have hC := (legs_tok e hg).2.2.2.2.2.1 rest F' hr1 hr2 hr3 (by omega)
      have hA := predAtom_aus F' (druckToks e ++ rest) rest e
        (by rw [hd]; exact (quant_frei _ _ hk).1) (by rw [hd]; exact (quant_frei _ _ hk).2) hC hf
      rw [hd, List.cons_append] at hA ⊢
      exact predNot_plain _ _ _ _ _ hb hA hpf
  simp only [parsePred, parsePredAnd, hAtom, parsePredAndL, parsePredOrL, stopUnd rest hr1,
    stopOder rest hr1]

/-! ### Predicate and place lists -/

/-- Comma lists of printed predicates (the printers' `druckPredListe`). -/
theorem predListe_rund : ∀ (ps : List SExpr) (rest : List Token) (F : Nat), ps ≠ [] →
    (∀ p ∈ ps, gut p = true) → PredFolge rest → (∀ r, rest ≠ .zeichen "," :: r) →
    8 * (druckPredListe ps).length + 47 ≤ F →
    parsePredListe F (druckPredListe ps ++ rest) = .ok (ps, rest) := by
  intro ps
  induction ps with
  | nil => intro _ _ h; exact absurd rfl h
  | cons p ps ih =>
    intro rest F _ hg hf hk hF
    have hp := hg p (by simp)
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    cases ps with
    | nil =>
      simp only [druckPredListe] at hF ⊢
      have hP := pred_druck p hp rest hf F' (by simp only [fb]; omega)
      simp only [parsePredListe, hP]
    | cons q qs =>
      have hq := hg q (by simp)
      have hd : druckPredListe (p :: q :: qs) ++ rest =
          druckToks p ++ .zeichen "," :: (druckPredListe (q :: qs) ++ rest) := by
        simp [druckPredListe]
      have hlen : (druckPredListe (p :: q :: qs)).length =
          (druckToks p).length + 1 + (druckPredListe (q :: qs)).length := by
        simp [druckPredListe]; omega
      have hlq : (druckToks q).length ≤ (druckPredListe (q :: qs)).length := by
        cases qs <;> simp [druckPredListe]
      rw [hlen] at hF
      rw [hd]
      have hR := ih rest F' (by simp) (fun x hx => hg x (List.mem_cons_of_mem _ hx)) hf hk (by omega)
      have hfk : PredFolge (.zeichen "," :: (druckPredListe (q :: qs) ++ rest)) :=
        ⟨rfl, rfl, rfl, (by intro r e; simp at e), (by intro r e; simp at e), (by intro r e; simp at e)⟩
      have hP := pred_druck p hp _ hfk F' (by simp only [fb]; omega)
      have hQ : ∃ v, parsePred F' (druckPredListe (q :: qs) ++ rest) = .ok v := by
        cases qs with
        | nil =>
          have h1 : (druckPredListe [q]).length = (druckToks q).length := rfl
          exact ⟨_, pred_druck q hq rest hf F' (by simp only [fb]; omega)⟩
        | cons x xs =>
          have hd2 : druckPredListe (q :: x :: xs) ++ rest =
              druckToks q ++ .zeichen "," :: (druckPredListe (x :: xs) ++ rest) := by
            simp [druckPredListe]
          rw [hd2]
          exact ⟨_, pred_druck q hq _ ⟨rfl, rfl, rfl, (by intro r e; simp at e), (by intro r e; simp at e),
            (by intro r e; simp at e)⟩ F' (by simp only [fb]; omega)⟩
      obtain ⟨v, hv⟩ := hQ
      simp only [parsePredListe, hP, hv, hR]

theorem druckPlaetze_eq : ∀ (ps : List SExpr), druckPlaetze ps = druckPredListe ps := by
  intro ps
  induction ps with
  | nil => rfl
  | cons p ps ih => cases ps with
    | nil => rfl
    | cons q qs => simp only [druckPlaetze, druckPredListe] at ih ⊢; rw [ih]

/-! ### `::` paths printed as text -/

theorem scan_name_vor (b : Bool) (s : String) (c : Char) (rest : List Char) (m : Nat)
    (h : nameForm s = true) (hc : istFolge c = false) (hc2 : c ≠ '/' ∨ True) :
    scan b (s.toList ++ c :: rest) (m + 1) = Except.map (nameTok s :: ·) (scan b (c :: rest) m) := by
  unfold nameForm at h
  have hs : s = String.ofList s.toList := (String.ofList_toList).symm
  generalize hl : s.toList = l at h hs
  match l, h with
  | d :: ds, h =>
    simp only [Bool.and_eq_true] at h
    have hle := istAnfang_nicht_leer h.1
    have hz : istZiffer d = false := by
      cases hz : istZiffer d
      · rfl
      · have := istZiffer_nicht_anfang hz; simp_all
    have hnf : nimmFolge (ds ++ c :: rest) = (ds, c :: rest) := by
      clear hs hl
      induction ds with
      | nil => simp [nimmFolge, hc]
      | cons e es ih =>
        simp only [List.all_cons, Bool.and_eq_true] at h
        simp only [List.cons_append, nimmFolge, h.2.1, ite_true, ih ⟨h.1, h.2.2⟩]
    rw [List.cons_append, scan.eq_7]
    · simp only [hle, hz, h.1, ite_true, Bool.false_eq_true, ite_false]
      rw [hnf]
      simp only [← hs, nameTok]
    · intro _ e _; exact istAnfang_ne h.1 '/' (by decide) e
    · intro _ e _; exact istAnfang_ne h.1 '/' (by decide) e
    · intro _ e _; exact istAnfang_ne h.1 '/' (by decide) e
    · intro _ e _; exact istAnfang_ne h.1 '/' (by decide) e
    · intro e; exact istAnfang_ne h.1 '"' (by decide) e

theorem scan_name_ende (b : Bool) (s : String) (m : Nat) (h : nameForm s = true) :
    scan b s.toList (m + 1) = .ok [nameTok s, .ende] := by
  unfold nameForm at h
  have hs : s = String.ofList s.toList := (String.ofList_toList).symm
  generalize hl : s.toList = l at h hs
  match l, h with
  | d :: ds, h =>
    simp only [Bool.and_eq_true] at h
    have hle := istAnfang_nicht_leer h.1
    have hz : istZiffer d = false := by
      cases hz : istZiffer d
      · rfl
      · have := istZiffer_nicht_anfang hz; simp_all
    rw [scan.eq_7]
    · simp only [hle, hz, h.1, ite_true, Bool.false_eq_true, ite_false]
      rw [nimmFolge_alle ds h.2]
      simp only [← hs, nameTok, scan]
      split <;> rfl
    · intro _ e _; exact istAnfang_ne h.1 '/' (by decide) e
    · intro _ e _; exact istAnfang_ne h.1 '/' (by decide) e
    · intro _ e _; exact istAnfang_ne h.1 '/' (by decide) e
    · intro _ e _; exact istAnfang_ne h.1 '/' (by decide) e
    · intro e; exact istAnfang_ne h.1 '"' (by decide) e

theorem scan_dd (b : Bool) (l : List Char) (m : Nat) (hl : ∀ r, l ≠ '%' :: r) (hl2 : ∀ r, l ≠ '<' :: r) :
    scan b (':' :: ':' :: l) (m + 1) = Except.map (Token.zeichen "::" :: ·) (scan b l m) := by
  simp [scan, nimmZeichen, istLeer, istZiffer, istAnfang]

/-- A path text, segments name-shaped, lexes to its path tokens. -/
theorem scan_pfad : ∀ (segs : List String) (n : Nat), segs ≠ [] →
    (∀ a ∈ segs, nameForm a = true) → 2 * segs.length ≤ n →
    scan false ([':', ':'].intercalate (segs.map String.toList)) n = .ok (pfadToks segs ++ [.ende]) := by
  intro segs
  induction segs with
  | nil => intro _ h; exact absurd rfl h
  | cons a segs ih =>
    intro n _ hg hn
    have ha := hg a (by simp)
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
    cases segs with
    | nil =>
      simp only [List.map_cons, List.map_nil, List.intercalate_singleton]
      rw [scan_name_ende false a m ha]
      simp [pfadToks, nameTok]
    | cons b bs =>
      have hb := hg b (by simp)
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp at hn; omega⟩
      have hi := ih k (by simp) (fun x hx => hg x (List.mem_cons_of_mem _ hx)) (by simp at hn ⊢; omega)
      have hcons : [':', ':'].intercalate ((a :: b :: bs).map String.toList) =
          a.toList ++ ':' :: ':' :: [':', ':'].intercalate ((b :: bs).map String.toList) := by
        simp [List.intercalate_cons_cons]
      have hbk : ∃ c cs, [':', ':'].intercalate ((b :: bs).map String.toList) = c :: cs ∧ istAnfang c = true := by
        unfold nameForm at hb
        cases hbl : b.toList with
        | nil => rw [hbl] at hb; simp at hb
        | cons c cs =>
          rw [hbl] at hb; simp only [Bool.and_eq_true] at hb
          cases bs with
          | nil => exact ⟨c, cs, by simp [hbl], hb.1⟩
          | cons x xs =>
            exact ⟨c, cs ++ ':' :: ':' :: [':', ':'].intercalate ((x :: xs).map String.toList),
              by simp [List.intercalate_cons_cons, hbl], hb.1⟩
      obtain ⟨c, cs, hc, hca⟩ := hbk
      rw [hcons, scan_name_vor false a ':' _ _ ha (by decide) (Or.inr trivial), scan_dd]
      · rw [hi]
        simp [pfadToks, nameTok, Except.map]
      · rw [hc]; intro r e; injection e with e; subst e; simp [istAnfang] at hca
      · rw [hc]; intro r e; injection e with e; subst e; simp [istAnfang] at hca

theorem pfad_len : ∀ (segs : List String), segs ≠ [] → (∀ a ∈ segs, nameForm a = true) →
    2 * segs.length ≤ ([':', ':'].intercalate (segs.map String.toList)).length + 1 := by
  intro segs
  induction segs with
  | nil => intro h; exact absurd rfl h
  | cons a as ih =>
    intro _ hg
    have ha : 1 ≤ a.toList.length := by
      have := hg a (by simp)
      unfold nameForm at this
      cases h : a.toList with
      | nil => rw [h] at this; simp at this
      | cons _ _ => simp
    cases as with
    | nil =>
      rw [List.map_cons, List.map_nil, List.intercalate_singleton]
      simp only [List.length_singleton]; omega
    | cons b bs =>
      have := ih (by simp) (fun x hx => hg x (List.mem_cons_of_mem _ hx))
      rw [List.map_cons, List.map_cons, List.intercalate_cons_cons]
      rw [List.map_cons] at this
      simp only [List.length_append, List.length_cons] at this ⊢
      omega

theorem lex_pfad (segs : List String) (hne : segs ≠ [])
    (hg : ∀ a ∈ segs, nameForm a = true) :
    lex ("::".intercalate segs) = .ok (pfadToks segs ++ [.ende]) := by
  unfold lex
  rw [← String.length_toList, String.toList_intercalate]
  have : ("::" : String).toList = [':', ':'] := rfl
  rw [this]
  exact scan_pfad segs _ hne hg (pfad_len segs hne hg)

/-- A name-shaped name prints as a lexically clean token. -/
theorem tokGut_nameTok {a : String} (h : nameForm a = true) : TokGut (nameTok a) := by
  unfold nameTok; split
  · exact ⟨h, by assumption⟩
  · exact ⟨h, by simpa using (by assumption : ¬ istSchluessel a = true)⟩

theorem pfad_tokGut : ∀ (segs : List String), (∀ a ∈ segs, nameForm a = true) →
    ∀ t ∈ pfadToks segs, TokGut t := by
  intro segs
  induction segs with
  | nil => intro _ t h; simp [pfadToks] at h
  | cons a as ih =>
    intro hg t ht
    have ha := hg a (by simp)
    cases as with
    | nil => simp [pfadToks] at ht; subst ht; exact tokGut_nameTok ha
    | cons b bs =>
      simp only [pfadToks, List.cons_append, List.nil_append, List.mem_cons] at ht
      rcases ht with rfl | rfl | ht
      · exact tokGut_nameTok ha
      · show [':', ':'] ∈ markTafel; decide
      · exact ih (fun x hx => hg x (List.mem_cons_of_mem _ hx)) t (by simpa [pfadToks] using ht)

theorem rohToks_pfad (segs : List String) (hne : segs ≠ [])
    (hg : ∀ a ∈ segs, nameForm a = true) :
    rohToks ("::".intercalate segs) = pfadToks segs := by
  unfold rohToks
  rw [lex_pfad segs hne hg]
  exact filter_ende (pfadToks segs) (pfad_tokGut segs hg)

end Gabbro.Grammatik.Parser
