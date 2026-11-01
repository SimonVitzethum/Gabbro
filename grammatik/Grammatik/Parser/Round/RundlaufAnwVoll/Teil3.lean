module

public import Grammatik.Parser.Round.RundlaufQuant.Teil2
public import Grammatik.Parser.Round.RundlaufAnwVoll.Teil2

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000

theorem anw_swap (n : String) (hx : n ≠ "mut") (ty : Option STyp) (o : SExpr) (k : String)
    (hty : TypOptGut ty) (ho : gut o = true) (hk : RohSemi k) :
    AnwBein (.swap n ty o k) := by
  intro rest F _ hF
  obtain ⟨ts, rfl, hts⟩ := hk
  have hroh := rohToks_render ts (fun t ht => (hts t ht).1)
  simp only [fbA, druckAnw, hroh, List.length_cons, List.length_nil, List.length_append] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 4 := ⟨F - 4, by omega⟩
  have hd : druckAnw (.swap n ty o (renderText ts)) ++ rest = .wort "let" :: ((if false then [.wort "mut"] else []) ++
      nameTok n :: (druckTypOpt ty ++ .zeichen "=" :: (druckToks o ++ .wort "exchange" ::
        (ts ++ .zeichen ";" :: rest)))) := by
    simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc, hroh, Bool.false_eq_true,
  ↓reduceIte]
  rw [hd, parseStmt_let _ _ (by first | rfl | exact ortsFort_nameTok _ _)]
  rw [show F' + 3 = (F' + 2) + 1 from rfl,
    parseLet_kopf (F' + 2) false n hx ty _ hty (by
      intro t ht; have := fbT_of ty t ht; simp only [fbT]; omega),
    parseLetNach_expr _ _ _ _ o ho]
  have hO := ausdruck o ho (.wort "exchange" :: (ts ++ .zeichen ";" :: rest)) (F' + 1) rfl rfl rfl
    (by omega)
  have hN := nimmBisZeichen_roh ";" ts rest
    (fun t ht => ⟨(hts t ht).1, fun e => (hts t ht).2 (Or.inl e),
      fun e => (hts t ht).2 (Or.inr (Or.inl e)), fun e => (hts t ht).2 (Or.inr (Or.inr e))⟩)
  simp only [parseLetExpr, bind, Except.bind, hO, hN, fordereZeichen, strEq_self, ↓reduceIte, pure, Except.pure]

/-- The payload of a publication: `nothing`, or a raw text in braces. -/
def PubGut (p : String) : Prop := p = "nothing" ∨ (RohZu p ∧ p ≠ "nothing")

theorem anw_emit (z w : SExpr) (p : String) (hz : gutPlatz z = true) (hw : gut w = true)
    (hp : PubGut p) : AnwBein (.emit z w p) := by
  intro rest F _ hF
  -- the payload tokens
  obtain ⟨P, hP, hPk⟩ : ∃ P : List Token, (if strEq p "nothing" then [Token.wort "nothing"]
      else [Token.zeichen "{"] ++ rohToks p ++ [Token.zeichen "}"]) = P ∧
      ∀ r, (match P ++ .zeichen ";" :: r with
        | .wort q :: rest'' =>
          if strEq q "nothing" then match fordereZeichen ";" rest'' with
            | .ok rest3 => (Except.ok (SAnw.emit z w "nothing", rest3) : Except String (SAnw × List Token))
            | .error e => .error e
          else .error "publishes without payload"
        | .zeichen "{" :: rest'' => match nimmBisZeichen "}" rest'' 0 with
          | .ok (pl, rest3) => match fordereZeichen "}" rest3 with
            | .ok rest4 => match fordereZeichen ";" rest4 with
              | .ok rest5 => .ok (.emit z w pl, rest5)
              | .error e => .error e
            | .error e => .error e
          | .error e => .error e
        | _ => .error "publishes without payload") = .ok (.emit z w p, r) := by
    rcases hp with rfl | ⟨⟨ts, rfl, hts⟩, hne⟩
    · refine ⟨[.wort "nothing"], by simp only [strEq_self, ↓reduceIte], ?_⟩
      intro r; simp only [List.cons_append, List.nil_append, strEq_self, ↓reduceIte, fordereZeichen]
    · have hroh := rohToks_render ts (fun t ht => (hts t ht).1)
      have hs : strEq (renderText ts) "nothing" = false := by
        cases h : strEq (renderText ts) "nothing"
        · rfl
        · exact absurd ((strEq_eq _ _).mp h) hne
      refine ⟨[.zeichen "{"] ++ ts ++ [.zeichen "}"], by simp only [hs, Bool.false_eq_true, ↓reduceIte, hroh, List.cons_append, List.nil_append], ?_⟩
      intro r
      have hN := nimmBisZeichen_roh "}" ts (.zeichen ";" :: r)
        (fun t ht => ⟨(hts t ht).1, fun e => (hts t ht).2 (Or.inl e), fun e => (hts t ht).2 (Or.inr e),
          fun e => (hts t ht).2 (Or.inr e)⟩)
      simp only [List.cons_append, List.nil_append, List.append_assoc, hN, fordereZeichen, strEq_self, ↓reduceIte]
  have hlenP : P.length ≤ (druckAnw (.emit z w p)).length := by
    rw [← hP]; simp only [List.cons_append, List.nil_append, druckAnw, List.append_assoc, List.length_append,
  List.length_cons, List.length_nil, Nat.zero_add]; omega
  simp only [fbA] at hF
  have hd : druckAnw (.emit z w p) ++ rest = druckToks z ++ .zeichen "=" :: (druckToks w ++
      .wort "publishes" :: (P ++ .zeichen ";" :: rest)) := by
    rw [← hP]; simp only [druckAnw, List.append_assoc, List.cons_append, List.nil_append]
  have hlz : (druckAnw (.emit z w p)).length = (druckToks z).length + 1 + (druckToks w).length + 1 +
      P.length + 1 := by
    rw [← hP]; simp only [druckAnw, List.append_assoc, List.cons_append, List.nil_append, List.length_append,
  List.length_cons, List.length_nil, Nat.zero_add]; omega
  have := platz_nicht_start z hz (.zeichen "=" :: (druckToks w ++
      .wort "publishes" :: (P ++ .zeichen ";" :: rest))) (by intro r' e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e) rfl
  obtain ⟨a, r, hzr, hr, hro, hrt⟩ := this
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 3 := ⟨F - 3, by omega⟩
  rw [hd, hzr, parseStmt_ident _ _ _ hr (Or.inl hro), parsePlatzStmt_ident _ _ _ hrt, ← hzr]
  have hK := kopfP z hz (.zeichen "=" :: (druckToks w ++ .wort "publishes" :: (P ++ .zeichen ";" :: rest)))
    F' rfl (by omega)
  have hO := ausdruck w hw (.wort "publishes" :: (P ++ .zeichen ";" :: rest)) F' rfl rfl rfl (by omega)
  simp only [parseKopfStmt, hK]
  split
  · simp only [gutPlatz, Bool.false_eq_true] at hz
  · simp only [gutPlatz, Bool.false_eq_true] at hz
  · simp only [String.reduceEq, imp_self, strEq_self, Bool.true_or, ↓reduceIte, List.tail_cons, hO]
    exact hPk rest


/-! ### `start`, `breaking`, loops, `narrow`, `traverse` -/

theorem parseStmt_start (f : Nat) (r : List Token) :
    parseStmt (f + 1) (.ident "start" :: .zeichen "{" :: r) = parseStart f r := by
  simp only [parseStmt]

theorem startRoots_rund : ∀ (ps : List String) (rest : List Token) (F : Nat), ps ≠ [] →
    (∀ p ∈ ps, NameGut p) → ps.length + 1 ≤ F →
    parseStartRoots F (druckWurzeln ps ++ .zeichen "}" :: rest) = .ok (ps, rest) := by
  intro ps
  induction ps with
  | nil => intro _ _ h; exact absurd rfl h
  | cons p ps ih =>
    intro rest F _ hp hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    have hp1 := rohToks_nameGut p (hp p (by simp only [List.mem_cons, true_or]))
    cases ps with
    | nil =>
      have hs := sammleSeg_stop2 [p] (.zeichen "}" :: rest) (by intro x e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e)
      simp only [parseStartRoots, bind, Except.bind, nimmName, druckWurzeln, hp1, List.cons_append, List.nil_append,
  nameText_nameTok, hs, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, imp_self, implies_true,
  fordereZeichen, strEq_self, ↓reduceIte, pure, Except.pure, String.intercalate_singleton]
    | cons q qs =>
      have hq := ih rest F' (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) (fun x hx => hp x (List.mem_cons_of_mem _ hx))
        (by simp only [List.length_cons, Nat.add_le_add_iff_right] at hF ⊢; omega)
      have hq1 := rohToks_nameGut q (hp q (by simp only [List.mem_cons, true_or, or_true]))
      have hs := sammleSeg_stop2 [p] (.zeichen "," :: (druckWurzeln (q :: qs) ++ .zeichen "}" :: rest))
        (by intro x e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e)
      have hw : druckWurzeln (q :: qs) = nameTok q :: (druckWurzeln (q :: qs)).tail := by
        cases qs <;> simp only [druckWurzeln, hq1, List.tail_cons, List.cons_append, List.nil_append]
      have hd : druckWurzeln (p :: q :: qs) ++ .zeichen "}" :: rest =
          nameTok p :: .zeichen "," :: (druckWurzeln (q :: qs) ++ .zeichen "}" :: rest) := by
        simp only [druckWurzeln, hp1, List.cons_append, List.nil_append]
      rw [hd]
      simp only [parseStartRoots, nimmName, nameText_nameTok, nameText_ident, nameText_wort, nameText_zeichen, nameText_num, nameText_ende, hs, String.intercalate_singleton, bind, Except.bind, pure, Except.pure]
      rw [hw] at hq ⊢
      simp only [List.cons_append] at hq
      simp only [List.cons_append, List.cons.injEq, nameTok_ne_zeichen, false_and, imp_self, implies_true, hq]

theorem anw_start (ps : List String) (hne : ps ≠ []) (hp : ∀ p ∈ ps, NameGut p) :
    AnwBein (.start ps) := by
  intro rest F _ hF
  have hlen : ps.length ≤ (druckWurzeln ps).length := by
    clear hF hne
    induction ps with
    | nil => simp only [List.length_nil, Nat.zero_le]
    | cons p ps ih =>
      have h1 := rohToks_nameGut p (hp p (by simp only [List.mem_cons, true_or]))
      have := ih (fun x hx => hp x (List.mem_cons_of_mem _ hx))
      cases ps with
      | nil => simp only [List.length_cons, List.length_nil, Nat.zero_add, druckWurzeln, h1, Std.le_refl]
      | cons q qs => simp only [List.length_cons, druckWurzeln, h1, List.cons_append, List.nil_append, Nat.add_le_add_iff_right,
  ge_iff_le] at this ⊢; omega
  simp only [fbA, druckAnw, List.length_append, List.length_cons, List.length_nil] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
  have hd : druckAnw (.start ps) ++ rest = .ident "start" :: .zeichen "{" ::
      (druckWurzeln ps ++ .zeichen "}" :: .zeichen ";" :: rest) := by
    simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc]
  have hR := startRoots_rund ps (.zeichen ";" :: rest) F' hne hp (by omega)
  rw [hd, parseStmt_start]
  simp only [parseStart, bind, Except.bind, hR, fordereZeichen, strEq_self, ↓reduceIte, pure, Except.pure]

theorem identList_rund : ∀ (ns : List String) (X : List Token) (F : Nat), ns ≠ [] →
    (∀ r, X ≠ .zeichen "," :: r) → ns.length ≤ F →
    nimmIdentList F (druckNamen ns ++ X) = .ok (ns, X) := by
  intro ns
  induction ns with
  | nil => intro _ _ h; exact absurd rfl h
  | cons n ns ih =>
    intro X F _ hX hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp only [List.length_cons] at hF; omega⟩
    cases ns with
    | nil =>
      rcases X with _ | ⟨x, xs⟩
      · simp only [nimmIdentList, nimmName, druckNamen, List.append_nil, nameText_nameTok]
      · have : ∀ r, x :: xs ≠ .zeichen "," :: r := hX
        simp only [druckNamen, List.cons_append, List.nil_append, nimmIdentList, nimmName, nameText_nameTok, nameText_ident, nameText_wort, nameText_zeichen, nameText_num, nameText_ende]
        all_goals split
        all_goals first
          | rfl
          | (rename_i heq; simp at heq; exact absurd (by rw [heq.1, heq.2]) (hX _))
    | cons m ms =>
      have hq := ih X F' (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) hX (by simp only [List.length_cons, Nat.add_le_add_iff_right] at hF ⊢; omega)
      simp only [druckNamen, List.cons_append, List.nil_append, List.singleton_append] at hq ⊢
      simp only [nimmIdentList, nimmName, nameText_nameTok, hq]

theorem anw_waive (ns : List String) (b : SAnw) (hne : ns ≠ []) (hb : BlockBein b) (hk : BlockKopf b) :
    AnwBein (.waive ns b) := by
  intro rest F _ hF
  have hlen : ns.length ≤ (druckNamen ns).length := by
    clear hF hne
    induction ns with
    | nil => simp only [List.length_nil, Nat.zero_le]
    | cons n ns ih => cases ns with
      | nil => simp only [List.length_cons, List.length_nil, Nat.zero_add, druckNamen, Std.le_refl]
      | cons m ms => simp only [List.length_cons, druckNamen, List.cons_append, List.nil_append, Nat.add_le_add_iff_right] at ih ⊢; omega
  obtain ⟨ts, hts⟩ := hk
  simp only [fbA, druckAnw, List.length_append, List.length_cons, List.length_nil] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 3 := ⟨F - 3, by omega⟩
  have hd : druckAnw (.waive ns b) ++ rest = .wort "breaking" :: (druckNamen ns ++ (druckAnw b ++ rest)) := by
    simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc]
  have hI := identList_rund ns (druckAnw b ++ rest) (F' + 1) hne (by rw [hts]; intro r e; simp only [List.cons_append, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e)
    (by omega)
  have hB := hb rest (F' + 1) (by simp only [fbA]; omega)
  have hof : istOrtsFort (druckNamen ns ++ (druckAnw b ++ rest)) = false := by
    cases ns with
    | nil => exact absurd rfl hne
    | cons n ns => cases ns <;> simp only [druckNamen, List.cons_append, List.nil_append, ortsFort_nameTok]
  rw [hd, parseStmt_breaking _ _ hof]
  simp only [parseBricht, hI, hB]

/-- A loop header: a raw text without a brace or `effects`, not starting with a place continuation. -/
def RohKopf (h : String) : Prop :=
  ∃ ts, h = renderText ts ∧ (∀ t ∈ ts, TokGut t ∧ t ≠ .zeichen "{" ∧ t ≠ .wort "effects") ∧
    ∀ R, istOrtsFort (ts ++ .zeichen "{" :: R) = false

theorem anw_schleife (art : Nat) (h : String) (b : SAnw) (ha : art = 1 ∨ art = 2) (hh : RohKopf h)
    (hb : BlockBein b) (hk : BlockKopf b) :
    AnwBein (if art = 1 then .retry h b else .loop h b) := by
  intro rest F _ hF
  obtain ⟨ts, rfl, hts, hof⟩ := hh
  obtain ⟨us, hus⟩ := hk
  have hroh := rohToks_render ts (fun t ht => (hts t ht).1)
  have hd : druckAnw (if art = 1 then .retry (renderText ts) b else .loop (renderText ts) b) ++ rest =
      .wort (if art = 1 then "retry" else "forever") :: (ts ++ (druckAnw b ++ rest)) := by
    rcases ha with rfl | rfl <;> simp only [↓reduceIte, druckAnw, hroh, List.cons_append, List.nil_append, List.append_assoc, Nat.succ_ne_self]
  have hlen : (druckAnw (if art = 1 then .retry (renderText ts) b else .loop (renderText ts) b)).length =
      1 + ts.length + (druckAnw b).length := by
    rcases ha with rfl | rfl <;> simp only [↓reduceIte, druckAnw, hroh, List.cons_append, List.nil_append, List.length_cons, List.length_append, Nat.succ_ne_self] <;> omega
  simp only [fbA, hlen] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
  have hK := schleifenKopf_roh ts (us ++ rest) F' (fun t ht => hts t ht) (by omega)
  have hB := hb rest F' (by simp only [fbA]; omega)
  have hof' : istOrtsFort (ts ++ (druckAnw b ++ rest)) = false := by
    rw [hus]; exact hof _
  rw [hd]
  rcases ha with rfl | rfl
  · simp only [ite_true]
    rw [parseStmt_retry _ _ hof']
    rw [hus] at hB ⊢
    simp only [List.cons_append] at hB
    simp only [parseSchleife, List.cons_append, hK, hB, BEq.rfl, ↓reduceIte]
  · simp only [show ¬((2 : Nat) = 1) from by decide, ite_false]
    rw [parseStmt_forever _ _ hof']
    rw [hus] at hB ⊢
    simp only [List.cons_append] at hB
    simp only [parseSchleife, List.cons_append, hK, hB, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte]

/-- The range text of `narrow ... to`: `finite`, or a raw text without braces or `else` that does
    not start with `finite`. -/
def TrimGut (t : String) : Prop :=
  t = "finite" ∨ ∃ ts, t = renderText ts ∧
    (∀ x ∈ ts, TokGut x ∧ x ≠ .zeichen "{" ∧ x ≠ .zeichen "}" ∧ x ≠ .wort "else") ∧
    ∀ r, ts ≠ .wort "finite" :: r

theorem anw_trim (o : SExpr) (t : String) (b : SAnw) (ho : gutPlatz o = true) (ht : TrimGut t)
    (hb : BlockBein b) (hk : BlockKopf b) : AnwBein (.trim o t b) := by
  intro rest F _ hF
  obtain ⟨us, hus⟩ := hk
  obtain ⟨c, cs, hc, ck⟩ := platz_kopf o ho
  rcases ht with rfl | ⟨ts, rfl, hts, hfin⟩
  · have hroh : rohToks "finite" = [.wort "finite"] := by
      rw [rohToks_name "finite" (by decide)]; simp only [nameTok, List.cons.injEq, ite_eq_left_iff, Bool.not_eq_true, reduceCtorEq, imp_false,
  Bool.not_eq_false, and_true]; decide
    simp only [fbA, druckAnw, hroh, List.length_append, List.length_cons, List.length_nil] at hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
    have hd : druckAnw (.trim o "finite" b) ++ rest = .wort "narrow" :: (druckToks o ++
        .wort "to" :: .wort "finite" :: .wort "else" :: (druckAnw b ++ rest)) := by
      simp only [druckAnw, List.cons_append, List.nil_append, hroh, List.append_assoc]
    have hO := ortP o ho (.wort "to" :: .wort "finite" :: .wort "else" :: (druckAnw b ++ rest)) F' rfl
      (by omega)
    have hB := hb rest F' (by simp only [fbA]; omega)
    rw [hd, parseStmt_narrow _ _ (by rw [hc]; first | rfl | exact ortsFort_nameTok _ _)]
    simp only [parseNarrow, hO, strEq_self, ↓reduceIte, hB]
  · have hroh := rohToks_render ts (fun x hx => (hts x hx).1)
    simp only [fbA, druckAnw, hroh, List.length_append, List.length_cons, List.length_nil] at hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
    have hd : druckAnw (.trim o (renderText ts) b) ++ rest = .wort "narrow" :: (druckToks o ++
        .wort "to" :: (ts ++ .wort "else" :: (druckAnw b ++ rest))) := by
      simp only [druckAnw, List.cons_append, List.nil_append, hroh, List.append_assoc]
    have hO := ortP o ho (.wort "to" :: (ts ++ .wort "else" :: (druckAnw b ++ rest))) F' rfl (by omega)
    have hB := hb rest F' (by simp only [fbA]; omega)
    have hN := nimmBisWort_roh "else" ts (druckAnw b ++ rest) hts
    rw [hd, parseStmt_narrow _ _ (by rw [hc]; first | rfl | exact ortsFort_nameTok _ _)]
    simp only [parseNarrow, hO, strEq_self, ite_true]
    split
    · rename_i z rest'' heq
      have hz : strEq z "finite" = false := by
        cases h : strEq z "finite"
        · rfl
        · have := (strEq_eq _ _).mp h
          subst this
          cases ts with
          | nil => simp only [List.nil_append, List.cons.injEq, Token.wort.injEq, String.reduceEq, false_and] at heq
          | cons x xs => simp only [List.cons_append, List.cons.injEq] at heq; exact absurd (by rw [heq.1]) (hfin xs)
      simp only [hz, Bool.false_eq_true, ite_false]
      rw [hN]
      simp only [nimmWort, strEq_self, ↓reduceIte, hB]
    · rw [hN]
      simp only [nimmWort, strEq_self, ↓reduceIte, hB]

/-- `traverseRest` stops at `invariant` too. -/
theorem traverseRest_roh2 : ∀ (ts rest : List Token) (x : Token),
    (x = .zeichen "{" ∨ x = .wort "invariant") →
    (∀ t ∈ ts, TokGut t ∧ t ≠ .zeichen "{" ∧ t ≠ .wort "invariant") →
    traverseRest (ts ++ x :: rest) = .ok (renderText ts, x :: rest) := by
  intro ts rest x hx
  rcases hx with rfl | rfl
  · exact traverseRest_roh ts rest
  · induction ts with
    | nil => intro _; simp only [List.nil_append, traverseRest, strEq_self, ↓reduceIte, renderText_nil]
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

/-- The raw words of a `traverse` header: no brace, no `invariant`. -/
def RohTrav (r : String) : Prop :=
  ∃ ts, r = renderText ts ∧ ∀ t ∈ ts, TokGut t ∧ t ≠ .zeichen "{" ∧ t ≠ .wort "invariant"

/-- The tokens an optional `of e` / `invariant e` adds. -/
def optTokLen : Option SExpr → Nat
  | some x => 1 + (druckToks x).length
  | none => 0

theorem anw_each (b : String) (o : Option SExpr) (k : String) (s : SExpr) (m : String) (r : String)
    (i : Option SExpr) (body : SAnw) (ho : ∀ e, o = some e → gut e = true) (hs : gut s = true)
    (hr : RohTrav r) (hi : ∀ e, i = some e → PredGut e) (hb : BlockBein body)
    (hk : BlockKopf body) : AnwBein (.each b o k s m r i body) := by
  intro rest F _ hF
  obtain ⟨ts, rfl, hts⟩ := hr
  obtain ⟨us, hus⟩ := hk
  have hroh := rohToks_render ts (fun x hx => (hts x hx).1)
  have hd0 : ∀ (O I : List Token), [Token.wort "traverse", nameTok b] ++ O ++
      [.wort "over", nameTok k, .wort "of"] ++ druckToks s ++ [.wort "by", nameTok m] ++ ts ++ I ++
        druckAnw body ++ rest = .wort "traverse" :: nameTok b :: (O ++ (.wort "over" :: nameTok k ::
          .wort "of" :: (druckToks s ++ (.wort "by" :: nameTok m :: (ts ++ (I ++ (.zeichen "{" ::
            (us ++ rest)))))))) := by
    intro O I; rw [hus]; simp only [List.cons_append, List.nil_append, List.append_assoc]
  have hlen : ∀ (O I : List Token), (druckAnw (.each b o k s m (renderText ts) i body)).length =
      2 + optTokLen o + 3 + (druckToks s).length + 2 + ts.length + optTokLen i +
        (druckAnw body).length := by
    intro _ _
    cases o <;> cases i <;> simp only [druckAnw, List.append_nil, List.cons_append, List.nil_append, hroh, List.append_assoc, List.length_cons, List.length_append, optTokLen, Nat.add_zero, Nat.reduceAdd] <;> omega
  have hlen' := hlen [] []
  simp only [fbA, hlen'] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
  have hS : ∀ (T : List Token), parseOr F' (druckToks s ++ .wort "by" :: T) = .ok (s, .wort "by" :: T) :=
    fun T => ausdruck s hs _ F' rfl rfl rfl (by omega)
  have hB : parseBlock F' (.zeichen "{" :: (us ++ rest)) = .ok (body, rest) := by
    have := hb rest F' (by simp only [fbA]; omega)
    rw [hus] at this; simpa using this
  have hT1 := traverseRest_roh2 ts (us ++ rest) (.zeichen "{") (Or.inl rfl) hts
  cases o with
  | none =>
    cases i with
    | none =>
      have hd : druckAnw (.each b none k s m (renderText ts) none body) ++ rest =
          [Token.wort "traverse", nameTok b] ++ [] ++ [.wort "over", nameTok k, .wort "of"] ++
          druckToks s ++ [.wort "by", nameTok m] ++ ts ++ [] ++ druckAnw body ++ rest := by
        simp only [druckAnw, List.append_nil, List.cons_append, List.nil_append, hroh, List.append_assoc]
      rw [hd, hd0, parseStmt_traverse _ _ (by first | rfl | exact ortsFort_nameTok _ _)]
      simp only [List.nil_append] at hT1 ⊢
      simp only [parseTraverse, nimmName, nameText_nameTok, List.cons.injEq, Token.wort.injEq, String.reduceEq,
  false_and, imp_self, implies_true, nimmWort, strEq_self, ↓reduceIte, hS, hT1, hB]
    | some e =>
      have he := hi e rfl
      have hd : druckAnw (.each b none k s m (renderText ts) (some e) body) ++ rest =
          [Token.wort "traverse", nameTok b] ++ [] ++ [.wort "over", nameTok k, .wort "of"] ++
          druckToks s ++ [.wort "by", nameTok m] ++ ts ++ ([.wort "invariant"] ++ druckToks e) ++
            druckAnw body ++ rest := by
        simp only [druckAnw, List.append_nil, List.cons_append, List.nil_append, hroh, List.append_assoc]
      have hT := traverseRest_roh2 ts (druckToks e ++ (.zeichen "{" :: (us ++ rest))) (.wort "invariant")
        (Or.inr rfl) hts
      have hE := pred_voll e he (.zeichen "{" :: (us ++ rest)) ⟨rfl, rfl, rfl, by simp only [ne_eq, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, not_false_eq_true,
  implies_true], by simp only [ne_eq, List.cons.injEq, reduceCtorEq, false_and, not_false_eq_true, implies_true], by simp only [ne_eq, List.cons.injEq, reduceCtorEq, false_and, not_false_eq_true, implies_true]⟩ F'
        (by simp only [bP]; simp only [optTokLen] at hF; omega)
      rw [hd, hd0, parseStmt_traverse _ _ (by first | rfl | exact ortsFort_nameTok _ _)]
      simp only [List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hT ⊢
      simp only [parseTraverse, nimmName, nameText_nameTok, List.cons.injEq, Token.wort.injEq, String.reduceEq,
  false_and, imp_self, implies_true, nimmWort, strEq_self, ↓reduceIte, hS, hT, hE, hB]
  | some x =>
    have hx := ho x rfl
    have hX : ∀ (T : List Token), parseOr F' (druckToks x ++ .wort "over" :: T) = .ok (x, .wort "over" :: T) :=
      fun T => ausdruck x hx _ F' rfl rfl rfl (by simp only [optTokLen] at hF; omega)
    cases i with
    | none =>
      have hd : druckAnw (.each b (some x) k s m (renderText ts) none body) ++ rest =
          [Token.wort "traverse", nameTok b] ++ ([.wort "of"] ++ druckToks x) ++
          [.wort "over", nameTok k, .wort "of"] ++ druckToks s ++ [.wort "by", nameTok m] ++ ts ++ [] ++
            druckAnw body ++ rest := by
        simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc, hroh, List.append_nil]
      rw [hd, hd0, parseStmt_traverse _ _ (by first | rfl | exact ortsFort_nameTok _ _)]
      simp only [List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hT1 ⊢
      simp only [parseTraverse, nimmName, nameText_nameTok, hX, nimmWort, strEq_self, ↓reduceIte, hS, hT1, hB]
    | some e =>
      have he := hi e rfl
      have hd : druckAnw (.each b (some x) k s m (renderText ts) (some e) body) ++ rest =
          [Token.wort "traverse", nameTok b] ++ ([.wort "of"] ++ druckToks x) ++
          [.wort "over", nameTok k, .wort "of"] ++ druckToks s ++ [.wort "by", nameTok m] ++ ts ++
            ([.wort "invariant"] ++ druckToks e) ++ druckAnw body ++ rest := by
        simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc, hroh]
      have hT := traverseRest_roh2 ts (druckToks e ++ (.zeichen "{" :: (us ++ rest))) (.wort "invariant")
        (Or.inr rfl) hts
      have hE := pred_voll e he (.zeichen "{" :: (us ++ rest)) ⟨rfl, rfl, rfl, by simp only [ne_eq, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, not_false_eq_true,
  implies_true], by simp only [ne_eq, List.cons.injEq, reduceCtorEq, false_and, not_false_eq_true, implies_true], by simp only [ne_eq, List.cons.injEq, reduceCtorEq, false_and, not_false_eq_true, implies_true]⟩ F'
        (by simp only [bP]; simp only [optTokLen] at hF; omega)
      rw [hd, hd0, parseStmt_traverse _ _ (by first | rfl | exact ortsFort_nameTok _ _)]
      simp only [List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hT ⊢
      simp only [parseTraverse, nimmName, nameText_nameTok, hX, nimmWort, strEq_self, ↓reduceIte, hS, hT, hE, hB]


/-! ### `if` with `else if` branches, `match` with arms -/

/-- The legs of an `else if` branch. -/
def ElsifBein (x : SAnw) : Prop :=
  ∃ c b, x = .elsif c b ∧ gut c = true ∧ BlockBein b ∧ BlockKopf b

/-- The tokens of an optional `else` block. -/
def druckSonst : Option SAnw → List Token
  | some b => [.wort "else"] ++ druckAnw b
  | none => []

end Gabbro.Grammatik.Parser
