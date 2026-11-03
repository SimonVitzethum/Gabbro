module

public import Grammatik.Parser.Round.RundlaufQuant.Teil2
public import Grammatik.Parser.Round.RundlaufAnwVoll.Teil2
public import Grammatik.Parser.Round.RundlaufAnwVoll.Teil2a

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
  simp only [parseLetExpr, strEq_semi_frage, Bool.false_eq_true, bind, Except.bind, hO, hN, fordereZeichen, strEq_self, ↓reduceIte, pure, Except.pure]

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
  obtain ⟨hmiss, hgeneric⟩ := zuweis_keineRufOeffnung "=" rfl
    (druckToks w ++ .wort "publishes" :: (P ++ .zeichen ";" :: rest))
  simp only [parseKopfStmt, hK]
  split
  · simp only [gutPlatz, Bool.false_eq_true] at hz
  · simp only [gutPlatz, Bool.false_eq_true] at hz
  · simp only [gutPlatz, Bool.false_eq_true] at hz
  · simp only [hmiss, imp_self, strEq_self, Bool.true_or, ↓reduceIte, List.tail_cons, hO]
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


end Gabbro.Grammatik.Parser
