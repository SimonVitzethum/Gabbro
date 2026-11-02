module

public import Grammatik.Parser.Round.RundlaufAnwVoll.Teil3a
public import Grammatik.Parser.Round.RundlaufQuant.Teil2
public import Grammatik.Parser.Round.RundlaufAnwVoll.Teil2
public import Grammatik.Parser.Round.RundlaufAnwVoll.Teil2a

@[expose] public section

namespace Gabbro.Grammatik.Parser
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
