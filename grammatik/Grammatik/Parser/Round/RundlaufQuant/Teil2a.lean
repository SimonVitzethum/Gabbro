module

public import Grammatik.Parser.Round.RundlaufPred
public import Grammatik.Parser.Round.RundlaufQuant.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000

/-- `l || X` where the `&&` reader fails on `X`. -/
theorem oder_fehlt (l : SExpr) (hl : gut l = true) (X : List Token) (c b : Nat) (hX : Fehlt parseAnd c X)
    (h1 : fb l + 9 ≤ b) (h2 : c + 3 ≤ b) : Fehlt parseOr b (druckToks l ++ .zeichen "||" :: X) := by
  intro f hf
  obtain ⟨k, rfl⟩ : ∃ k, f = k + 3 := ⟨f - 3, by omega⟩
  have hC := cmp_gut l hl (.zeichen "||" :: X) (atomFolge_zeichen "||" X (Or.inr (Or.inl rfl))) (k + 1)
    (by omega)
  have hAL : parseAndL (k + 1) l (.zeichen "||" :: X) = .ok (l, .zeichen "||" :: X) := by
    simp only [parseAndL, opUnd, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, imp_self, implies_true]
  have hA : parseAnd (k + 2) (druckToks l ++ .zeichen "||" :: X) = .ok (l, .zeichen "||" :: X) := by
    simp only [parseAnd, hC, hAL]
  obtain ⟨m, hm⟩ := hX (k + 1) (by omega)
  have hOL : parseOrL (k + 2) l (.zeichen "||" :: X) = .error m := by
    simp only [parseOrL, opOder, hm]
  exact ⟨m, by simp only [parseOr, hA, hOL]⟩

/-- `( a => X` read as an expression: the parenthesis never closes before `=>`. -/
theorem folgt_fehlt (a : SExpr) (X : List Token) (c b : Nat)
    (ha : gut a = true ∨ Fehlt parseOr c (druckToks a ++ .zeichen "=>" :: X))
    (h1 : fb a + 9 ≤ b) (h2 : c + 1 ≤ b) :
    Fehlt parsePrimary b (.zeichen "(" :: (druckToks a ++ .zeichen "=>" :: X)) := by
  rcases ha with ha | ha
  · intro f hf
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    have hO := (legs_tok a ha).2.2.2.2.2.2.2 (.zeichen "=>" :: X) g rfl rfl rfl (by omega)
    exact ⟨"( without )", by simp only [parsePrimary, hO, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, imp_self, implies_true]⟩
  · exact fehlt_mono (fehlt_prim_klammer ha) (by omega)

/-! ### The predicate class and its legs -/

/-- **The printable predicates** (see the header). -/
inductive PredGut : SExpr → Prop
  | expr (e : SExpr) : gut e = true → PredGut e
  | quant (k : XKind) (x dk : String) (ns : List String) (ops : List SExpr) (body : SExpr) :
      (k = .all ∨ k = .any) → DomGut dk ns ops → PredGut body →
      PredGut (.ext k (x :: dk :: ns) (ops ++ [body]))
  | und (l r : SExpr) : PredGut l → PredGut r → PredGut (.bin "&&" l r)
  | oder (l r : SExpr) : PredGut l → PredGut r → PredGut (.bin "||" l r)
  | nicht (x : SExpr) : PredGut x → PredGut (.un "!" x)
  | folgt (a b : SExpr) : PredGut a → PredGut b → PredGut (.ext .imp [] [a, b])

/-- The fuel of a predicate's atom and of its failing expression read. -/
def bP (e : SExpr) : Nat := 8 * (druckToks e).length + 42
def bE (e : SExpr) : Nat := 8 * (druckToks e).length + 12

/-- What the induction carries. -/
structure PredBein (e : SExpr) : Prop where
  atom : ∀ R G, AtomFolge R → bP e ≤ G → parsePredAtom G (atomTeil e ++ R) = .ok (atomWert e, R)
  fehlt : gut e = false → ∀ R, Fehlt parseUnary (bE e) (druckToks e ++ R)
  kopf : ∃ t ts, druckToks e = t :: ts ∧ (t = .zeichen "!" → nichtKopf e = true) ∧
    (gut e = false → t = .zeichen "(" ∨ t = .zeichen "!")

theorem bein_not (e : SExpr) (h : PredBein e) (R : List Token) (G : Nat) (hR : AtomFolge R)
    (hn : ∀ r, R ≠ .zeichen "=>" :: r) (hG : bP e + 1 ≤ G) : parsePredNot G (druckToks e ++ R) = .ok (e, R) := by
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
  have hA := h.atom R G' hR (by omega)
  cases hk : nichtKopf e with
  | false =>
    obtain ⟨t, ts, hd, hb, -⟩ := h.kopf
    obtain ⟨h1, h2⟩ := atom_nicht_nichtKopf e hk
    rw [h1, h2] at hA
    exact predNot_ohne e G' R t ts hd (fun e' => by rw [hb e'] at hk; cases hk) hA hn
  | true =>
    cases e with
    | un o x =>
      simp only [nichtKopf] at hk
      have := (strEq_eq _ _).mp hk; subst this
      simp only [atomWert, strEq_self, ite_true] at hA
      exact predNot_mit x G' R hA hn
    | _ => simp only [nichtKopf, Bool.false_eq_true] at hk

theorem bein_notF (e b : SExpr) (h : PredBein e) (X r : List Token) (G : Nat)
    (hB : parsePred G X = .ok (b, r)) (hG : bP e ≤ G) :
    parsePredNot (G + 1) (druckToks e ++ .zeichen "=>" :: X) = .ok (.ext .imp [] [e, b], r) := by
  have hA := h.atom (.zeichen "=>" :: X) G (atomFolge_zeichen "=>" X (Or.inr (Or.inr (Or.inl rfl)))) hG
  cases hk : nichtKopf e with
  | false =>
    obtain ⟨t, ts, hd, hb, -⟩ := h.kopf
    obtain ⟨h1, h2⟩ := atom_nicht_nichtKopf e hk
    rw [h1, h2] at hA
    exact predNot_ohne_folgt e b G X r t ts hd (fun e' => by rw [hb e'] at hk; cases hk) hA hB
  | true =>
    cases e with
    | un o x =>
      simp only [nichtKopf] at hk
      have := (strEq_eq _ _).mp hk; subst this
      simp only [atomWert, strEq_self, ite_true] at hA
      exact predNot_mit_folgt x b G X r hA hB
    | _ => simp only [nichtKopf, Bool.false_eq_true] at hk

theorem bein_top (e : SExpr) (h : PredBein e) (R : List Token) (G : Nat) (hR : PredFolge R)
    (hG : bP e + 4 ≤ G) : parsePred G (druckToks e ++ R) = .ok (e, R) := by
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 4 := ⟨G - 4, by omega⟩
  exact pred_aus_not e G' R hR.1 (bein_not e h R (G' + 2) (atomFolge_pred R hR) hR.2.2.2.1 (by omega))

/-! ### Inside the parenthesis: the predicate reader -/

theorem atom_klammer (G : Nat) (T R : List Token) (p : SExpr) (m : String)
    (hC : parseCmp G (.zeichen "(" :: T) = .error m) (hP : parsePred G T = .ok (p, .zeichen ")" :: R)) :
    parsePredAtom (G + 1) (.zeichen "(" :: T) = .ok (p, R) := by
  simp only [parsePredAtom]
  simp only [hC, hP]

theorem und_innen (l r : SExpr) (hl : PredBein l) (hr : PredBein r) (R : List Token) (G : Nat)
    (h1 : bP l + 3 ≤ G) (h2 : bP r + 2 ≤ G) :
    parsePred (G + 4) (druckToks l ++ .zeichen "&&" :: (druckToks r ++ .zeichen ")" :: R)) =
      .ok (.bin "&&" l r, .zeichen ")" :: R) := by
  have hNl := bein_not l hl (.zeichen "&&" :: (druckToks r ++ .zeichen ")" :: R)) (G + 2)
    (atomFolge_zeichen "&&" _ (Or.inl rfl)) (by intro x e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e) (by omega)
  have hNr := bein_not r hr (.zeichen ")" :: R) (G + 1)
    (atomFolge_zeichen ")" _ (Or.inr (Or.inr (Or.inr rfl)))) (by intro x e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e) (by omega)
  have u1 : ∀ X : List Token, opUnd (.zeichen "&&" :: X) = some X := fun _ => rfl
  have u2 : opUnd (.zeichen ")" :: R) = none := rfl
  have o2 : opOder (.zeichen ")" :: R) = none := rfl
  simp only [parsePred, parsePredAnd, hNl, parsePredAndL, u1, hNr, u2, parsePredOrL, o2]

theorem oder_innen (l r : SExpr) (hl : PredBein l) (hr : PredBein r) (R : List Token) (G : Nat)
    (h1 : bP l + 3 ≤ G) (h2 : bP r + 2 ≤ G) :
    parsePred (G + 4) (druckToks l ++ .zeichen "||" :: (druckToks r ++ .zeichen ")" :: R)) =
      .ok (.bin "||" l r, .zeichen ")" :: R) := by
  have hNl := bein_not l hl (.zeichen "||" :: (druckToks r ++ .zeichen ")" :: R)) (G + 2)
    (atomFolge_zeichen "||" _ (Or.inr (Or.inl rfl))) (by intro x e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e) (by omega)
  have hNr := bein_not r hr (.zeichen ")" :: R) (G + 1)
    (atomFolge_zeichen ")" _ (Or.inr (Or.inr (Or.inr rfl)))) (by intro x e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e) (by omega)
  have u1 : ∀ X : List Token, opUnd (.zeichen "||" :: X) = none := fun _ => rfl
  have o1 : ∀ X : List Token, opOder (.zeichen "||" :: X) = some X := fun _ => rfl
  have u2 : opUnd (.zeichen ")" :: R) = none := rfl
  have o2 : opOder (.zeichen ")" :: R) = none := rfl
  simp only [parsePred, parsePredAnd, hNl, parsePredAndL, u1, parsePredOrL, o1, hNr, u2, o2]

theorem folgt_innen (a b : SExpr) (ha : PredBein a) (hb : PredBein b) (R : List Token) (G : Nat)
    (h1 : bP a ≤ G + 1) (h2 : bP b + 4 ≤ G + 1) :
    parsePred (G + 4) (druckToks a ++ .zeichen "=>" :: (druckToks b ++ .zeichen ")" :: R)) =
      .ok (.ext .imp [] [a, b], .zeichen ")" :: R) := by
  have hB := bein_top b hb (.zeichen ")" :: R) (G + 1)
    ⟨rfl, rfl, rfl, by simp only [ne_eq, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, not_false_eq_true, implies_true], by simp only [ne_eq, List.cons.injEq, reduceCtorEq, false_and, not_false_eq_true, implies_true], by simp only [ne_eq, List.cons.injEq, reduceCtorEq, false_and, not_false_eq_true, implies_true]⟩ h2
  have hN := bein_notF a b ha _ _ (G + 1) hB h1
  have u2 : opUnd (.zeichen ")" :: R) = none := rfl
  have o2 : opOder (.zeichen ")" :: R) = none := rfl
  simp only [parsePred, parsePredAnd, hN, parsePredAndL, u2, parsePredOrL, o2]

theorem quant_innen (k : XKind) (hk : k = .all ∨ k = .any) (x dk : String) (ns : List String)
    (ops : List SExpr) (hd : DomGut dk ns ops) (body : SExpr) (hb : PredBein body) (R : List Token) (G : Nat)
    (h1 : 8 * (domToks dk ns (druckToksViele ops)).length + 40 ≤ G) (h2 : bP body + 4 ≤ G) :
    parsePred (G + 5) (.wort (quantWort k) :: nameTok x :: .wort "in" ::
      (domToks dk ns (druckToksViele ops) ++ .zeichen ":" :: (druckToks body ++ .zeichen ")" :: R))) =
      .ok (.ext k (x :: dk :: ns) (ops ++ [body]), .zeichen ")" :: R) := by
  have hD := dom_rund dk ns ops hd (druckToks body ++ .zeichen ")" :: R) G h1
  have hB := bein_top body hb (.zeichen ")" :: R) G ⟨rfl, rfl, rfl, by simp only [ne_eq, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, not_false_eq_true, implies_true], by simp only [ne_eq, List.cons.injEq, reduceCtorEq, false_and, not_false_eq_true, implies_true], by simp only [ne_eq, List.cons.injEq, reduceCtorEq, false_and, not_false_eq_true, implies_true]⟩ h2
  have hA := quant_rund k hk x dk ns ops body R G hD hB
  have hN : parsePredNot (G + 3) (.wort (quantWort k) :: nameTok x :: .wort "in" ::
      (domToks dk ns (druckToksViele ops) ++ .zeichen ":" :: (druckToks body ++ .zeichen ")" :: R))) =
      .ok (.ext k (x :: dk :: ns) (ops ++ [body]), .zeichen ")" :: R) :=
    predNot_plain _ _ _ _ _ (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) hA (by intro r e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e)
  have u2 : opUnd (.zeichen ")" :: R) = none := rfl
  have o2 : opOder (.zeichen ")" :: R) = none := rfl
  simp only [parsePred, parsePredAnd, hN, parsePredAndL, u2, parsePredOrL, o2]

/-! ### The induction -/

theorem bein_expr (e : SExpr) (hg : gut e = true) : PredBein e := by
  have hL : 1 ≤ (druckToks e).length := by
    obtain ⟨t, ts, hd, -⟩ := druck_kopf_pred e hg; rw [hd]; simp only [List.length_cons, Nat.le_add_left]
  refine ⟨fun R G hR hG => atom_gut e hg R hR G (by simp only [fb, bP] at hG ⊢; omega),
    (fun h => by rw [hg] at h; cases h), ?_⟩
  obtain ⟨t, ts, hd, -, hbang⟩ := druck_kopf_pred e hg
  refine ⟨t, ts, hd, fun ht => ?_, (fun h => by rw [hg] at h; cases h)⟩
  obtain ⟨x, rfl⟩ := hbang ht
  exact nichtKopf_un x

theorem nichtKopf_ext (k : XKind) (ns : List String) (xs : List SExpr) : nichtKopf (.ext k ns xs) = false := by rfl

theorem bein_quant (k : XKind) (hk : k = .all ∨ k = .any) (x dk : String) (ns : List String) (ops : List SExpr)
    (hd : DomGut dk ns ops) (body : SExpr) (hb : PredBein body) :
    PredBein (.ext k (x :: dk :: ns) (ops ++ [body])) := by
  have hq : quantWort k = "forall" ∨ quantWort k = "exists" := by rcases hk with rfl | rfl <;> simp only [quantWort, String.reduceEq, or_false, or_true]
  have hdr := quant_druck k hk x dk ns ops body
  have hF : ∀ R, Fehlt parseUnary 2 (druckToks (.ext k (x :: dk :: ns) (ops ++ [body])) ++ R) := by
    intro R
    rw [hdr]
    simp only [List.cons_append, List.nil_append, List.append_assoc]
    exact fehlt_klammer (fehlt_quant _ hq _)
  refine ⟨?_, fun _ R => fehlt_mono (hF R) (by simp only [bE]; omega), ?_⟩
  · intro R G hR hG
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by simp only [bP] at hG; omega⟩
    simp only [atomTeil, atomWert]
    obtain ⟨m, hm⟩ := fehlt_cmp_u (hF R) G' (by simp only [bP] at hG; omega)
    simp only [bP] at hG
    rw [hdr] at hm hG ⊢
    simp only [List.cons_append, List.nil_append, List.append_assoc] at hm ⊢
    simp only [List.length_append, List.length_cons, List.length_nil] at hG
    obtain ⟨G5, rfl⟩ : ∃ G5, G' = G5 + 5 := ⟨G' - 5, by omega⟩
    exact atom_klammer _ _ R _ m hm (quant_innen k hk x dk ns ops hd body hb R G5 (by omega)
      (by simp only [bP]; omega))
  · rw [hdr]
    exact ⟨_, _, rfl, by simp only [Token.zeichen.injEq, String.reduceEq, false_implies], fun _ => Or.inl rfl⟩


end Gabbro.Grammatik.Parser
