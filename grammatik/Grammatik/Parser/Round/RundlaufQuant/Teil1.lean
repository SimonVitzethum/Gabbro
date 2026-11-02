/-
  File:      Grammatik/Parser/Round/RundlaufQuant.lean
  Subject:   Predicates with quantifiers read back: `forall x in D : p`, `exists x in D : p`, and
             `&&`, `||`, `!`, `=>` over them, through `parsePred` -- `pred_voll`.

  The printable predicates (`PredGut`): every printable expression (`gut`), the quantifiers
  `forall`/`exists` over the domains `slots of`, `descendants of`, `ancestors of`, `elems of`,
  `mappings of` a place, `queue` a place and `threads` (`DomGut`), and `&&`, `||`, `!`, `=>` over
  printable predicates. The printer prints a quantifier and `=>` in parentheses (`druckExtToks`),
  and every `&&`/`||` in parentheses (`druckToks`).

  The reader takes a parenthesis at the atom level: it first tries the expression reader
  (`parseCmp`) and falls back to `( pred )` when that fails. So the proof carries two legs per
  predicate (`PredBein`): the atom leg (what `parsePredAtom` returns) and, for a predicate that is
  no expression, the error leg (the expression reader fails on its print, `parseUnary` and up).

  Excluded (recorded in the CUTS at the end): `count x in D : p` (it reads as an expression at the
  primary level), `e in D`, `a reaches b via f`, the domains `fields of` and `chain (x, y) in`.
-/
module

public import Grammatik.Parser.Round.RundlaufPred
public import Grammatik.Parser.Round.RundlaufQuant.Teil1a

@[expose] public section



namespace Gabbro.Grammatik.Parser

set_option maxRecDepth 100000
/-- Does the print start with `!` (a `!` tree)? -/
def nichtKopf : SExpr → Bool
  | .un o _ => strEq o "!"
  | _ => false

/-- The atom part of a print: behind its `!` for a `!` tree, the whole print otherwise. -/
def atomTeil : SExpr → List Token
  | .un o x => if strEq o "!" then (if istAtom x then druckToks x else [.zeichen "("] ++ druckToks x ++ [.zeichen ")"])
      else druckToks (.un o x)
  | e => druckToks e

/-- What the atom reader returns on the atom part. -/
def atomWert : SExpr → SExpr
  | .un o x => if strEq o "!" then x else .un o x
  | e => e

theorem druck_nichtKopf (e : SExpr) (h : nichtKopf e = true) : druckToks e = .zeichen "!" :: atomTeil e := by
  cases e with
  | un o x =>
    simp only [nichtKopf] at h
    have := (strEq_eq _ _).mp h; subst this
    cases hx : istAtom x <;> simp only [druckToks, strEq_bang_klammer, Bool.false_eq_true, ↓reduceIte, hx, List.cons_append, List.nil_append, atomTeil, strEq_self]
  | _ => simp only [nichtKopf, Bool.false_eq_true] at h

theorem atom_nicht_nichtKopf (e : SExpr) (h : nichtKopf e = false) : atomTeil e = druckToks e ∧ atomWert e = e := by
  cases e with
  | un o x =>
    simp only [nichtKopf] at h
    simp only [atomTeil, h, Bool.false_eq_true, ↓reduceIte, atomWert, and_self]
  | _ => exact ⟨rfl, rfl⟩

theorem nichtKopf_un (x : SExpr) : nichtKopf (.un "!" x) = true := by simp only [nichtKopf, strEq_self]

/-- **A printable expression at the atom level** (behind its `!`, for a `!` tree). -/
theorem atom_gut (e : SExpr) (hg : gut e = true) (R : List Token) (hR : AtomFolge R) (G : Nat)
    (hG : fb e + 18 ≤ G) : parsePredAtom G (atomTeil e ++ R) = .ok (atomWert e, R) := by
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
  cases hk : nichtKopf e with
  | false =>
    obtain ⟨h1, h2⟩ := atom_nicht_nichtKopf e hk
    rw [h1, h2]
    obtain ⟨t, ts, hd, hkp, -⟩ := druck_kopf_pred e hg
    exact predAtom_aus' G' _ R e (by rw [hd]; exact (quant_frei _ _ hkp).1) (by rw [hd]; exact (quant_frei _ _ hkp).2)
      (cmp_gut e hg R hR G' (by omega)) hR.nichtIn hR.nichtReach
  | true =>
    cases e with
    | un o x =>
      simp only [nichtKopf] at hk
      have := (strEq_eq _ _).mp hk; subst this
      have hx : gut x = true := by
        simp only [gut, strEq_bang_klammer, Bool.false_and, Bool.or_false, Bool.and_eq_true] at hg; exact hg.2
      have hlen : (druckToks x).length + 1 ≤ (druckToks (.un "!" x)).length := by
        cases ha : istAtom x <;> simp only [druckToks, strEq_bang_klammer, Bool.false_eq_true, ↓reduceIte, ha, List.cons_append, List.nil_append, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.add_le_add_iff_right, Nat.le_add_right, Std.le_refl]
      simp only [atomTeil, atomWert, strEq_self, ite_true]
      cases ha : istAtom x with
      | true =>
        obtain ⟨t, ts, hd, hkp, -⟩ := druck_kopf_pred x hx
        simp only [ite_true]
        exact predAtom_aus' G' _ R x (by rw [hd]; exact (quant_frei _ _ hkp).1)
          (by rw [hd]; exact (quant_frei _ _ hkp).2)
          (cmp_gut x hx R hR G' (by simp only [fb] at hG ⊢; omega)) hR.nichtIn hR.nichtReach
      | false =>
        simp only [Bool.false_eq_true, ite_false, List.append_assoc, List.cons_append, List.nil_append,
          List.singleton_append]
        exact predAtom_aus' G' _ R x (by intro x r e; injection e with e; cases e)
          (by intro x r e; injection e with e; cases e)
          (cmp_klammer' x hx R hR.cmp G' (by simp only [fb] at hG ⊢; omega)) hR.nichtIn hR.nichtReach
    | _ => simp only [nichtKopf, Bool.false_eq_true] at hk

/-! ### From the atom to `parsePredNot` and `parsePred` -/

/-- The `!`/`=>` level from the atom level: a print without `!` head, no `=>` behind. -/
theorem predNot_ohne (e : SExpr) (G : Nat) (R : List Token) (t : Token) (ts : List Token)
    (hd : druckToks e = t :: ts) (ht : t ≠ .zeichen "!")
    (hA : parsePredAtom G (druckToks e ++ R) = .ok (e, R)) (hR : ∀ r, R ≠ .zeichen "=>" :: r) :
    parsePredNot (G + 1) (druckToks e ++ R) = .ok (e, R) := by
  rw [hd, List.cons_append] at hA ⊢
  exact predNot_plain G t _ R e ht hA hR

/-- The same with `=>` behind: the implication. -/
theorem predNot_ohne_folgt (e b : SExpr) (G : Nat) (X r : List Token) (t : Token) (ts : List Token)
    (hd : druckToks e = t :: ts) (ht : t ≠ .zeichen "!")
    (hA : parsePredAtom G (druckToks e ++ .zeichen "=>" :: X) = .ok (e, .zeichen "=>" :: X))
    (hB : parsePred G X = .ok (b, r)) :
    parsePredNot (G + 1) (druckToks e ++ .zeichen "=>" :: X) = .ok (.ext .imp [] [e, b], r) := by
  rw [hd, List.cons_append] at hA ⊢
  cases t with
  | zeichen z =>
    have hz : ∀ r, Token.zeichen z :: (ts ++ .zeichen "=>" :: X) ≠ .zeichen "!" :: r := by
      intro r e; injection e with e1; exact ht (by rw [e1])
    simp only [parsePredNot, hz, hA, hB]
    simp only [Bool.false_eq_true, ↓reduceIte]
  | _ => simp only [parsePredNot, hA, hB]; simp only [Bool.false_eq_true, ↓reduceIte]

/-- A `!` tree from its atom part. -/
theorem predNot_mit (x : SExpr) (G : Nat) (R : List Token)
    (hA : parsePredAtom G (atomTeil (.un "!" x) ++ R) = .ok (x, R)) (hR : ∀ r, R ≠ .zeichen "=>" :: r) :
    parsePredNot (G + 1) (druckToks (.un "!" x) ++ R) = .ok (.un "!" x, R) := by
  rw [druck_nichtKopf _ (nichtKopf_un x), List.cons_append]
  exact predNot_bang G _ R x hA hR

theorem predNot_mit_folgt (x b : SExpr) (G : Nat) (X r : List Token)
    (hA : parsePredAtom G (atomTeil (.un "!" x) ++ .zeichen "=>" :: X) = .ok (x, .zeichen "=>" :: X))
    (hB : parsePred G X = .ok (b, r)) :
    parsePredNot (G + 1) (druckToks (.un "!" x) ++ .zeichen "=>" :: X) =
      .ok (.ext .imp [] [.un "!" x, b], r) := by
  rw [druck_nichtKopf _ (nichtKopf_un x), List.cons_append]
  simp only [parsePredNot, hA, ite_true, hB]

/-- The whole predicate reader from the `!`/`=>` level, before a predicate follow. -/
theorem pred_aus_not (e : SExpr) (G : Nat) (R : List Token) (hR : ruhig R = true)
    (hN : parsePredNot (G + 2) (druckToks e ++ R) = .ok (e, R)) :
    parsePred (G + 4) (druckToks e ++ R) = .ok (e, R) := by
  simp only [parsePred, parsePredAnd, hN, parsePredAndL, parsePredOrL, stopUnd R hR, stopOder R hR]

/-! ### Domains and the print of quantifiers -/

/-- The kinds of domain that take one place after `of`. -/
def ortArt (dk : String) : Prop :=
  dk = "slots" ∨ dk = "descendants" ∨ dk = "ancestors" ∨ dk = "elems" ∨ dk = "mappings"

/-- A printable domain: a kind with a place, `queue` a place, or `threads`. -/
inductive DomGut : String → List String → List SExpr → Prop
  | ort (dk : String) (p : SExpr) : ortArt dk → gutPlatz p = true → DomGut dk [] [p]
  | queue (p : SExpr) : gutPlatz p = true → DomGut "queue" [] [p]
  | threads : DomGut "threads" [] []

theorem domToks_ort (dk : String) (h : ortArt dk) (p : SExpr) :
    domToks dk [] (druckToksViele [p]) = .wort dk :: .wort "of" :: druckToks p := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem dom_rund (dk : String) (ns : List String) (ops : List SExpr) (h : DomGut dk ns ops) (X : List Token)
    (G : Nat) (hG : 8 * (domToks dk ns (druckToksViele ops)).length + 40 ≤ G) :
    parseDomain G (domToks dk ns (druckToksViele ops) ++ .zeichen ":" :: X) = .ok ((dk, ns, ops), .zeichen ":" :: X) := by
  cases h with
  | ort dk p hk hp =>
    rw [domToks_ort dk hk p] at hG ⊢
    simp only [List.length_cons] at hG
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 2 := ⟨G - 2, by omega⟩
    have hO := ortP p hp (.zeichen ":" :: X) G' rfl (by omega)
    rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      simp only [parseDomain, List.cons_append, domPlace, hO]
  | queue p hp =>
    have hd : domToks "queue" [] (druckToksViele [p]) = .wort "queue" :: druckToks p := rfl
    rw [hd] at hG ⊢
    simp only [List.length_cons] at hG
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 2 := ⟨G - 2, by omega⟩
    have hO := ortP p hp (.zeichen ":" :: X) G' rfl (by omega)
    simp only [parseDomain, List.cons_append, domPlace, hO]
  | threads =>
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hd : domToks "threads" [] (druckToksViele []) = [.wort "threads"] := rfl
    rw [hd]
    simp only [parseDomain, List.cons_append, List.nil_append]

theorem druckToksViele_append (xs : List SExpr) (y : SExpr) :
    druckToksViele (xs ++ [y]) = druckToksViele xs ++ [druckToks y] := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, druckToksViele, ih]

/-- The quantifier word of a kind. -/
def quantWort : XKind → String
  | .all => "forall"
  | .any => "exists"
  | _ => ""

/-- The print of a quantifier: in parentheses. -/
theorem quant_druck (k : XKind) (hk : k = .all ∨ k = .any) (x dk : String) (ns : List String)
    (ops : List SExpr) (body : SExpr) :
    druckToks (.ext k (x :: dk :: ns) (ops ++ [body])) =
      [.zeichen "(", .wort (quantWort k), nameTok x, .wort "in"] ++ domToks dk ns (druckToksViele ops) ++
        [.zeichen ":"] ++ druckToks body ++ [.zeichen ")"] := by
  rcases hk with rfl | rfl <;>
    simp only [druckToks, druckExtToks, druckExtToks.druckQuant, druckToksViele_append, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.reverse_reverse, List.append_assoc, quantWort]

theorem folgt_druck (a b : SExpr) :
    druckToks (.ext .imp [] [a, b]) = [.zeichen "("] ++ druckToks a ++ [.zeichen "=>"] ++ druckToks b ++ [.zeichen ")"] := by
  simp only [druckToks, druckExtToks, druckToksViele, List.cons_append, List.nil_append, List.append_assoc]

theorem quant_rund (k : XKind) (hk : k = .all ∨ k = .any) (x dk : String) (ns : List String)
    (ops : List SExpr) (body : SExpr) (R : List Token) (G : Nat)
    (hD : parseDomain G (domToks dk ns (druckToksViele ops) ++ .zeichen ":" :: (druckToks body ++ .zeichen ")" :: R)) =
      .ok ((dk, ns, ops), .zeichen ":" :: (druckToks body ++ .zeichen ")" :: R)))
    (hB : parsePred G (druckToks body ++ .zeichen ")" :: R) = .ok (body, .zeichen ")" :: R)) :
    parsePredAtom (G + 2) (.wort (quantWort k) :: nameTok x :: .wort "in" ::
      (domToks dk ns (druckToksViele ops) ++ .zeichen ":" :: (druckToks body ++ .zeichen ")" :: R))) =
      .ok (.ext k (x :: dk :: ns) (ops ++ [body]), .zeichen ")" :: R) := by
  have hQ : parseQuant (G + 1) k x (domToks dk ns (druckToksViele ops) ++ .zeichen ":" ::
      (druckToks body ++ .zeichen ")" :: R)) = .ok (.ext k (x :: dk :: ns) (ops ++ [body]), .zeichen ")" :: R) := by
    simp only [parseQuant, hD, hB]
  rcases hk with rfl | rfl
  · simp only [quantWort]; rw [parsePredAtom]; simp only [nameText_nameTok, hQ]
  · simp only [quantWort]; rw [parsePredAtom]; simp only [nameText_nameTok, hQ]

/-! ### Failing expression reads of the predicate-only forms -/

theorem unary_klammer (f : Nat) (T : List Token) :
    parseUnary (f + 1) (.zeichen "(" :: T) = parsePrimary f (.zeichen "(" :: T) := by
  have n1 : ("(" : String) ≠ "!" := by decide
  have n2 : ("(" : String) ≠ "-" := by decide
  have n3 : ("(" : String) ≠ "~" := by decide
  have n4 : ("(" : String) ≠ "&" := by decide
  simp only [parseUnary, List.cons.injEq, Token.zeichen.injEq, n1, false_and, imp_self, implies_true, n2, n3, n4]

theorem fehlt_prim_aus_unary {b : Nat} {T : List Token} (h : Fehlt parseUnary b (.zeichen "(" :: T)) :
    Fehlt parsePrimary b (.zeichen "(" :: T) := by
  intro f hf
  obtain ⟨m, hm⟩ := h (f + 1) (by omega)
  exact ⟨m, by rw [unary_klammer] at hm; exact hm⟩

theorem fehlt_unary_aus_prim {b : Nat} {T : List Token} (h : Fehlt parsePrimary b (.zeichen "(" :: T)) :
    Fehlt parseUnary (b + 1) (.zeichen "(" :: T) := by
  intro f hf
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  obtain ⟨m, hm⟩ := h f' (by omega)
  exact ⟨m, by rw [unary_klammer]; exact hm⟩

/-- `l && X` where the expression reader fails on `X`. -/
theorem und_fehlt (l : SExpr) (hl : gut l = true) (X : List Token) (c b : Nat) (hX : Fehlt parseCmp c X)
    (h1 : fb l + 9 ≤ b) (h2 : c + 3 ≤ b) : Fehlt parseOr b (druckToks l ++ .zeichen "&&" :: X) := by
  intro f hf
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 3 := ⟨f - 3, by omega⟩
  have hC := cmp_gut l hl (.zeichen "&&" :: X) (atomFolge_zeichen "&&" X (Or.inl rfl)) (g + 1) (by omega)
  obtain ⟨m, hm⟩ := hX g (by omega)
  exact ⟨m, by simp only [parseOr, parseAnd, hC, parseAndL, opUnd, hm]⟩

end Gabbro.Grammatik.Parser
