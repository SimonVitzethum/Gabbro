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
import Grammatik.Parser.Round.RundlaufPred

namespace Gabbro.Grammatik.Parser

set_option maxRecDepth 100000

/-! ### The comparison level before a follow that only stops it -/

/-- A follow the levels below `&&` stop at. -/
structure CmpStop (R : List Token) : Prop where
  vgl : opVgl R = none
  bit : opBit R = none
  add : opAdd R = none
  mul : opMul R = none

theorem cmpStop_ruhig (R : List Token) (h : ruhig R = true) : CmpStop R :=
  ⟨stopVgl R h, stopBit R h, stopAdd R h, stopMul R h⟩

theorem cmpStop_und (r : List Token) : CmpStop (.zeichen "&&" :: r) := ⟨rfl, rfl, rfl, rfl⟩
theorem cmpStop_oder (r : List Token) : CmpStop (.zeichen "||" :: r) := ⟨rfl, rfl, rfl, rfl⟩
theorem cmpStop_folgt (r : List Token) : CmpStop (.zeichen "=>" :: r) := ⟨rfl, rfl, rfl, rfl⟩

theorem cmp_aus_unary' (m : Nat) (x : SExpr) (T rest : List Token) (hs : CmpStop rest)
    (hU : ∀ G, m + 2 ≤ G → parseUnary G (T ++ rest) = .ok (x, rest)) :
    ∀ G, m + 6 ≤ G → parseCmp G (T ++ rest) = .ok (x, rest) := by
  have hM : ∀ G, m + 3 ≤ G → parseMul G (T ++ rest) = .ok (x, rest) := by
    intro G hG
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 2 := ⟨G - 2, by omega⟩
    have := hU (G' + 1) (by omega)
    simp only [parseMul, parseMulL, this, hs.mul]
  have hA : ∀ G, m + 4 ≤ G → parseAdd G (T ++ rest) = .ok (x, rest) := by
    intro G hG
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 2 := ⟨G - 2, by omega⟩
    have := hM (G' + 1) (by omega)
    simp only [parseAdd, parseAddL, this, hs.add]
  have hB : ∀ G, m + 5 ≤ G → parseBit G (T ++ rest) = .ok (x, rest) := by
    intro G hG
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 2 := ⟨G - 2, by omega⟩
    have := hA (G' + 1) (by omega)
    simp only [parseBit, parseBitL, this, hs.bit]
  intro G hG
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
  have := hB G' (by omega)
  simp only [parseCmp, this, hs.vgl]

/-! ### Errors climb the expression levels -/

/-- An error of a reader on a token list from fuel `b` on. -/
def Fehlt (P : Nat → List Token → Except String (SExpr × List Token)) (b : Nat) (T : List Token) : Prop :=
  ∀ f, b ≤ f → ∃ m, P f T = .error m

theorem fehlt_mul {b : Nat} {T : List Token} (h : Fehlt parseUnary b T) : Fehlt parseMul (b + 1) T := by
  intro f hf
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  obtain ⟨m, hm⟩ := h f' (by omega)
  exact ⟨m, by simp only [parseMul, hm]⟩

theorem fehlt_add {b : Nat} {T : List Token} (h : Fehlt parseMul b T) : Fehlt parseAdd (b + 1) T := by
  intro f hf
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  obtain ⟨m, hm⟩ := h f' (by omega)
  exact ⟨m, by simp only [parseAdd, hm]⟩

theorem fehlt_bit {b : Nat} {T : List Token} (h : Fehlt parseAdd b T) : Fehlt parseBit (b + 1) T := by
  intro f hf
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  obtain ⟨m, hm⟩ := h f' (by omega)
  exact ⟨m, by simp only [parseBit, hm]⟩

theorem fehlt_cmp {b : Nat} {T : List Token} (h : Fehlt parseBit b T) : Fehlt parseCmp (b + 1) T := by
  intro f hf
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  obtain ⟨m, hm⟩ := h f' (by omega)
  exact ⟨m, by simp only [parseCmp, hm]⟩

theorem fehlt_and {b : Nat} {T : List Token} (h : Fehlt parseCmp b T) : Fehlt parseAnd (b + 1) T := by
  intro f hf
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  obtain ⟨m, hm⟩ := h f' (by omega)
  exact ⟨m, by simp only [parseAnd, hm]⟩

theorem fehlt_or {b : Nat} {T : List Token} (h : Fehlt parseAnd b T) : Fehlt parseOr (b + 1) T := by
  intro f hf
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  obtain ⟨m, hm⟩ := h f' (by omega)
  exact ⟨m, by simp only [parseOr, hm]⟩

theorem fehlt_cmp_u {b : Nat} {T : List Token} (h : Fehlt parseUnary b T) : Fehlt parseCmp (b + 4) T :=
  fehlt_cmp (fehlt_bit (fehlt_add (fehlt_mul h)))

theorem fehlt_or_u {b : Nat} {T : List Token} (h : Fehlt parseUnary b T) : Fehlt parseOr (b + 6) T :=
  fehlt_or (fehlt_and (fehlt_cmp_u h))

/-- A parenthesis whose inside fails. -/
theorem fehlt_klammer {b : Nat} {T : List Token} (h : Fehlt parseOr b T) :
    Fehlt parseUnary (b + 2) (.zeichen "(" :: T) := by
  intro f hf
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 2 := ⟨f - 2, by omega⟩
  obtain ⟨m, hm⟩ := h f' (by omega)
  refine ⟨m, ?_⟩
  have n1 : ("(" : String) ≠ "!" := by decide
  have n2 : ("(" : String) ≠ "-" := by decide
  have n3 : ("(" : String) ≠ "~" := by decide
  have n4 : ("(" : String) ≠ "&" := by decide
  simp only [parseUnary, List.cons.injEq, Token.zeichen.injEq, n1, false_and, imp_self, implies_true, n2, n3, n4, parsePrimary, hm]

/-- `!` before a primary that fails. -/
theorem fehlt_nicht {b : Nat} {T : List Token} (h : Fehlt parsePrimary b T) :
    Fehlt parseUnary (b + 1) (.zeichen "!" :: T) := by
  intro f hf
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  obtain ⟨m, hm⟩ := h f' (by omega)
  exact ⟨m, by simp only [parseUnary, hm]⟩

theorem fehlt_prim_klammer {b : Nat} {T : List Token} (h : Fehlt parseOr b T) :
    Fehlt parsePrimary (b + 1) (.zeichen "(" :: T) := by
  intro f hf
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  obtain ⟨m, hm⟩ := h f' (by omega)
  exact ⟨m, by simp only [parsePrimary, hm]⟩

/-- A quantifier word heads no expression: every reader fails on it, whatever the fuel. -/
theorem fehlt_quant (w : String) (hw : w = "forall" ∨ w = "exists") (X : List Token) :
    Fehlt parseOr 0 (.wort w :: X) := by
  have hU : Fehlt parseUnary 0 (.wort w :: X) := by
    intro f _
    cases f with
    | zero => exact ⟨_, rfl⟩
    | succ f =>
      cases f with
      | zero => exact ⟨"out of fuel", by simp only [parseUnary, parsePrimary]⟩
      | succ f =>
        rcases hw with rfl | rfl
        · exact ⟨"reserved head forall", by simp [parseUnary, parsePrimary, nameText, istKeinPlatz, keinPlatzTafel]⟩
        · exact ⟨"reserved head exists", by simp [parseUnary, parsePrimary, nameText, istKeinPlatz, keinPlatzTafel]⟩
  have hM : Fehlt parseMul 0 (.wort w :: X) := by
    intro f _; cases f with
    | zero => exact ⟨_, rfl⟩
    | succ f => obtain ⟨m, hm⟩ := hU f (by omega); exact ⟨m, by simp only [parseMul, hm]⟩
  have hA : Fehlt parseAdd 0 (.wort w :: X) := by
    intro f _; cases f with
    | zero => exact ⟨_, rfl⟩
    | succ f => obtain ⟨m, hm⟩ := hM f (by omega); exact ⟨m, by simp only [parseAdd, hm]⟩
  have hB : Fehlt parseBit 0 (.wort w :: X) := by
    intro f _; cases f with
    | zero => exact ⟨_, rfl⟩
    | succ f => obtain ⟨m, hm⟩ := hA f (by omega); exact ⟨m, by simp only [parseBit, hm]⟩
  have hC : Fehlt parseCmp 0 (.wort w :: X) := by
    intro f _; cases f with
    | zero => exact ⟨_, rfl⟩
    | succ f => obtain ⟨m, hm⟩ := hB f (by omega); exact ⟨m, by simp only [parseCmp, hm]⟩
  have hN : Fehlt parseAnd 0 (.wort w :: X) := by
    intro f _; cases f with
    | zero => exact ⟨_, rfl⟩
    | succ f => obtain ⟨m, hm⟩ := hC f (by omega); exact ⟨m, by simp only [parseAnd, hm]⟩
  intro f _; cases f with
  | zero => exact ⟨_, rfl⟩
  | succ f => obtain ⟨m, hm⟩ := hN f (by omega); exact ⟨m, by simp only [parseOr, hm]⟩

theorem fehlt_mono {P : Nat → List Token → Except String (SExpr × List Token)} {b c : Nat} {T : List Token}
    (h : Fehlt P b T) (hc : b ≤ c) : Fehlt P c T := fun f hf => h f (by omega)

/-! ### Expressions at the atom level, before a follow that only stops the comparison -/

/-- What may follow a predicate atom: benign for the suffix and float readers, stopping the
    comparison level, and no `in`/`reaches` (which would extend the atom). -/
structure AtomFolge (R : List Token) : Prop where
  suff : ruhigSuff R = true
  gleit : ruhigGleit R = true
  cmp : CmpStop R
  nichtIn : ∀ r, R ≠ .wort "in" :: r
  nichtReach : ∀ r, R ≠ .wort "reaches" :: r

theorem atomFolge_pred (R : List Token) (h : PredFolge R) : AtomFolge R :=
  ⟨h.2.1, h.2.2.1, cmpStop_ruhig R h.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem atomFolge_zeichen (z : String) (r : List Token) (hz : z = "&&" ∨ z = "||" ∨ z = "=>" ∨ z = ")") :
    AtomFolge (.zeichen z :: r) := by
  rcases hz with rfl | rfl | rfl | rfl <;>
    exact ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, by simp only [ne_eq, List.cons.injEq, reduceCtorEq, false_and, not_false_eq_true, implies_true], by simp only [ne_eq, List.cons.injEq, reduceCtorEq, false_and, not_false_eq_true, implies_true]⟩

theorem predAtom_aus' (H : Nat) (toks rest : List Token) (e : SExpr)
    (hq : ∀ x r, toks ≠ .wort "forall" :: x :: .wort "in" :: r)
    (hq2 : ∀ x r, toks ≠ .wort "exists" :: x :: .wort "in" :: r)
    (hC : parseCmp H toks = .ok (e, rest)) (hin : ∀ r, rest ≠ .wort "in" :: r)
    (hre : ∀ r, rest ≠ .wort "reaches" :: r) :
    parsePredAtom (H + 1) toks = .ok (e, rest) := by
  rw [parsePredAtom.eq_def]
  simp only [hC]

/-- A printable expression at the comparison level before an atom follow. -/
theorem cmp_gut (e : SExpr) (hg : gut e = true) (R : List Token) (hR : AtomFolge R) (G : Nat)
    (hG : fb e + 6 ≤ G) : parseCmp G (druckToks e ++ R) = .ok (e, R) :=
  cmp_aus_unary' (fb e) e (druckToks e) R hR.cmp
    (fun G hG => (legs_tok e hg).2.1 R G hR.suff hR.gleit hG) G hG

/-- `( x )` at the comparison level before an atom follow. -/
theorem cmp_klammer' (x : SExpr) (hx : gut x = true) (R : List Token) (hR : CmpStop R)
    (G : Nat) (hG : fb x + 16 ≤ G) :
    parseCmp G (.zeichen "(" :: (druckToks x ++ .zeichen ")" :: R)) = .ok (x, R) := by
  have hU : ∀ G, fb x + 8 + 2 ≤ G →
      parseUnary G ([.zeichen "("] ++ (druckToks x ++ [.zeichen ")"]) ++ R) = .ok (x, R) := by
    intro G hG
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 2 := ⟨G - 2, by omega⟩
    have hO := (legs_tok x hx).2.2.2.2.2.2.2 ([.zeichen ")"] ++ R) G' (hr_paren R)
      (hrs_paren R) (hrg_paren R) (by omega)
    have hP := paren_arm _ _ _ _ hO
    have := un_paren_fall _ _ _ _ hP
    simpa only [List.append_assoc] using this
  have := cmp_aus_unary' (fb x + 8) x ([.zeichen "("] ++ (druckToks x ++ [.zeichen ")"])) R hR hU G
    (by omega)
  simpa only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] using this

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

theorem nichtKopf_ext (k : XKind) (ns : List String) (xs : List SExpr) : nichtKopf (.ext k ns xs) = false := rfl

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

theorem bein_und (l r : SExpr) (hl : PredBein l) (hr : PredBein r) : PredBein (.bin "&&" l r) := by
  by_cases hg : gut (.bin "&&" l r) = true
  · exact bein_expr _ hg
  · have hgf : gut (.bin "&&" l r) = false := by simpa using hg
    have hdr : druckToks (.bin "&&" l r) =
        .zeichen "(" :: (druckToks l ++ .zeichen "&&" :: (druckToks r ++ [.zeichen ")"])) := by
      simp only [druckToks, List.cons_append, List.nil_append, List.append_assoc]
    have hF : ∀ R, Fehlt parseUnary (bE (.bin "&&" l r)) (druckToks (.bin "&&" l r) ++ R) := by
      intro R
      rw [hdr]
      simp only [List.cons_append, List.append_assoc, List.singleton_append]
      have hL : (druckToks l).length ≥ 1 := by
        obtain ⟨t, ts, h, -⟩ := hl.kopf; rw [h]; simp only [List.length_cons, ge_iff_le, Nat.le_add_left]
      have hR' : (druckToks r).length ≥ 1 := by
        obtain ⟨t, ts, h, -⟩ := hr.kopf; rw [h]; simp only [List.length_cons, ge_iff_le, Nat.le_add_left]
      apply fehlt_mono (fehlt_klammer (b := bE (.bin "&&" l r) - 2) _)
      · simp only [bE]; omega
      · cases hgl : gut l with
        | false =>
          exact fehlt_mono (fehlt_or_u (hl.fehlt hgl _)) (by simp only [bE, hdr]; simp only [List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceSubDiff, Nat.add_le_add_iff_right, Nat.reduceLeDiff]; omega)
        | true =>
          have hgr : gut r = false := by
            cases hgr : gut r
            · rfl
            · have : gut (.bin "&&" l r) = true := by simp only [gut, hgl, hgr, Bool.and_true]; decide
              rw [this] at hgf; cases hgf
          exact und_fehlt l hgl _ _ _ (fehlt_cmp_u (hr.fehlt hgr _)) (by simp only [fb, bE, hdr]; simp only [List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceSubDiff, Nat.add_le_add_iff_right, Nat.reduceLeDiff]; omega)
            (by simp only [bE, hdr]; simp only [List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceSubDiff, Nat.add_le_add_iff_right, Nat.reduceLeDiff]; omega)
    refine ⟨?_, fun _ R => hF R, ⟨_, _, hdr, by simp only [Token.zeichen.injEq, String.reduceEq, false_implies], fun _ => Or.inl rfl⟩⟩
    intro R G hR hG
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by simp only [bP] at hG; omega⟩
    simp only [atomTeil, atomWert]
    obtain ⟨m, hm⟩ := fehlt_cmp_u (hF R) G' (by simp only [bP, bE] at hG ⊢; omega)
    simp only [bP] at hG
    rw [hdr] at hm hG ⊢
    simp only [List.cons_append, List.nil_append, List.append_assoc, List.singleton_append] at hm ⊢
    simp only [List.length_append, List.length_cons, List.length_nil] at hG
    obtain ⟨G5, rfl⟩ : ∃ G5, G' = G5 + 4 := ⟨G' - 4, by omega⟩
    exact atom_klammer _ _ R _ m hm (und_innen l r hl hr R G5 (by simp only [bP]; omega) (by simp only [bP]; omega))

theorem bein_oder (l r : SExpr) (hl : PredBein l) (hr : PredBein r) : PredBein (.bin "||" l r) := by
  by_cases hg : gut (.bin "||" l r) = true
  · exact bein_expr _ hg
  · have hgf : gut (.bin "||" l r) = false := by simpa using hg
    have hdr : druckToks (.bin "||" l r) =
        .zeichen "(" :: (druckToks l ++ .zeichen "||" :: (druckToks r ++ [.zeichen ")"])) := by
      simp only [druckToks, List.cons_append, List.nil_append, List.append_assoc]
    have hF : ∀ R, Fehlt parseUnary (bE (.bin "||" l r)) (druckToks (.bin "||" l r) ++ R) := by
      intro R
      rw [hdr]
      simp only [List.cons_append, List.append_assoc, List.singleton_append]
      have hL : (druckToks l).length ≥ 1 := by
        obtain ⟨t, ts, h, -⟩ := hl.kopf; rw [h]; simp only [List.length_cons, ge_iff_le, Nat.le_add_left]
      have hR' : (druckToks r).length ≥ 1 := by
        obtain ⟨t, ts, h, -⟩ := hr.kopf; rw [h]; simp only [List.length_cons, ge_iff_le, Nat.le_add_left]
      apply fehlt_mono (fehlt_klammer (b := bE (.bin "||" l r) - 2) _)
      · simp only [bE]; omega
      · cases hgl : gut l with
        | false =>
          exact fehlt_mono (fehlt_or_u (hl.fehlt hgl _)) (by simp only [bE, hdr]; simp only [List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceSubDiff, Nat.add_le_add_iff_right, Nat.reduceLeDiff]; omega)
        | true =>
          have hgr : gut r = false := by
            cases hgr : gut r
            · rfl
            · have : gut (.bin "||" l r) = true := by simp only [gut, hgl, hgr, Bool.and_true]; decide
              rw [this] at hgf; cases hgf
          exact oder_fehlt l hgl _ _ _ (fehlt_and (fehlt_cmp_u (hr.fehlt hgr _)))
            (by simp only [fb, bE, hdr]; simp only [List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceSubDiff, Nat.add_le_add_iff_right, Nat.reduceLeDiff]; omega) (by simp only [bE, hdr]; simp only [List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceSubDiff, Nat.add_le_add_iff_right, Nat.reduceLeDiff]; omega)
    refine ⟨?_, fun _ R => hF R, ⟨_, _, hdr, by simp only [Token.zeichen.injEq, String.reduceEq, false_implies], fun _ => Or.inl rfl⟩⟩
    intro R G hR hG
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by simp only [bP] at hG; omega⟩
    simp only [atomTeil, atomWert]
    obtain ⟨m, hm⟩ := fehlt_cmp_u (hF R) G' (by simp only [bP, bE] at hG ⊢; omega)
    simp only [bP] at hG
    rw [hdr] at hm hG ⊢
    simp only [List.cons_append, List.nil_append, List.append_assoc, List.singleton_append] at hm ⊢
    simp only [List.length_append, List.length_cons, List.length_nil] at hG
    obtain ⟨G5, rfl⟩ : ∃ G5, G' = G5 + 4 := ⟨G' - 4, by omega⟩
    exact atom_klammer _ _ R _ m hm (oder_innen l r hl hr R G5 (by simp only [bP]; omega) (by simp only [bP]; omega))

theorem bein_nicht (x : SExpr) (hx : PredBein x) : PredBein (.un "!" x) := by
  by_cases hg : gut (.un "!" x) = true
  · exact bein_expr _ hg
  · have hgx : gut x = false := by
      cases h : gut x
      · rfl
      · exact absurd (by simp only [gut, h, Bool.and_true, strEq_bang_klammer, Bool.false_and, Bool.or_false]; decide) hg
    have hdr := druck_nichtKopf _ (nichtKopf_un x)
    have hW : atomWert (.un "!" x) = x := by simp only [atomWert, strEq_self, ↓reduceIte]
    obtain ⟨t, ts, hxd, hxb, hxk⟩ := hx.kopf
    have hlen : (druckToks x).length + 1 ≤ (druckToks (.un "!" x)).length := by
      cases ha : istAtom x <;> simp only [druckToks, strEq_bang_klammer, Bool.false_eq_true, ↓reduceIte, ha, List.cons_append, List.nil_append, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.add_le_add_iff_right, Nat.le_add_right, Std.le_refl]
    refine ⟨?_, ?_, ⟨_, _, hdr, fun _ => nichtKopf_un x, fun _ => Or.inr rfl⟩⟩
    · intro R G hR hG
      rw [hW]
      cases ha : istAtom x with
      | true =>
        have hnk : nichtKopf x = false := by cases x <;> simp_all [istAtom, nichtKopf]
        obtain ⟨h1, h2⟩ := atom_nicht_nichtKopf x hnk
        have := hx.atom R G hR (by simp only [bP] at hG ⊢; omega)
        rw [h1, h2] at this
        simpa [atomTeil, strEq_self, ha] using this
      | false =>
        simp only [atomTeil, strEq_self, ite_true, ha, Bool.false_eq_true, ite_false, List.cons_append,
          List.nil_append, List.append_assoc, List.singleton_append]
        obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by simp only [bP] at hG; omega⟩
        have hF : Fehlt parseCmp (bE x + 12) (.zeichen "(" :: (druckToks x ++ .zeichen ")" :: R)) :=
          fehlt_cmp_u (fehlt_klammer (fehlt_or_u (hx.fehlt hgx (.zeichen ")" :: R))))
        obtain ⟨m, hm⟩ := hF G' (by simp only [bP, bE] at hG ⊢; omega)
        exact atom_klammer _ _ R _ m hm (bein_top x hx (.zeichen ")" :: R) G'
          ⟨rfl, rfl, rfl, by simp only [ne_eq, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, not_false_eq_true, implies_true], by simp only [ne_eq, List.cons.injEq, reduceCtorEq, false_and, not_false_eq_true, implies_true], by simp only [ne_eq, List.cons.injEq, reduceCtorEq, false_and, not_false_eq_true, implies_true]⟩ (by simp only [bP] at hG ⊢; omega))
    · intro _ R
      rw [hdr, List.cons_append]
      apply fehlt_mono (fehlt_nicht (b := bE x + 7) _) (by simp only [bE]; omega)
      cases ha : istAtom x with
      | true =>
        have ht : t = .zeichen "(" := by
          rcases hxk hgx with h | h
          · exact h
          · have := hxb h
            cases x <;> simp_all [istAtom, nichtKopf]
        simp only [atomTeil, strEq_self, ite_true, ha]
        have h0 := hx.fehlt hgx R
        rw [hxd, ht, List.cons_append] at h0
        rw [hxd, ht, List.cons_append]
        exact fehlt_mono (fehlt_prim_aus_unary h0) (by omega)
      | false =>
        simp only [atomTeil, strEq_self, ite_true, ha, Bool.false_eq_true, ite_false, List.cons_append,
          List.nil_append, List.append_assoc, List.singleton_append]
        exact fehlt_mono (fehlt_prim_klammer (fehlt_or_u (hx.fehlt hgx (.zeichen ")" :: R)))) (by omega)

theorem bein_folgt (a b : SExpr) (ha : PredBein a) (hb : PredBein b) : PredBein (.ext .imp [] [a, b]) := by
  have hdr := folgt_druck a b
  have hgf : gut (.ext .imp [] [a, b]) = false := rfl
  have hL : (druckToks a).length ≥ 1 := by
    obtain ⟨t, ts, h, -⟩ := ha.kopf; rw [h]; simp only [List.length_cons, ge_iff_le, Nat.le_add_left]
  have hF : ∀ R, Fehlt parseUnary (bE (.ext .imp [] [a, b])) (druckToks (.ext .imp [] [a, b]) ++ R) := by
    intro R
    rw [hdr]
    simp only [List.cons_append, List.nil_append, List.append_assoc, List.singleton_append]
    have hX : gut a = true ∨ Fehlt parseOr (bE a + 6) (druckToks a ++ .zeichen "=>" ::
        (druckToks b ++ .zeichen ")" :: R)) := by
      cases hga : gut a with
      | true => exact Or.inl rfl
      | false => exact Or.inr (fehlt_or_u (ha.fehlt hga _))
    apply fehlt_mono (fehlt_unary_aus_prim (folgt_fehlt a _ (bE a + 6) (bE (.ext .imp [] [a, b]) - 1) hX
      (by simp only [fb, bE, hdr]; simp only [List.cons_append, List.nil_append, List.append_assoc, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.add_one_sub_one, Nat.add_le_add_iff_right, Nat.reduceLeDiff]; omega) (by simp only [bE, hdr]; simp only [List.cons_append, List.nil_append, List.append_assoc, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.add_one_sub_one, Nat.add_le_add_iff_right, Nat.reduceLeDiff]; omega)))
    simp only [bE]; omega
  refine ⟨?_, fun _ R => hF R, ⟨_, _, hdr, by simp only [Token.zeichen.injEq, String.reduceEq, false_implies], fun _ => Or.inl rfl⟩⟩
  intro R G hR hG
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by simp only [bP] at hG; omega⟩
  simp only [atomTeil, atomWert]
  obtain ⟨m, hm⟩ := fehlt_cmp_u (hF R) G' (by simp only [bP, bE] at hG ⊢; omega)
  simp only [bP] at hG
  rw [hdr] at hm hG ⊢
  simp only [List.cons_append, List.nil_append, List.append_assoc, List.singleton_append] at hm ⊢
  simp only [List.length_append, List.length_cons, List.length_nil] at hG
  obtain ⟨G5, rfl⟩ : ∃ G5, G' = G5 + 4 := ⟨G' - 4, by omega⟩
  exact atom_klammer _ _ R _ m hm (folgt_innen a b ha hb R G5 (by simp only [bP]; omega) (by simp only [bP]; omega))

/-- **The induction**: every printable predicate has its legs. -/
theorem pred_bein : ∀ (e : SExpr), PredGut e → PredBein e := by
  intro e h
  induction h with
  | expr e hg => exact bein_expr e hg
  | quant k x dk ns ops body hk hd _ ih => exact bein_quant k hk x dk ns ops hd body ih
  | und l r _ _ ihl ihr => exact bein_und l r ihl ihr
  | oder l r _ _ ihl ihr => exact bein_oder l r ihl ihr
  | nicht x _ ih => exact bein_nicht x ih
  | folgt a b _ _ iha ihb => exact bein_folgt a b iha ihb

/-- **Predicates with quantifiers read back** through `parsePred`, before a predicate follow. -/
theorem pred_voll (e : SExpr) (h : PredGut e) (R : List Token) (hR : PredFolge R) (F : Nat)
    (hF : bP e + 4 ≤ F) : parsePred F (druckToks e ++ R) = .ok (e, R) :=
  bein_top e (pred_bein e h) R F hR hF

/-! ### Witness -/

/-- `(!(exists k in queue Q : true) => ((forall s in descendants of b.kinder : s >= 0) || x))`:
    an implication over a negated `exists`, a `||` over a `forall`, a `queue` and a place domain. -/
def zeugePred : SExpr :=
  .ext .imp [] [.un "!" (.ext .any ["k", "queue"] [.variable "Q", .tru]),
    .bin "||" (.ext .all ["s", "descendants"] [.field (.variable "b") "kinder", .bin ">=" (.variable "s") (.lit 0)])
      (.variable "x")]

theorem zeugePred_gut : PredGut zeugePred :=
  .folgt _ _ (.nicht _ (.quant .any "k" "queue" [] [.variable "Q"] _ (Or.inr rfl) (.queue _ (by decide))
      (.expr _ (by decide))))
    (.oder _ _ (.quant .all "s" "descendants" [] [.field (.variable "b") "kinder"] _ (Or.inl rfl)
      (.ort _ _ (Or.inr (Or.inl rfl)) (by decide)) (.expr _ (by decide))) (.expr _ (by decide)))

/-- The witness reads back through the predicate reader. -/
theorem zeugePred_rund : parsePred 400 (druckToks zeugePred ++ [.ende]) = .ok (zeugePred, [.ende]) :=
  pred_voll zeugePred zeugePred_gut [.ende] ⟨rfl, rfl, rfl, by simp only [ne_eq, List.cons.injEq, reduceCtorEq, List.nil_eq, false_and, not_false_eq_true, implies_true], by simp only [ne_eq, List.cons.injEq, reduceCtorEq, List.nil_eq, false_and, not_false_eq_true, implies_true], by simp only [ne_eq, List.cons.injEq, reduceCtorEq, List.nil_eq, false_and, not_false_eq_true, implies_true]⟩ 400 (by decide)

/-- Its rendered text lexes back to its tokens (so the reader sees the same list). -/
theorem zeugePred_text : lex (renderText (druckToks zeugePred)) = .ok (druckToks zeugePred ++ [.ende]) :=
  lex_render _ (tokGut_of_all _ (by decide))

end Gabbro.Grammatik.Parser

#print axioms Gabbro.Grammatik.Parser.pred_voll
#print axioms Gabbro.Grammatik.Parser.zeugePred_rund
#print axioms Gabbro.Grammatik.Parser.zeugePred_text

/-
  CUTS: what the predicate round trip does not cover, and why.

  * `count x in D : p`: the reader takes `count` at the primary level (`parsePrimary`), so it is an
    expression form that nests inside comparisons; it needs its own leg in the expression towers
    (`LegsB`), not a predicate leg.
  * `e in D` and `a reaches b via f` (`ext .mem`, `ext .reach`): the reader takes them behind a
    comparison (`parsePredAtom` after `parseCmp`); a further `PredGut` case each, with the
    comparison leg before `in`/`reaches`.
  * The domains `fields of` a path and `chain (x, y) in` a place: two more `DomGut` cases.
-/
