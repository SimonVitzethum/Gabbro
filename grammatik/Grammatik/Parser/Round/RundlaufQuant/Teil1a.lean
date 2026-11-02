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

public import Grammatik.Parser.Round.Statements.RundlaufPred

@[expose] public section



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

end Gabbro.Grammatik.Parser
