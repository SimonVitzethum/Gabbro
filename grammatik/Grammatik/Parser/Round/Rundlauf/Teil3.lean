module

public import Grammatik.Parser.Expr.Ausdruck
public import Grammatik.Parser.Stmt.Anweisung
public import Grammatik.Parser.Lex.WortStellung
import all Init.Data.Repr
import all Init.Data.String.Defs
public import Grammatik.Parser.Round.Rundlauf.Teil2

@[expose] public section

namespace Gabbro.Grammatik.Parser

-- Every printed tree is a non-empty token list (the argument-label
-- strip of `parseArg` fires only on a `name :` prefix, and the
-- empty-print case below would leave it facing the separator).
theorem toksLang : ∀ (n : Nat) (e : SExpr),
    groesse e ≤ n → 1 ≤ (druckToks e).length := by
  intro n
  induction n with
  | zero =>
    intro e hs
    have hp := groesse_pos e
    omega
  | succ n ih =>
    intro e hs
    cases e with
    | lit m => exact Nat.le_refl _
    | float s => exact Nat.le_refl _
    | tru => exact Nat.le_refl _
    | fls => exact Nat.le_refl _
    | «variable» s => exact Nat.le_refl _
    | field x f =>
      have hx : groesse x ≤ n := by
        simp only [groesse] at hs
        omega
      have hlen := ih x hx
      simp only [druckToks, List.length_append, List.length] at ⊢
      omega
    | index x i =>
      have hx : groesse x ≤ n := by
        simp only [groesse] at hs
        omega
      have hlen := ih x hx
      simp only [druckToks, List.length_append, List.length] at ⊢
      omega
    | arrow x f =>
      have hx : groesse x ≤ n := by
        simp only [groesse] at hs
        omega
      have hlen := ih x hx
      simp only [druckToks, List.length_append, List.length] at ⊢
      omega
    | un o x =>
      simp only [druckToks] at ⊢
      split
      · simp only [List.length_append, List.length] at ⊢
        have hx : groesse x ≤ n := by
          simp only [groesse] at hs
          omega
        have hlen := ih x hx
        omega
      · simp only [List.length_append, List.length] at ⊢
        omega
    | bin o l r =>
      have hl : groesse l ≤ n := by
        simp only [groesse] at hs
        omega
      have hlen := ih l hl
      simp only [druckToks, List.length_append, List.length] at ⊢
      omega
    | call f xs =>
      simp only [druckToks, List.length_append,
        List.length] at ⊢
      omega
    | fnref p =>
      simp only [druckToks, List.length] at ⊢
      omega
    | built f xs =>
      simp only [druckToks, List.length_append,
        List.length] at ⊢
      omega
    | old x =>
      have hx : groesse x ≤ n := by
        simp only [groesse] at hs
        omega
      have hlen := ih x hx
      simp only [druckToks, List.length_append, List.length] at ⊢
      omega
    | res => exact Nat.le_refl _
    | why g f =>
      simp only [druckToks, List.length] at ⊢
      omega
    | ext xk xn xs =>
      have hl : 0 < (druckExtToks xk xn (druckToksViele xs)).length :=
        List.length_pos_iff.mpr (druckExtToks_ne_nil _ _ _)
      simp only [druckToks, groesse]
      omega

-- An element is no bigger than its list.
theorem groesse_mem_le : ∀ (xs : List SExpr) (x : SExpr),
    x ∈ xs → groesse x ≤ groesseListe xs := by
  intro xs
  induction xs with
  | nil =>
    intro x hm
    simp only [List.not_mem_nil] at hm
  | cons y ys ih =>
    intro x hm
    simp only [List.mem_cons] at hm
    obtain hxy | hm2 := hm
    · subst hxy
      simp only [groesseListe]
      omega
    · simp only [groesseListe]
      have := ih x hm2
      omega

-- A `gut` element stays `gut` in its list.
theorem gutListe_mem : ∀ (xs : List SExpr) (x : SExpr),
    x ∈ xs → gutListe xs = true → gut x = true := by
  intro xs
  induction xs with
  | nil =>
    intro x hm _
    simp only [List.not_mem_nil] at hm
  | cons y ys ih =>
    intro x hm hxs
    simp only [List.mem_cons] at hm
    simp only [gutListe, Bool.and_eq_true] at hxs
    obtain hxy | hm2 := hm
    · subst hxy
      exact hxs.1
    · exact ih x hm2 hxs.2

-- A `gutPlatz` tree is `gut` (every place shape checks the same
-- names; places only exclude more).
theorem gut_of_gutPlatz : ∀ (x : SExpr),
    gutPlatz x = true → gut x = true := by
  intro x h
  cases x with
  | lit m => simp only [gutPlatz, Bool.false_eq_true] at h
  | float s => simp only [gutPlatz, Bool.false_eq_true] at h
  | tru => simp only [gutPlatz, Bool.false_eq_true] at h
  | fls => simp only [gutPlatz, Bool.false_eq_true] at h
  | «variable» s =>
    simp only [gutPlatz] at h
    simp only [gut] at ⊢
    exact h
  | field x f =>
    simp only [gutPlatz] at h
    simp only [gut] at ⊢
    exact h
  | index x i =>
    simp only [gutPlatz, Bool.and_eq_true] at h
    simp only [gut, Bool.and_eq_true] at ⊢
    exact h
  | arrow x f =>
    simp only [gutPlatz] at h
    simp only [gut] at ⊢
    exact h
  | un o x => simp only [gutPlatz, Bool.false_eq_true] at h
  | bin o l r => simp only [gutPlatz, Bool.false_eq_true] at h
  | call f xs => simp only [gutPlatz, Bool.false_eq_true] at h
  | fnref f => simp only [gutPlatz, Bool.false_eq_true] at h
  | built f xs => simp only [gutPlatz, Bool.false_eq_true] at h
  | old x => simp only [gutPlatz, Bool.false_eq_true] at h
  | res => simp only [gutPlatz, Bool.false_eq_true] at h
  | why g f => simp only [gutPlatz, Bool.false_eq_true] at h
  | ext xk xn xs => simp only [gutPlatz, Bool.false_eq_true] at h

/-- The printable `ext` trees are the calls through a place: a suffixed place, then the arguments. -/
theorem gut_ruf_faelle (k : XKind) (ns : List String) (xs : List SExpr) (h : gut (.ext k ns xs) = true) :
    k = .call ∧ ns = [] ∧ ∃ c ys, xs = c :: ys ∧ gutPlatz c = true ∧ istVar c = false ∧
      gutListe ys = true := by
  cases k with
  | call =>
    cases ns with
    | cons _ _ => simp only [gut, Bool.false_eq_true] at h
    | nil =>
      cases xs with
      | nil => simp only [gut, gutOrtRuf, Bool.false_eq_true] at h
      | cons c ys =>
        simp only [gut, gutOrtRuf, Bool.and_eq_true, Bool.not_eq_true'] at h
        exact ⟨rfl, rfl, c, ys, rfl, h.1.1, h.1.2, h.2⟩
  | _ => simp only [gut, Bool.false_eq_true] at h

/-- Printed operands, comma separated, are the printed list. -/
theorem kommaToks_viele : ∀ (ys : List SExpr), kommaToks (druckToksViele ys) = druckToksListe ys
  | [] => rfl
  | [_] => rfl
  | y :: z :: zs => by
    have ih := kommaToks_viele (z :: zs)
    simp only [druckToksViele] at ih ⊢
    simp only [kommaToks, druckToksListe, ih]

/-- The print of a call through a place: the place, then the parenthesised arguments. -/
theorem druck_ruf (c : SExpr) (ys : List SExpr) :
    druckToks (.ext .call [] (c :: ys)) =
      druckToks c ++ ([.zeichen "("] ++ druckToksListe ys ++ [.zeichen ")"]) := by
  simp only [druckToks, druckToksViele, druckExtToks, kommaToks_viele, List.append_assoc]

-- Head and tail of a `gut` list stay `gut`.
theorem gutListe_Kopf : ∀ (x : SExpr) (xs : List SExpr),
    gutListe (x :: xs) = true → gut x = true := by
  intro x xs h
  simp only [gutListe, Bool.and_eq_true] at h
  exact h.1
theorem gutListe_Schwanz : ∀ (x : SExpr) (xs : List SExpr),
    gutListe (x :: xs) = true → gutListe xs = true := by
  intro x xs h
  simp only [gutListe, Bool.and_eq_true] at h
  exact h.2

-- Unfolding equations for printed argument lists, as plain
-- rewrite rules (kernel-checked, no equation-lemma matching).
theorem args_einzeln : ∀ (x : SExpr),
    druckToksListe [x] = druckToks x := by
  intro x
  rfl
theorem args_cons : ∀ (x y : SExpr) (ys : List SExpr),
    druckToksListe (x :: y :: ys) =
      druckToks x ++ [.zeichen ","] ++ druckToksListe (y :: ys) := by
  intro x y ys
  rfl

-- No `:` in printed argument lists, from no-`:` in printed
-- elements (plain list induction; the tree fact arrives as a
-- premise, so nothing here recurses into trees).
theorem keinDP_list : ∀ (n : Nat)
    (eP : ∀ (e : SExpr), groesse e ≤ n → gut e = true →
      ∀ (t : Token), t ∈ druckToks e → t ≠ .zeichen ":")
    (xs : List SExpr), groesseListe xs ≤ n → gutListe xs = true →
    ∀ (t : Token), t ∈ druckToksListe xs → t ≠ .zeichen ":" := by
  intro n eP xs
  induction xs with
  | nil =>
    intro hs hg t hm
    simp only [druckToksListe, List.not_mem_nil] at hm
  | cons x zs ihzs =>
    intro hs hg t hm
    cases zs with
    | nil =>
      rw [args_einzeln] at hm
      have hx : groesse x ≤ n := by
        simp only [groesseListe] at hs
        omega
      exact eP x hx (gutListe_Kopf x [] hg) t hm
    | cons y ys =>
      rw [args_cons] at hm
      rw [List.mem_append] at hm
      obtain hmL | hmR := hm
      · rw [List.mem_append] at hmL
        obtain hm1 | hm2 := hmL
        · have hx : groesse x ≤ n := by
            simp only [groesseListe] at hs
            omega
          exact eP x hx (gutListe_Kopf x (y :: ys) hg) t hm1
        · rw [List.mem_singleton] at hm2
          subst hm2
          intro h
          simp only [Token.zeichen.injEq, String.reduceEq] at h
      · have hzs : groesseListe (y :: ys) ≤ n := by
          simp only [groesseListe] at hs ⊢
          omega
        exact ihzs hzs (gutListe_Schwanz x (y :: ys) hg) t hmR

-- Shape equations for `built` printability, as plain rewrite
-- rules (kernel-checked; the `gut` match has literal and shape
-- arms that `simp` equations do not select).
theorem gut_sizeof_one : ∀ (x : SExpr),
    gut (.built "sizeof" [x]) = (gutPlatz x && (!istTypWortVar x)) := by
  intro x
  rfl
theorem gut_sizeof_multi : ∀ (x y : SExpr) (ys : List SExpr),
    gut (.built "sizeof" (x :: y :: ys)) = false := by
  intro x y ys
  rfl
theorem gut_lenof_one : ∀ (x : SExpr),
    gut (.built "lenof" [x]) = (gutPlatz x && (!istTypWortVar x)) := by
  intro x
  rfl
theorem gut_lenof_multi : ∀ (x y : SExpr) (ys : List SExpr),
    gut (.built "lenof" (x :: y :: ys)) = false := by
  intro x y ys
  rfl
theorem gut_aligned_one : ∀ (a : SExpr),
    gut (.built "aligned" [a]) = false := by
  intro a
  rfl
theorem gut_aligned_two : ∀ (a b : SExpr),
    gut (.built "aligned" [a, b]) = (gut a && gut b) := by
  intro a b
  rfl
theorem gut_aligned_multi : ∀ (a b c : SExpr) (xs : List SExpr),
    gut (.built "aligned" (a :: b :: c :: xs)) = false := by
  intro a b c xs
  rfl

end Gabbro.Grammatik.Parser
