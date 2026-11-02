module

public import Grammatik.Parser.Round.Rundlauf.Teil6a

public import Grammatik.Parser.Expr.Ausdruck
public import Grammatik.Parser.Stmt.Anweisung
public import Grammatik.Parser.Lex.WortStellung
import all Init.Data.Repr
import all Init.Data.String.Defs
public import Grammatik.Parser.Round.Rundlauf.Teil5

@[expose] public section

namespace Gabbro.Grammatik.Parser
-- `sammleSegmente` never consumes a suffix chain (fragments start
-- with `.`, `->`, `[`, never `::`; the tail is benign).
theorem sammleSeg_suffToks : ∀ (suff : List SuffFrag) (segs : List String)
    (rest : List Token),
    ruhigSuff rest = true →
    sammleSegmente (suffToks suff ++ rest) segs =
      (segs, suffToks suff ++ rest) := by
  intro suff
  induction suff with
  | nil =>
    intro segs rest hr
    simp only [suffToks, List.nil_append] at ⊢
    exact sammleSeg_stop segs rest hr
  | cons frag suff ih =>
    cases frag with
    | dot f => intro segs rest hr; rfl
    | arrow f => intro segs rest hr; rfl
    | idx i => intro segs rest hr; rfl

-- A suffix chain followed by a benign tail never starts with `(`.
theorem suffToks_nopar : ∀ (suff : List SuffFrag) (rest R : List Token),
    ruhigSuff rest = true →
    suffToks suff ++ rest ≠ .zeichen "(" :: R := by
  intro suff
  induction suff with
  | nil =>
    intro rest R hr hcon
    simp only [suffToks, List.nil_append] at hcon
    exact ruhigSuff_nopar rest hr R hcon
  | cons frag suff ih =>
    cases frag with
    | dot f =>
      intro rest R hr hcon
      simp only [suffToks, List.cons_append] at hcon
      simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at hcon
    | arrow f =>
      intro rest R hr hcon
      simp only [suffToks, List.cons_append] at hcon
      simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at hcon
    | idx i =>
      intro rest R hr hcon
      simp only [suffToks, List.cons_append] at hcon
      simp only [List.append_assoc, List.cons_append, List.nil_append, List.cons.injEq, Token.zeichen.injEq,
  String.reduceEq, false_and] at hcon

-- Every `gutPlatz` tree is a head variable plus fragments, with a
-- lawful head and lawful index payloads. By size induction.
theorem zerlege : ∀ (n : Nat) (p : SExpr), groesse p ≤ n →
    gutPlatz p = true →
    ∃ (a : String) (suff : List SuffFrag),
      p = applySuff (.variable a) suff ∧
      (!istKopfWort a) = true ∧
      suffGut suff = true ∧
      suffGroesse suff + 1 ≤ n := by
  intro n
  induction n with
  | zero =>
    intro p hs _
    have hp := groesse_pos p
    omega
  | succ n ih =>
    intro p hs hg
    cases p with
    | lit m => simp only [gutPlatz, Bool.false_eq_true] at hg
    | float s => simp only [gutPlatz, Bool.false_eq_true] at hg
    | tru => simp only [gutPlatz, Bool.false_eq_true] at hg
    | fls => simp only [gutPlatz, Bool.false_eq_true] at hg
    | «variable» a =>
      simp only [gutPlatz] at hg
      exact ⟨a, [], rfl, hg, rfl, by simp only [suffGroesse]; omega⟩
    | field x f =>
      simp only [gutPlatz] at hg
      have hx : groesse x ≤ n := by
        simp only [groesse] at hs
        omega
      obtain ⟨a, suff, rfl, hka, hgs, hsz⟩ := ih x hx hg
      refine ⟨a, suff ++ [.dot f], ?_, hka, ?_, ?_⟩
      · rw [applySuff_append]
        rfl
      · have hsg : suffGut (suff ++ [.dot f]) = suffGut suff := by
          simp only [suffGut_append, suffGut, Bool.and_true]
        rw [hsg]
        exact hgs
      · simp only [suffGroesse_append, suffGroesse] at ⊢
        omega
    | index x i =>
      simp only [gutPlatz, Bool.and_eq_true] at hg
      obtain ⟨hpx, hi⟩ := hg
      have hx : groesse x ≤ n := by
        simp only [groesse] at hs
        omega
      obtain ⟨a, suff, rfl, hka, hgs, hsz⟩ := ih x hx hpx
      refine ⟨a, suff ++ [.idx i], ?_, hka, ?_, ?_⟩
      · rw [applySuff_append]
        rfl
      · have hgi : gut i = true := hi
        have hsg : suffGut (suff ++ [.idx i]) = (suffGut suff && gut i) := by
          simp only [suffGut_append, suffGut, Bool.and_true]
        rw [hsg]
        simp only [hgs, hgi, Bool.and_self]
      · simp only [suffGroesse_append, suffGroesse] at ⊢
        simp only [groesse, groesse_applySuff] at hs
        omega
    | arrow x f =>
      simp only [gutPlatz] at hg
      have hx : groesse x ≤ n := by
        simp only [groesse] at hs
        omega
      obtain ⟨a, suff, rfl, hka, hgs, hsz⟩ := ih x hx hg
      refine ⟨a, suff ++ [.arrow f], ?_, hka, ?_, ?_⟩
      · rw [applySuff_append]
        rfl
      · have hsg : suffGut (suff ++ [.arrow f]) = suffGut suff := by
          simp only [suffGut_append, suffGut, Bool.and_true]
        rw [hsg]
        exact hgs
      · simp only [suffGroesse_append, suffGroesse] at ⊢
        omega
    | un o x => simp only [gutPlatz, Bool.false_eq_true] at hg
    | bin o l r => simp only [gutPlatz, Bool.false_eq_true] at hg
    | call f xs => simp only [gutPlatz, Bool.false_eq_true] at hg
    | fnref f => simp only [gutPlatz, Bool.false_eq_true] at hg
    | built f xs => simp only [gutPlatz, Bool.false_eq_true] at hg
    | old x => simp only [gutPlatz, Bool.false_eq_true] at hg
    | res => simp only [gutPlatz, Bool.false_eq_true] at hg
    | why g f => simp only [gutPlatz, Bool.false_eq_true] at hg
    | ext xk xn xs => simp only [gutPlatz, Bool.false_eq_true] at hg

-- Suffix chains through `parseSuffixe`, by list induction. Index
-- payloads parse via `R n` (smaller); fuel carries one spare per
-- fragment (`suff.length`) over the linear bound, so every strip
-- and every child is covered.
theorem suff_rund : ∀ (n : Nat) (Rn : R n)
    (suff : List SuffFrag) (base : SExpr) (rest : List Token) (F : Nat),
    suffGroesse suff + groesse base ≤ n + 1 →
    suffGut suff = true →
    ruhigSuff rest = true →
    12 * (suffGroesse suff + groesse base + 1) + suffGroesse suff ≤ F →
    parseSuffixe F base (suffToks suff ++ rest) =
      .ok (applySuff base suff, rest) := by
  intro n Rn suff
  induction suff with
  | nil =>
    intro base rest F hs hg hr hF
    have hF1 : 1 ≤ F := by omega
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [suffToks, List.nil_append] at ⊢
    exact stopSuffix F' base rest hr
  | cons frag suff ih =>
    cases frag with
    | dot f =>
      intro base rest F hs hg hr hF
      simp only [suffGut] at hg
      have hF1 : 1 ≤ F := by omega
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      simp only [suffToks, List.cons_append] at ⊢
      simp only [parseSuffixe, nameText_nameTok] at ⊢
      -- ⊢ : parseSuffixe F' (feld base f) (suffToks suff ++ rest) = ...
      simp only [applySuff] at ⊢
      have hs2 : suffGroesse suff + groesse (.field base f) ≤ n + 1 := by
        simp only [suffGroesse, groesse] at hs ⊢
        omega
      have hF2 : 12 * (suffGroesse suff + groesse (.field base f) + 1) +
          suffGroesse suff ≤ F' := by
        simp only [suffGroesse, groesse] at hs hF ⊢
        omega
      exact ih (SExpr.field base f) rest F' hs2 hg hr hF2
    | arrow f =>
      intro base rest F hs hg hr hF
      simp only [suffGut] at hg
      have hF1 : 1 ≤ F := by omega
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      simp only [suffToks, List.cons_append] at ⊢
      simp only [parseSuffixe, nameText_nameTok] at ⊢
      simp only [applySuff] at ⊢
      have hs2 : suffGroesse suff + groesse (.arrow base f) ≤ n + 1 := by
        simp only [suffGroesse, groesse] at hs ⊢
        omega
      have hF2 : 12 * (suffGroesse suff + groesse (.arrow base f) + 1) +
          suffGroesse suff ≤ F' := by
        simp only [suffGroesse, groesse] at hs hF ⊢
        omega
      exact ih (SExpr.arrow base f) rest F' hs2 hg hr hF2
    | idx i =>
      intro base rest F hs hg hr hF
      simp only [suffGut, Bool.and_eq_true] at hg
      obtain ⟨hi, hgs⟩ := hg
      have hF1 : 1 ≤ F := by omega
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      simp only [suffToks, List.cons_append] at ⊢
      simp only [parseSuffixe, nameText_nameTok] at ⊢
      -- ⊢ : parseOr F' (T(i) ++ ...) then `]` then recurse.
      have hii : groesse i ≤ n := by
        simp only [suffGroesse] at hs
        omega
      have hr1 : ruhig ([.zeichen "]"] ++ suffToks suff ++ rest) = true :=
        rfl
      have hr2 : ruhigSuff ([.zeichen "]"] ++ suffToks suff ++ rest) = true :=
        rfl
      have hr3 : ruhigGleit ([.zeichen "]"] ++ suffToks suff ++ rest) = true :=
        rfl
      have hFi : 12 * (groesse i + 1) + groesse i + 8 ≤ F' := by
        simp only [suffGroesse] at hs hF ⊢
        omega
      obtain ⟨hOr, -⟩ := Rn
      have hOi := hOr i ([.zeichen "]"] ++ suffToks suff ++ rest) F'
        hii hi hr1 hr2 hr3 hFi
      simp only [List.append_assoc, List.cons_append, List.nil_append] at ⊢ hOi
      simp only [hOi, List.cons_append] at ⊢
      simp only [applySuff] at ⊢
      have hs2 : suffGroesse suff + groesse (.index base i) ≤ n + 1 := by
        simp only [suffGroesse, groesse] at hs ⊢
        omega
      have hF2 : 12 * (suffGroesse suff + groesse (.index base i) + 1) +
          suffGroesse suff ≤ F' := by
        simp only [suffGroesse, groesse] at hs hF ⊢
        omega
      exact ih (SExpr.index base i) rest F' hs2 hgs hr hF2

end Gabbro.Grammatik.Parser
