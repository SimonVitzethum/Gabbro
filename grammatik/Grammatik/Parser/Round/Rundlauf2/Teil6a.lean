module

public import Grammatik.Parser.Round.Rundlauf
public import Grammatik.Parser.Round.Rundlauf2.Teil5

@[expose] public section

namespace Gabbro.Grammatik.Parser

-- Every `gutKernPlatz` tree is a head variable plus
-- kernel-lawful fragments: lane 161's `zerlege` with the
-- conclusion strengthened to `suffGutKern`.
theorem zerlege_kern : ∀ (n : Nat) (p : SExpr), groesse p ≤ n →
    gutKernPlatz p = true →
    ∃ (a : String) (suff : List SuffFrag),
      p = applySuff (.variable a) suff ∧
      (!istKopfWort a) = true ∧
      suffGutKern suff = true ∧
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
    | lit m => simp only [gutKernPlatz, Bool.false_eq_true] at hg
    | float s => simp only [gutKernPlatz, Bool.false_eq_true] at hg
    | tru => simp only [gutKernPlatz, Bool.false_eq_true] at hg
    | fls => simp only [gutKernPlatz, Bool.false_eq_true] at hg
    | «variable» a =>
      simp only [gutKernPlatz] at hg
      exact ⟨a, [], rfl, hg, rfl, by simp only [suffGroesse]; omega⟩
    | field x f =>
      simp only [gutKernPlatz] at hg
      have hx : groesse x ≤ n := by
        simp only [groesse] at hs
        omega
      obtain ⟨a, suff, rfl, hka, hgs, hsz⟩ := ih x hx hg
      refine ⟨a, suff ++ [.dot f], ?_, hka, ?_, ?_⟩
      · rw [applySuff_append]
        rfl
      · have hsg : suffGutKern (suff ++ [.dot f]) = suffGutKern suff := by
          simp only [suffGutKern_append, suffGutKern, Bool.and_true]
        rw [hsg]
        exact hgs
      · simp only [suffGroesse_append, suffGroesse] at ⊢
        omega
    | index x i =>
      simp only [gutKernPlatz, Bool.and_eq_true] at hg
      obtain ⟨hpx, hi⟩ := hg
      have hx : groesse x ≤ n := by
        simp only [groesse] at hs
        omega
      obtain ⟨a, suff, rfl, hka, hgs, hsz⟩ := ih x hx hpx
      refine ⟨a, suff ++ [.idx i], ?_, hka, ?_, ?_⟩
      · rw [applySuff_append]
        rfl
      · have hgi : gutKern i = true := hi
        have hsg : suffGutKern (suff ++ [.idx i]) =
            (suffGutKern suff && gutKern i) := by
          simp only [suffGutKern_append, suffGutKern, Bool.and_true]
        rw [hsg]
        simp only [hgs, hgi, Bool.and_self]
      · simp only [suffGroesse_append, suffGroesse] at ⊢
        simp only [groesse, groesse_applySuff] at hs
        omega
    | arrow x f =>
      simp only [gutKernPlatz] at hg
      have hx : groesse x ≤ n := by
        simp only [groesse] at hs
        omega
      obtain ⟨a, suff, rfl, hka, hgs, hsz⟩ := ih x hx hg
      refine ⟨a, suff ++ [.arrow f], ?_, hka, ?_, ?_⟩
      · rw [applySuff_append]
        rfl
      · have hsg : suffGutKern (suff ++ [.arrow f]) = suffGutKern suff := by
          simp only [suffGutKern_append, suffGutKern, Bool.and_true]
        rw [hsg]
        exact hgs
      · simp only [suffGroesse_append, suffGroesse] at ⊢
        omega
    | un o x => simp only [gutKernPlatz, Bool.false_eq_true] at hg
    | bin o l r => simp only [gutKernPlatz, Bool.false_eq_true] at hg
    | call f xs => simp only [gutKernPlatz, Bool.false_eq_true] at hg
    | fnref f => simp only [gutKernPlatz, Bool.false_eq_true] at hg
    | built f xs => simp only [gutKernPlatz, Bool.false_eq_true] at hg
    | old x => simp only [gutKernPlatz, Bool.false_eq_true] at hg
    | res => simp only [gutKernPlatz, Bool.false_eq_true] at hg
    | why g f => simp only [gutKernPlatz, Bool.false_eq_true] at hg
    | ext xk xn xs => simp only [gutKernPlatz, Bool.false_eq_true] at hg

-- Suffix chains through `parseSuffixe` over kernel trees:
-- lane 161's `suff_rund` with index payloads parsed through
-- `RKern` (they are `gutKern` by `suffGutKern`).
theorem kern_suff_rund : ∀ (n : Nat) (rkn : RKern n)
    (suff : List SuffFrag) (base : SExpr) (rest : List Token) (F : Nat),
    suffGroesse suff + groesse base ≤ n + 1 →
    suffGutKern suff = true →
    ruhigSuff rest = true →
    12 * (suffGroesse suff + groesse base + 1) + suffGroesse suff ≤ F →
    parseSuffixe F base (suffToks suff ++ rest) =
      .ok (applySuff base suff, rest) := by
  intro n rkn suff
  obtain ⟨rOr, -, -, -, -, -, -, -⟩ := rkn
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
      simp only [suffGutKern] at hg
      have hF1 : 1 ≤ F := by omega
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      simp only [suffToks, List.cons_append] at ⊢
      simp only [parseSuffixe, nameText_nameTok] at ⊢
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
      simp only [suffGutKern] at hg
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
      simp only [suffGutKern, Bool.and_eq_true] at hg
      obtain ⟨hi, hgs⟩ := hg
      have hF1 : 1 ≤ F := by omega
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      simp only [suffToks, List.cons_append] at ⊢
      simp only [parseSuffixe, nameText_nameTok] at ⊢
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
      have hOi := rOr i ([.zeichen "]"] ++ suffToks suff ++ rest) F'
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
