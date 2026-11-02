module

public import Grammatik.Parser.Round.Rundlauf2.Teil8a

public import Grammatik.Parser.Round.Rundlauf
public import Grammatik.Parser.Round.Rundlauf2.Teil7

@[expose] public section

namespace Gabbro.Grammatik.Parser
-- The `parsePrimary` step: no `ruhig` premise (suffixes never
-- see loop operators), prefix trees vacuous by `primFrei`.
theorem kernPrimary_step : ∀ (n : Nat), RKern n → BKern n → BKernStar n → BKernOr n → BKernAnd n →
    (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n + 1 →
      gutKern e = true → primFrei e = true → ruhigSuff rest = true →
      ruhigGleit rest = true →
      12 * (groesse e + 1) + groesse e + 1 ≤ F →
      parsePrimary F (druckToks e ++ rest) = .ok (e, rest)) := by
  intro n rkn bkn bStar bOr bAnd e rest F hs hg hpf hrs hrg hF
  cases e with
  | lit m => exact prim_lit m rest F (by omega)
  | float s => exact prim_gleit s rest F hrg (by omega)
  | tru => exact prim_wahr rest F (by omega)
  | fls => exact prim_falsch rest F (by omega)
  | «variable» a =>
    have hka : (!istKopfWort a) = true := by
      simp only [gutKern] at hg
      exact hg
    exact kern_prim_var a rest F hka hrs (by omega)
  | un o x => simp only [primFrei, Bool.false_eq_true] at hpf
  | bin o l r =>
    rw [gutKern_bin] at hg
    simp only [Bool.and_eq_true, and_assoc] at hg
    obtain ⟨hop, hl, hr2⟩ := hg
    obtain rfl | rfl | rfl | rfl := bin_is_pm o hop
    · have hsize : groesse (.bin "+" l r) = groesse l + groesse r + 1 := rfl
      have hsum : groesse l + groesse r ≤ n := by omega
      have hB : ∀ (G : Nat),
          12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
          parseOr G (druckToks l ++ [.zeichen "+"] ++ druckToks r ++
            [.zeichen ")"] ++ rest) =
            .ok (.bin "+" l r, [.zeichen ")"] ++ rest) := by
        intro G hG
        exact bkn l r rest G hsum hl hr2 hG
      exact kern_bin_prim l r rest hB F (by omega)
    · have hsize : groesse (.bin "*" l r) = groesse l + groesse r + 1 := rfl
      have hsum : groesse l + groesse r ≤ n := by omega
      have hB : ∀ (G : Nat),
          12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
          parseOr G (druckToks l ++ [.zeichen "*"] ++ druckToks r ++
            [.zeichen ")"] ++ rest) =
            .ok (.bin "*" l r, [.zeichen ")"] ++ rest) := by
        intro G hG
        exact bStar l r rest G hsum hl hr2 hG
      exact kern_bin_prim_star l r rest hB F (by omega)
    · have hsize : groesse (.bin "||" l r) = groesse l + groesse r + 1 := rfl
      have hsum : groesse l + groesse r ≤ n := by omega
      have hB : ∀ (G : Nat),
          12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
          parseOr G (druckToks l ++ [.zeichen "||"] ++ druckToks r ++
            [.zeichen ")"] ++ rest) =
            .ok (.bin "||" l r, [.zeichen ")"] ++ rest) := by
        intro G hG
        exact bOr l r rest G hsum hl hr2 hG
      exact kern_bin_prim_or l r rest hB F (by omega)
    · have hsize : groesse (.bin "&&" l r) = groesse l + groesse r + 1 := rfl
      have hsum : groesse l + groesse r ≤ n := by omega
      have hB : ∀ (G : Nat),
          12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
          parseOr G (druckToks l ++ [.zeichen "&&"] ++ druckToks r ++
            [.zeichen ")"] ++ rest) =
            .ok (.bin "&&" l r, [.zeichen ")"] ++ rest) := by
        intro G hG
        exact bAnd l r rest G hsum hl hr2 hG
      exact kern_bin_prim_and l r rest hB F (by omega)
  | field x f =>
    rw [gutKern_feld] at hg
    have hpp : gutKernPlatz (.field x f) = true := by
      rw [gutKernPlatz_feld]; exact hg
    exact kern_prim_platz n rkn (.field x f) rest F hs hpp hrs (by omega)
  | index x i =>
    rw [gutKern_index] at hg
    simp only [Bool.and_eq_true] at hg
    obtain ⟨hpx, hi⟩ := hg
    have hpp : gutKernPlatz (.index x i) = true := by
      rw [gutKernPlatz_index]; simp only [Bool.and_eq_true]; exact ⟨hpx, hi⟩
    exact kern_prim_platz n rkn (.index x i) rest F hs hpp hrs (by omega)
  | arrow x f =>
    rw [gutKern_pfeil] at hg
    have hpp : gutKernPlatz (.arrow x f) = true := by
      rw [gutKernPlatz_pfeil]; exact hg
    exact kern_prim_platz n rkn (.arrow x f) rest F hs hpp hrs (by omega)
  | call f xs => simp only [gutKern, Bool.false_eq_true] at hg
  | fnref f => simp only [gutKern, Bool.false_eq_true] at hg
  | built f xs => simp only [gutKern, Bool.false_eq_true] at hg
  | old x => simp only [gutKern, Bool.false_eq_true] at hg
  | res => simp only [gutKern, Bool.false_eq_true] at hg
  | why g f => simp only [gutKern, Bool.false_eq_true] at hg
  | ext xk xn xs => simp only [gutKern, Bool.false_eq_true] at hg

-- The joint invariant by size induction: base cases are
-- vacuous (every tree has size at least one, every pair at
-- least two), steps assemble the eight level lemmas plus all
-- four inner traces.
theorem kernRB : ∀ (n : Nat), RKern n ∧ BKern n ∧ BKernStar n ∧ BKernOr n ∧ BKernAnd n := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro e rest F hs _ _ _ _ _
        have hp := groesse_pos e
        omega
      · intro e rest F hs _ _ _ _ _
        have hp := groesse_pos e
        omega
      · intro e rest F hs _ _ _ _ _
        have hp := groesse_pos e
        omega
      · intro e rest F hs _ _ _ _ _
        have hp := groesse_pos e
        omega
      · intro e rest F hs _ _ _ _ _
        have hp := groesse_pos e
        omega
      · intro e rest F hs _ _ _ _ _
        have hp := groesse_pos e
        omega
      · intro e rest F hs _ _ _ _
        have hp := groesse_pos e
        omega
      · intro e rest F hs _ _ _ _ _
        have hp := groesse_pos e
        omega
    · intro l r W F hsum _ _ _
      have hpl := groesse_pos l
      have hpr := groesse_pos r
      omega
    · intro l r W F hsum _ _ _
      have hpl := groesse_pos l
      have hpr := groesse_pos r
      omega
    · intro l r W F hsum _ _ _
      have hpl := groesse_pos l
      have hpr := groesse_pos r
      omega
    · intro l r W F hsum _ _ _
      have hpl := groesse_pos l
      have hpr := groesse_pos r
      omega
  | succ n ih =>
    obtain ⟨rkn, bkn, bStar, bOr, bAnd⟩ := ih
    exact ⟨⟨kernOr_step n rkn bkn bStar bOr bAnd, kernAnd_step n rkn bkn bStar bOr bAnd,
      kernCmp_step n rkn bkn bStar bOr bAnd, kernBit_step n rkn bkn bStar bOr bAnd,
      kernAdd_step n rkn bkn bStar bOr bAnd, kernMul_step n rkn bkn bStar bOr bAnd,
      kernUnary_step n rkn bkn bStar bOr bAnd, kernPrimary_step n rkn bkn bStar bOr bAnd⟩,
      kernB_step n rkn, kernB_step_star n rkn, kernB_step_or n rkn,
      kernB_step_and n rkn⟩

-- Step A goal: every `gutKern` tree parses back from its
-- printed tokens with `brennstoff` fuel. The `Or` leg of the
-- invariant at `groesse e`, with `ende` follows (all `rfl`) and
-- fuel exactly `brennstoff` (which was grown to the `RKern`
-- bound -- measured, see its doc comment).
theorem parse_druck_kern : ∀ (e : SExpr), gutKern e = true →
    parseOr (brennstoff e) (druckToks e ++ [.ende]) =
      .ok (e, [.ende]) := by
  intro e hg
  have hRB := kernRB (groesse e)
  obtain ⟨⟨rOr, -, -, -, -, -, -, -⟩, -, -, -, -⟩ := hRB
  have hr : ruhig [.ende] = true := rfl
  have hrs : ruhigSuff [.ende] = true := rfl
  have hrg : ruhigGleit [.ende] = true := rfl
  have hF : 12 * (groesse e + 1) + groesse e + 8 ≤ brennstoff e := by
    simp only [brennstoff, Std.le_refl]
  exact rOr e [.ende] (brennstoff e) (Nat.le_refl _) hg hr hrs hrg hF

-- Witnesses on small expressions, each in two forms: the
-- `parse_druck_kern` instance (the round trip at work), and a
-- kernel-computed shape check. (`decide` on `Except`-equality
-- fails: no `DecidableEq SExpr` -- the `match` form needs only
-- discrimination, so the kernel evaluates both sides.)
theorem zeuge_kern_lit : parseOr (brennstoff (.lit 5))
    (druckToks (.lit 5) ++ [.ende]) = .ok (.lit 5, [.ende]) :=
  parse_druck_kern _ (by decide)
theorem zeuge_kern_lit_rech : (match parseOr (brennstoff (.lit 5))
    (druckToks (.lit 5) ++ [.ende]) with
    | .ok (.lit 5, [.ende]) => true
    | _ => false) = true := by
  decide
theorem zeuge_kern_plus :
    parseOr (brennstoff (.bin "+" (.lit 1) (.lit 2)))
    (druckToks (.bin "+" (.lit 1) (.lit 2)) ++ [.ende]) =
      .ok (.bin "+" (.lit 1) (.lit 2), [.ende]) :=
  parse_druck_kern _ (by decide)
theorem zeuge_kern_plus_rech : (match parseOr
    (brennstoff (.bin "+" (.lit 1) (.lit 2)))
    (druckToks (.bin "+" (.lit 1) (.lit 2)) ++ [.ende]) with
    | .ok (.bin "+" (.lit 1) (.lit 2), [.ende]) => true
    | _ => false) = true := by
  decide
-- Step B1 witnesses: the widened predicate at work (negation
-- of a literal, bitwise-not of a variable).
theorem zeuge_kern_neg : parseOr (brennstoff (.un "-" (.lit 3)))
    (druckToks (.un "-" (.lit 3)) ++ [.ende]) =
      .ok (.un "-" (.lit 3), [.ende]) :=
  parse_druck_kern _ (by decide)
theorem zeuge_kern_neg_rech : (match parseOr (brennstoff (.un "-" (.lit 3)))
    (druckToks (.un "-" (.lit 3)) ++ [.ende]) with
    | .ok (.un "-" (.lit 3), [.ende]) => true
    | _ => false) = true := by
  decide
-- Step B2 witnesses: the second binary level at work (a
-- product, nested in a sum).
theorem zeuge_kern_mul : parseOr (brennstoff (.bin "*" (.lit 2) (.lit 3)))
    (druckToks (.bin "*" (.lit 2) (.lit 3)) ++ [.ende]) =
      .ok (.bin "*" (.lit 2) (.lit 3), [.ende]) :=
  parse_druck_kern _ (by decide)
theorem zeuge_kern_mul_rech : (match parseOr
    (brennstoff (.bin "*" (.lit 2) (.lit 3)))
    (druckToks (.bin "*" (.lit 2) (.lit 3)) ++ [.ende]) with
    | .ok (.bin "*" (.lit 2) (.lit 3), [.ende]) => true
    | _ => false) = true := by
  decide
-- Step B4 witnesses: the loop level at work (a disjunction).
theorem zeuge_kern_or : parseOr (brennstoff (.bin "||" (.tru) (.fls)))
    (druckToks (.bin "||" (.tru) (.fls)) ++ [.ende]) =
      .ok (.bin "||" (.tru) (.fls), [.ende]) :=
  parse_druck_kern _ (by decide)
theorem zeuge_kern_or_rech : (match parseOr
    (brennstoff (.bin "||" (.tru) (.fls)))
    (druckToks (.bin "||" (.tru) (.fls)) ++ [.ende]) with
    | .ok (.bin "||" (.tru) (.fls), [.ende]) => true
    | _ => false) = true := by
  decide
-- Step B5 witnesses: the second loop level at work (a
-- conjunction).
theorem zeuge_kern_and : parseOr (brennstoff (.bin "&&" (.tru) (.tru)))
    (druckToks (.bin "&&" (.tru) (.tru)) ++ [.ende]) =
      .ok (.bin "&&" (.tru) (.tru), [.ende]) :=
  parse_druck_kern _ (by decide)
theorem zeuge_kern_and_rech : (match parseOr
    (brennstoff (.bin "&&" (.tru) (.tru)))
    (druckToks (.bin "&&" (.tru) (.tru)) ++ [.ende]) with
    | .ok (.bin "&&" (.tru) (.tru), [.ende]) => true
    | _ => false) = true := by
  decide
end Gabbro.Grammatik.Parser
