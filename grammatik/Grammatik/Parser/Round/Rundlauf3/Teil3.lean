module

public import Grammatik.Parser.Round.Rundlauf3.Teil3a

public import Grammatik.Parser.Round.Rundlauf2
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Round.Rundlauf3.Teil2

@[expose] public section

namespace Gabbro.Grammatik.Parser
-- Add-rest legs from operand legs (covers all five add
-- spellings, `+` included -- overlap with older predicates is
-- harmless since the earlier disjunct wins).
theorem addLegs : ∀ (op : String) (l r : SExpr),
    istAddOp op = true → Legs l → Legs r → Legs (.bin op l r) := by
  intro op l r hop Hl Hr
  apply bin_turm3 op l r
  intro T G hG
  obtain ⟨hmMul, hrsS1, hrgS1⟩ :=
    addbar_facts op (druckToks r ++ ([.zeichen ")"] ++ T)) hop
  have hhit := opAdd_add_hit op
    (druckToks r ++ ([.zeichen ")"] ++ T)) hop
  have hUl : ∀ (G' : Nat),
      12 * (groesse l + 1) + groesse l + 2 ≤ G' →
      parseUnary G' (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ T)))) =
        .ok (l, [.zeichen op] ++
          (druckToks r ++ ([.zeichen ")"] ++ T))) := by
    intro G' hG'
    exact Hl.2.1 ([.zeichen op] ++
      (druckToks r ++ ([.zeichen ")"] ++ T))) G' hrsS1 hrgS1 hG'
  have hUr : ∀ (G' : Nat),
      12 * (groesse r + 1) + groesse r + 2 ≤ G' →
      parseUnary G' (druckToks r ++ ([.zeichen ")"] ++ T)) =
        .ok (r, [.zeichen ")"] ++ T) := by
    intro G' hG'
    exact Hr.2.1 ([.zeichen ")"] ++ T) G'
      (hrs_paren T) (hrg_paren T) hG'
  exact addB_step op l r T hUl hUr hmMul hhit hrsS1 hrgS1 G hG

-- Mul-rest legs from operand legs (covers all four mul
-- spellings, `*` included).
theorem mulLegs : ∀ (op : String) (l r : SExpr),
    istMulOp op = true → Legs l → Legs r → Legs (.bin op l r) := by
  intro op l r hop Hl Hr
  apply bin_turm3 op l r
  intro T G hG
  obtain ⟨hrsS1, hrgS1⟩ :=
    mulbar_facts op (druckToks r ++ ([.zeichen ")"] ++ T)) hop
  have hhit := opMul_mul_hit op
    (druckToks r ++ ([.zeichen ")"] ++ T)) hop
  have hUl : ∀ (G' : Nat),
      12 * (groesse l + 1) + groesse l + 2 ≤ G' →
      parseUnary G' (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ T)))) =
        .ok (l, [.zeichen op] ++
          (druckToks r ++ ([.zeichen ")"] ++ T))) := by
    intro G' hG'
    exact Hl.2.1 ([.zeichen op] ++
      (druckToks r ++ ([.zeichen ")"] ++ T))) G' hrsS1 hrgS1 hG'
  have hUr : ∀ (G' : Nat),
      12 * (groesse r + 1) + groesse r + 2 ≤ G' →
      parseUnary G' (druckToks r ++ ([.zeichen ")"] ++ T)) =
        .ok (r, [.zeichen ")"] ++ T) := by
    intro G' hG'
    exact Hr.2.1 ([.zeichen ")"] ++ T) G'
      (hrs_paren T) (hrg_paren T) hG'
  exact mulB_step op l r T hUl hUr hhit hrsS1 hrgS1 G hG

-- The two new layers: add/mul operators over level-2 trees.
def addNeu : SExpr → Bool
  | .bin o l r => istAddOp o && gutBit l && gutBit r
  | _ => false
def mulNeu : SExpr → Bool
  | .bin o l r => istMulOp o && gutBit l && gutBit r
  | _ => false

-- Level-3 predicate: level 2 plus one add layer plus one mul
-- layer.
def gutAM (e : SExpr) : Bool := gutBit e || addNeu e || mulNeu e

-- Every level-3 tree has legs: level-2 trees by `legsBit`, new
-- nodes by `addLegs`/`mulLegs` over level-2 legs.
theorem legsAM : ∀ (e : SExpr), gutAM e = true → Legs e := by
  intro e hg
  simp only [gutAM, Bool.or_eq_true] at hg
  obtain hold | hnew := hg
  · obtain hold2 | hadd := hold
    · exact legsBit e hold2
    · cases e with
      | lit m => simp only [addNeu, Bool.false_eq_true] at hadd
      | float s => simp only [addNeu, Bool.false_eq_true] at hadd
      | tru => simp only [addNeu, Bool.false_eq_true] at hadd
      | fls => simp only [addNeu, Bool.false_eq_true] at hadd
      | «variable» s => simp only [addNeu, Bool.false_eq_true] at hadd
      | un o x => simp only [addNeu, Bool.false_eq_true] at hadd
      | bin o l r =>
        simp only [addNeu, Bool.and_eq_true, and_assoc] at hadd
        obtain ⟨hop, hl, hr2⟩ := hadd
        have Hl := legsBit l hl
        have Hr := legsBit r hr2
        have hao : istAddOp o = true := hop
        obtain rfl | rfl | rfl | rfl | rfl := add_is o hop
        · exact addLegs "+" l r hao Hl Hr
        · exact addLegs "-" l r hao Hl Hr
        · exact addLegs "+%" l r hao Hl Hr
        · exact addLegs "-%" l r hao Hl Hr
        · exact addLegs "+|" l r hao Hl Hr
      | field x f => simp only [addNeu, Bool.false_eq_true] at hadd
      | index x i => simp only [addNeu, Bool.false_eq_true] at hadd
      | arrow x f => simp only [addNeu, Bool.false_eq_true] at hadd
      | call f xs => simp only [addNeu, Bool.false_eq_true] at hadd
      | fnref f => simp only [addNeu, Bool.false_eq_true] at hadd
      | built f xs => simp only [addNeu, Bool.false_eq_true] at hadd
      | old x => simp only [addNeu, Bool.false_eq_true] at hadd
      | res => simp only [addNeu, Bool.false_eq_true] at hadd
      | why g f => simp only [addNeu, Bool.false_eq_true] at hadd
      | ext xk xn xs => simp only [addNeu, Bool.false_eq_true] at hadd
  · cases e with
    | lit m => simp only [mulNeu, Bool.false_eq_true] at hnew
    | float s => simp only [mulNeu, Bool.false_eq_true] at hnew
    | tru => simp only [mulNeu, Bool.false_eq_true] at hnew
    | fls => simp only [mulNeu, Bool.false_eq_true] at hnew
    | «variable» s => simp only [mulNeu, Bool.false_eq_true] at hnew
    | un o x => simp only [mulNeu, Bool.false_eq_true] at hnew
    | bin o l r =>
      simp only [mulNeu, Bool.and_eq_true, and_assoc] at hnew
      obtain ⟨hop, hl, hr2⟩ := hnew
      have Hl := legsBit l hl
      have Hr := legsBit r hr2
      have hmo : istMulOp o = true := hop
      obtain rfl | rfl | rfl | rfl := mul_is o hop
      · exact mulLegs "*" l r hmo Hl Hr
      · exact mulLegs "/" l r hmo Hl Hr
      · exact mulLegs "%" l r hmo Hl Hr
      · exact mulLegs "*%" l r hmo Hl Hr
    | field x f => simp only [mulNeu, Bool.false_eq_true] at hnew
    | index x i => simp only [mulNeu, Bool.false_eq_true] at hnew
    | arrow x f => simp only [mulNeu, Bool.false_eq_true] at hnew
    | call f xs => simp only [mulNeu, Bool.false_eq_true] at hnew
    | fnref f => simp only [mulNeu, Bool.false_eq_true] at hnew
    | built f xs => simp only [mulNeu, Bool.false_eq_true] at hnew
    | old x => simp only [mulNeu, Bool.false_eq_true] at hnew
    | res => simp only [mulNeu, Bool.false_eq_true] at hnew
    | why g f => simp only [mulNeu, Bool.false_eq_true] at hnew
    | ext xk xn xs => simp only [mulNeu, Bool.false_eq_true] at hnew

-- Level-3 goal: every `gutAM` tree parses back from its printed
-- tokens with `brennstoff` fuel.
theorem parse_druck_am : ∀ (e : SExpr), gutAM e = true →
    parseOr (brennstoff e) (druckToks e ++ [.ende]) =
      .ok (e, [.ende]) := by
  intro e hg
  have hL := legsAM e hg
  have hr : ruhig [.ende] = true := rfl
  have hrs : ruhigSuff [.ende] = true := rfl
  have hrg : ruhigGleit [.ende] = true := rfl
  have hF : 12 * (groesse e + 1) + groesse e + 8 ≤ brennstoff e := by
    simp only [brennstoff, Std.le_refl]
  exact hL.2.2.2.2.2.2.2 [.ende] (brennstoff e) hr hrs hrg hF

-- Level-3 witnesses, corpus-flavoured (the corpus subtracts
-- counters and divides ranges all over `04-schleifen`): a
-- binary `-` and a `/`, each as a `parse_druck_am` instance and
-- a kernel-computed `match` check.
theorem zeuge_am_sub :
    parseOr (brennstoff (.bin "-" (.variable "s") (.lit 1)))
    (druckToks (.bin "-" (.variable "s") (.lit 1)) ++ [.ende]) =
      .ok (.bin "-" (.variable "s") (.lit 1), [.ende]) :=
  parse_druck_am _ (by decide)
theorem zeuge_am_sub_rech : (match parseOr
    (brennstoff (.bin "-" (.variable "s") (.lit 1)))
    (druckToks (.bin "-" (.variable "s") (.lit 1)) ++ [.ende]) with
    | .ok (.bin "-" (.variable "s") (.lit 1), [.ende]) => true
    | _ => false) = true := by
  decide
theorem zeuge_am_div :
    parseOr (brennstoff (.bin "/" (.variable "n") (.lit 2)))
    (druckToks (.bin "/" (.variable "n") (.lit 2)) ++ [.ende]) =
      .ok (.bin "/" (.variable "n") (.lit 2), [.ende]) :=
  parse_druck_am _ (by decide)
theorem zeuge_am_div_rech : (match parseOr
    (brennstoff (.bin "/" (.variable "n") (.lit 2)))
    (druckToks (.bin "/" (.variable "n") (.lit 2)) ++ [.ende]) with
    | .ok (.bin "/" (.variable "n") (.lit 2), [.ende]) => true
    | _ => false) = true := by
  decide

-- BRIDGES to lane 161's `gut`: every layered predicate implies
-- `gut`. Needed for the calls level (`keinDP_tree` and
-- `toksKopf` are already proved for `gut`, so no analogues are
-- needed -- the 172 estimate assumed an `RKern` adaptation).
theorem gutOpBin_of_cmp : ∀ (o : String),
    istCmpOp o = true → gutOpBin o = true := by
  intro o h
  simp only [gutOpBin, gutOpCmp, h, Bool.or_true, Bool.true_or]
theorem gutOpBin_of_bit : ∀ (o : String),
    istBitOp o = true → gutOpBin o = true := by
  intro o h
  simp only [gutOpBin, gutOpBit, h, Bool.or_true, Bool.true_or]
theorem gutOpBin_of_add : ∀ (o : String),
    istAddOp o = true → gutOpBin o = true := by
  intro o h
  simp only [gutOpBin, gutOpAdd, h, Bool.or_true, Bool.true_or]
theorem gutOpBin_of_mul : ∀ (o : String),
    istMulOp o = true → gutOpBin o = true := by
  intro o h
  simp only [gutOpBin, gutOpMul, h, Bool.or_true]

end Gabbro.Grammatik.Parser
