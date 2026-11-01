module

public import Grammatik.Parser.Round.Rundlauf2
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Round.Rundlauf3.Teil2

@[expose] public section

namespace Gabbro.Grammatik.Parser

-- The add-loop inner trace, generic over the spelling: mirror
-- of `kernB_step` (`parseOr` descends to `parseAdd`,
-- `parseMul` runs `l`, `parseAddL` consumes the operator and
-- `r`, stops at `)`), with every concrete fact as a
-- hypothesis. Same `+10` fuel. No predicate anywhere.
theorem addB_step : ∀ (op : String) (l r : SExpr) (W : List Token),
    (∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 2 ≤ G →
      parseUnary G (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (l, [.zeichen op] ++
          (druckToks r ++ ([.zeichen ")"] ++ W)))) →
    (∀ (G : Nat), 12 * (groesse r + 1) + groesse r + 2 ≤ G →
      parseUnary G (druckToks r ++ ([.zeichen ")"] ++ W)) =
        .ok (r, [.zeichen ")"] ++ W)) →
    opMul ([.zeichen op] ++ (druckToks r ++ ([.zeichen ")"] ++ W))) = none →
    opAdd ([.zeichen op] ++ (druckToks r ++ ([.zeichen ")"] ++ W))) =
      some (op, druckToks r ++ ([.zeichen ")"] ++ W)) →
    ruhigSuff ([.zeichen op] ++ (druckToks r ++ ([.zeichen ")"] ++ W))) = true →
    ruhigGleit ([.zeichen op] ++ (druckToks r ++ ([.zeichen ")"] ++ W))) = true →
    ∀ (G : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen op] ++ druckToks r ++
        [.zeichen ")"] ++ W) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
  intro op l r W hUl hUr hMulmiss hop hrsS1 hrgS1 G hG
  have hpos_l := groesse_pos l
  have hpos_r := groesse_pos r
  simp only [List.append_assoc] at ⊢
  -- Left operand through `parseMul` with the operator follow.
  have hMl : ∀ (G5 : Nat),
      12 * (groesse l + 1) + groesse l + 3 ≤ G5 →
      parseMul G5 (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (l, [.zeichen op] ++
          (druckToks r ++ ([.zeichen ")"] ++ W))) := by
    intro G5 hG5
    have h51 : 1 ≤ G5 := by omega
    obtain ⟨G6, rfl⟩ : ∃ G6, G5 = G6 + 1 := ⟨G5 - 1, by omega⟩
    have hUl' := hUl G6 (by omega)
    have h52 : 1 ≤ G6 := by omega
    obtain ⟨G7, rfl⟩ : ∃ G7, G6 = G7 + 1 := ⟨G6 - 1, by omega⟩
    simp only [parseMul, parseMulL, hUl', hMulmiss] at ⊢
  -- Right operand through `parseMul` with the `)` follow.
  have hMr : ∀ (G5x : Nat),
      12 * (groesse r + 1) + groesse r + 3 ≤ G5x →
      parseMul G5x (druckToks r ++ ([.zeichen ")"] ++ W)) =
        .ok (r, [.zeichen ")"] ++ W) := by
    intro G5x hG5x
    have h53 : 1 ≤ G5x := by omega
    obtain ⟨G6x, rfl⟩ : ∃ G6x, G5x = G6x + 1 := ⟨G5x - 1, by omega⟩
    have hUr' := hUr G6x (by omega)
    have h54 : 1 ≤ G6x := by omega
    obtain ⟨G7x, rfl⟩ : ∃ G7x, G6x = G7x + 1 := ⟨G6x - 1, by omega⟩
    have hstop := opMul_paren W
    simp only [parseMul, parseMulL, hUr', hstop] at ⊢
  -- The `parseAdd` core: `l`, consume the operator, `r`, stop
  -- at `)`.
  have hAdd : ∀ (G4 : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 6 ≤ G4 →
      parseAdd G4 (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
    intro G4 hG4
    have h41 : 1 ≤ G4 := by omega
    obtain ⟨G5, rfl⟩ : ∃ G5, G4 = G5 + 1 := ⟨G4 - 1, by omega⟩
    have hMl' := hMl G5 (by omega)
    have h42 : 1 ≤ G5 := by omega
    obtain ⟨G5x, rfl⟩ : ∃ G5x, G5 = G5x + 1 := ⟨G5 - 1, by omega⟩
    have hMr' := hMr G5x (by omega)
    have hstop := stopAdd ([.zeichen ")"] ++ W) (hr_paren W)
    have h43 : 1 ≤ G5x := by omega
    obtain ⟨G5y, rfl⟩ : ∃ G5y, G5x = G5y + 1 := ⟨G5x - 1, by omega⟩
    simp only [parseAdd, parseAddL, hMl', hop, hMr', hstop] at ⊢
  -- Up the pass-through levels, each stopping at `)`.
  have hBit : ∀ (G3 : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 7 ≤ G3 →
      parseBit G3 (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
    intro G3 hG3
    have h31 : 1 ≤ G3 := by omega
    obtain ⟨G4, rfl⟩ : ∃ G4, G3 = G4 + 1 := ⟨G3 - 1, by omega⟩
    have hAdd' := hAdd G4 (by omega)
    have h32 : 1 ≤ G4 := by omega
    obtain ⟨G4x, rfl⟩ : ∃ G4x, G4 = G4x + 1 := ⟨G4 - 1, by omega⟩
    have hstop := stopBit ([.zeichen ")"] ++ W) (hr_paren W)
    simp only [parseBit, parseBitL, hAdd', hstop] at ⊢
  have hCmp : ∀ (G2 : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 8 ≤ G2 →
      parseCmp G2 (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
    intro G2 hG2
    have h21 : 1 ≤ G2 := by omega
    obtain ⟨G3, rfl⟩ : ∃ G3, G2 = G3 + 1 := ⟨G2 - 1, by omega⟩
    have hBit' := hBit G3 (by omega)
    have hstop := opVgl_paren W
    simp only [parseCmp, hBit', hstop] at ⊢
  have hAnd : ∀ (G1 : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 9 ≤ G1 →
      parseAnd G1 (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
    intro G1 hG1
    have h11 : 1 ≤ G1 := by omega
    obtain ⟨G2, rfl⟩ : ∃ G2, G1 = G2 + 1 := ⟨G1 - 1, by omega⟩
    have hCmp' := hCmp G2 (by omega)
    have h12 : 1 ≤ G2 := by omega
    obtain ⟨G2x, rfl⟩ : ∃ G2x, G2 = G2x + 1 := ⟨G2 - 1, by omega⟩
    have hstop := opUnd_paren W
    simp only [parseAnd, parseAndL, hCmp', hstop] at ⊢
  have hOr : ∀ (G0 : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G0 →
      parseOr G0 (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
    intro G0 hG0
    have h01 : 1 ≤ G0 := by omega
    obtain ⟨G1, rfl⟩ : ∃ G1, G0 = G1 + 1 := ⟨G0 - 1, by omega⟩
    have hAnd' := hAnd G1 (by omega)
    have h02 : 1 ≤ G1 := by omega
    obtain ⟨G1x, rfl⟩ : ∃ G1x, G1 = G1x + 1 := ⟨G1 - 1, by omega⟩
    have hstop := opOder_paren W
    simp only [parseOr, parseOrL, hAnd', hstop] at ⊢
  exact hOr G hG

-- The mul-loop inner trace, generic over the spelling: mirror
-- of `kernB_step_star` (the operator consumes inside
-- `parseMul`, `parseAdd` stops at `)`), with every concrete
-- fact as a hypothesis. Same `+10` fuel. No predicate
-- anywhere.
theorem mulB_step : ∀ (op : String) (l r : SExpr) (W : List Token),
    (∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 2 ≤ G →
      parseUnary G (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (l, [.zeichen op] ++
          (druckToks r ++ ([.zeichen ")"] ++ W)))) →
    (∀ (G : Nat), 12 * (groesse r + 1) + groesse r + 2 ≤ G →
      parseUnary G (druckToks r ++ ([.zeichen ")"] ++ W)) =
        .ok (r, [.zeichen ")"] ++ W)) →
    opMul ([.zeichen op] ++ (druckToks r ++ ([.zeichen ")"] ++ W))) =
      some (op, druckToks r ++ ([.zeichen ")"] ++ W)) →
    ruhigSuff ([.zeichen op] ++ (druckToks r ++ ([.zeichen ")"] ++ W))) = true →
    ruhigGleit ([.zeichen op] ++ (druckToks r ++ ([.zeichen ")"] ++ W))) = true →
    ∀ (G : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen op] ++ druckToks r ++
        [.zeichen ")"] ++ W) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
  intro op l r W hUl hUr hop hrsS1 hrgS1 G hG
  have hpos_l := groesse_pos l
  have hpos_r := groesse_pos r
  simp only [List.append_assoc] at ⊢
  -- The `parseAdd` core with the operator consumed inside
  -- `parseMul` (mirror of `kernB_step_star`, spelling
  -- generalised).
  have hAdd : ∀ (G4 : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 6 ≤ G4 →
      parseAdd G4 (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
    intro G4 hG4
    have h41 : 1 ≤ G4 := by omega
    obtain ⟨G5, rfl⟩ : ∃ G5, G4 = G5 + 1 := ⟨G4 - 1, by omega⟩
    have h42 : 1 ≤ G5 := by omega
    obtain ⟨G6, rfl⟩ : ∃ G6, G5 = G6 + 1 := ⟨G5 - 1, by omega⟩
    have hUl' := hUl G6 (by omega)
    have h43 : 1 ≤ G6 := by omega
    obtain ⟨G6x, rfl⟩ : ∃ G6x, G6 = G6x + 1 := ⟨G6 - 1, by omega⟩
    have hUr' := hUr G6x (by omega)
    have h44 : 1 ≤ G6x := by omega
    obtain ⟨G6y, rfl⟩ : ∃ G6y, G6x = G6y + 1 := ⟨G6x - 1, by omega⟩
    have hstopM := opMul_paren W
    have hstopA := stopAdd ([.zeichen ")"] ++ W) (hr_paren W)
    simp only [parseAdd, parseMul, parseMulL, hUl', hop, hUr', hstopM] at ⊢
    -- Four strips numeral-fold the loop fuel to `+ 3`, which no
    -- equation fires on: unfold once more by explicit rewrite
    -- (same as `kernB_step_star`).
    have h45 : G6y + 3 = (G6y + 2) + 1 := by omega
    rw [h45] at ⊢
    simp only [parseAddL, hstopA] at ⊢
  -- Up the pass-through levels, each stopping at `)`.
  have hBit : ∀ (G3 : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 7 ≤ G3 →
      parseBit G3 (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
    intro G3 hG3
    have h31 : 1 ≤ G3 := by omega
    obtain ⟨G4, rfl⟩ : ∃ G4, G3 = G4 + 1 := ⟨G3 - 1, by omega⟩
    have hAdd' := hAdd G4 (by omega)
    have h32 : 1 ≤ G4 := by omega
    obtain ⟨G4x, rfl⟩ : ∃ G4x, G4 = G4x + 1 := ⟨G4 - 1, by omega⟩
    have hstop := stopBit ([.zeichen ")"] ++ W) (hr_paren W)
    simp only [parseBit, parseBitL, hAdd', hstop] at ⊢
  have hCmp : ∀ (G2 : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 8 ≤ G2 →
      parseCmp G2 (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
    intro G2 hG2
    have h21 : 1 ≤ G2 := by omega
    obtain ⟨G3, rfl⟩ : ∃ G3, G2 = G3 + 1 := ⟨G2 - 1, by omega⟩
    have hBit' := hBit G3 (by omega)
    have hstop := opVgl_paren W
    simp only [parseCmp, hBit', hstop] at ⊢
  have hAnd : ∀ (G1 : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 9 ≤ G1 →
      parseAnd G1 (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
    intro G1 hG1
    have h11 : 1 ≤ G1 := by omega
    obtain ⟨G2, rfl⟩ : ∃ G2, G1 = G2 + 1 := ⟨G1 - 1, by omega⟩
    have hCmp' := hCmp G2 (by omega)
    have h12 : 1 ≤ G2 := by omega
    obtain ⟨G2x, rfl⟩ : ∃ G2x, G2 = G2x + 1 := ⟨G2 - 1, by omega⟩
    have hstop := opUnd_paren W
    simp only [parseAnd, parseAndL, hCmp', hstop] at ⊢
  have hOr : ∀ (G0 : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G0 →
      parseOr G0 (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
    intro G0 hG0
    have h01 : 1 ≤ G0 := by omega
    obtain ⟨G1, rfl⟩ : ∃ G1, G0 = G1 + 1 := ⟨G0 - 1, by omega⟩
    have hAnd' := hAnd G1 (by omega)
    have h02 : 1 ≤ G1 := by omega
    obtain ⟨G1x, rfl⟩ : ∃ G1x, G1 = G1x + 1 := ⟨G1 - 1, by omega⟩
    have hstop := opOder_paren W
    simp only [parseOr, parseOrL, hAnd', hstop] at ⊢
  exact hOr G hG

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
