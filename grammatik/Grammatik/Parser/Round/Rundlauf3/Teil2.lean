module

public import Grammatik.Parser.Round.Rundlauf2
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Round.Rundlauf3.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Parser

theorem zeuge_cmp_lt_rech : (match parseOr
    (brennstoff (.bin "<" (.variable "s") (.lit 64)))
    (druckToks (.bin "<" (.variable "s") (.lit 64)) ++ [.ende]) with
    | .ok (.bin "<" (.variable "s") (.lit 64), [.ende]) => true
    | _ => false) = true := by
  decide

-- LEVEL BIT (`&`, `|`, `^`, `<<`, `>>`, `<<%`): the flat loop at
-- `parseBitL`, exactly the `+` shape one level up (lane 172
-- report). Generic over the spelling like the comparison level.
theorem bit_is : ∀ (o : String), istBitOp o = true →
    o = "&" ∨ o = "|" ∨ o = "^" ∨ o = "<<" ∨ o = ">>" ∨ o = "<<%" := by
  intro o h
  simp only [istBitOp, Bool.or_eq_true] at h
  obtain h5 | hF := h
  · obtain h4 | hE := h5
    · obtain h3 | hD := h4
      · obtain h2 | hC := h3
        · obtain hA | hB := h2
          · exact Or.inl (strKlingt o "&" hA)
          · exact Or.inr (Or.inl (strKlingt o "|" hB))
        · exact Or.inr (Or.inr (Or.inl (strKlingt o "^" hC)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (strKlingt o "<<" hD))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (strKlingt o ">>" hE)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (strKlingt o "<<%" hF)))))

-- Facts for a bit-operator follow: the two loops below
-- `parseBit` miss it (`parseBitL` itself consumes it), and the
-- suffix/float tails are benign. One bundle for all six
-- spellings (each case `rfl`).
theorem bitbar_facts : ∀ (op : String) (T : List Token),
    istBitOp op = true →
    opMul ([.zeichen op] ++ T) = none ∧
    opAdd ([.zeichen op] ++ T) = none ∧
    ruhigSuff ([.zeichen op] ++ T) = true ∧
    ruhigGleit ([.zeichen op] ++ T) = true := by
  intro op T h
  obtain rfl | rfl | rfl | rfl | rfl | rfl := bit_is op h
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩

-- The bit table hits its own spelling (one lemma for all six
-- spellings; each case `rfl`).
theorem opBit_bit_hit : ∀ (op : String) (T : List Token),
    istBitOp op = true →
    opBit ([.zeichen op] ++ T) = some (op, T) := by
  intro op T h
  obtain rfl | rfl | rfl | rfl | rfl | rfl := bit_is op h
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

-- The `parseAdd`-level bar tower for a bit follow: from the
-- `parseUnary` leg, the two loop levels below `parseBit` each
-- run their child and stop on the operator. One level taller
-- than `tower_up_cmpbar`.
theorem tower_up_bitbar : ∀ (l : SExpr) (S1 : List Token),
    (∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 2 ≤ G →
      parseUnary G (druckToks l ++ S1) = .ok (l, S1)) →
    opMul S1 = none → opAdd S1 = none →
    (∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 3 ≤ G →
      parseMul G (druckToks l ++ S1) = .ok (l, S1))
    ∧ (∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 4 ≤ G →
      parseAdd G (druckToks l ++ S1) = .ok (l, S1)) := by
  intro l S1 hU hMul hAdd
  have hM : ∀ (G : Nat),
      12 * (groesse l + 1) + groesse l + 3 ≤ G →
      parseMul G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hU' := hU G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    simp only [parseMul, parseMulL, hU', hMul] at ⊢
  have hA : ∀ (G : Nat),
      12 * (groesse l + 1) + groesse l + 4 ≤ G →
      parseAdd G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hM' := hM G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    simp only [parseAdd, parseAddL, hM', hAdd] at ⊢
  exact ⟨hM, hA⟩

-- The bit inner trace, generic over the spelling: the left
-- operand parses at `parseAdd` with the operator follow,
-- `parseBitL` consumes the operator and the right operand in a
-- flat loop (one iteration, then the loop stops at `)`), and
-- `parseCmp`/`parseAnd`/`parseOr` stop at `)`. Same `+10`
-- fuel as every other B-trace. No predicate anywhere.
theorem bitB_step : ∀ (op : String) (l r : SExpr) (W : List Token),
    (∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 2 ≤ G →
      parseUnary G (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (l, [.zeichen op] ++
          (druckToks r ++ ([.zeichen ")"] ++ W)))) →
    (∀ (G : Nat), 12 * (groesse r + 1) + groesse r + 2 ≤ G →
      parseUnary G (druckToks r ++ ([.zeichen ")"] ++ W)) =
        .ok (r, [.zeichen ")"] ++ W)) →
    opMul ([.zeichen op] ++ (druckToks r ++ ([.zeichen ")"] ++ W))) = none →
    opAdd ([.zeichen op] ++ (druckToks r ++ ([.zeichen ")"] ++ W))) = none →
    opBit ([.zeichen op] ++ (druckToks r ++ ([.zeichen ")"] ++ W))) =
      some (op, druckToks r ++ ([.zeichen ")"] ++ W)) →
    ∀ (G : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen op] ++ druckToks r ++
        [.zeichen ")"] ++ W) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
  intro op l r W hUl hUr hMul hAdd hop G hG
  have hpos_l := groesse_pos l
  have hpos_r := groesse_pos r
  simp only [List.append_assoc] at ⊢
  -- Left operand at `parseAdd` with the operator follow.
  have hAl : ∀ (G5 : Nat),
      12 * (groesse l + 1) + groesse l + 4 ≤ G5 →
      parseAdd G5 (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (l, [.zeichen op] ++
          (druckToks r ++ ([.zeichen ")"] ++ W))) := by
    intro G5 hG5
    have hbar := tower_up_bitbar l ([.zeichen op] ++
      (druckToks r ++ ([.zeichen ")"] ++ W))) hUl hMul hAdd
    exact hbar.2 G5 hG5
  -- Right operand at `parseAdd` with the `)` follow.
  have hAr : ∀ (G5x : Nat),
      12 * (groesse r + 1) + groesse r + 4 ≤ G5x →
      parseAdd G5x (druckToks r ++ ([.zeichen ")"] ++ W)) =
        .ok (r, [.zeichen ")"] ++ W) := by
    intro G5x hG5x
    have hup := tower_up r ([.zeichen ")"] ++ W) (hr_paren W) hUr
    exact hup.2.1 G5x hG5x
  -- The `parseBit` core: `l`, consume the operator, `r`, stop
  -- at `)` (one flat-loop iteration, then the second
  -- `parseBitL` strip stops fuel-free).
  have hBit : ∀ (G3 : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 7 ≤ G3 →
      parseBit G3 (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
    intro G3 hG3
    have h31 : 1 ≤ G3 := by omega
    obtain ⟨G4, rfl⟩ : ∃ G4, G3 = G4 + 1 := ⟨G3 - 1, by omega⟩
    have hAl' := hAl G4 (by omega)
    have h32 : 1 ≤ G4 := by omega
    obtain ⟨G4x, rfl⟩ : ∃ G4x, G4 = G4x + 1 := ⟨G4 - 1, by omega⟩
    have hAr' := hAr G4x (by omega)
    have h33 : 1 ≤ G4x := by omega
    obtain ⟨G4y, rfl⟩ : ∃ G4y, G4x = G4y + 1 := ⟨G4x - 1, by omega⟩
    have hstop := opBit_paren W
    simp only [parseBit, parseBitL, hAl', hop, hAr', hstop] at ⊢
  -- Up the pass-through levels, each stopping at `)`.
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

-- Bit legs from operand legs: assemble the `parseUnary` legs
-- (suffix/float follows from the bar facts, `)` follows by
-- `rfl`-lemmas), run the generic inner trace, climb the generic
-- tower.
theorem bitLegs : ∀ (op : String) (l r : SExpr),
    istBitOp op = true → Legs l → Legs r → Legs (.bin op l r) := by
  intro op l r hop Hl Hr
  apply bin_turm3 op l r
  intro T G hG
  obtain ⟨hmMul, hmAdd, hrsS1, hrgS1⟩ :=
    bitbar_facts op (druckToks r ++ ([.zeichen ")"] ++ T)) hop
  have hhit := opBit_bit_hit op
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
  exact bitB_step op l r T hUl hUr hmMul hmAdd hhit G hG

-- The new bit layer: one bit operator over level-1 trees
-- (disjoint from `gutCmp` -- neither `gutKern` nor `cmpNeu`
-- has a bit spelling).
def bitNeu : SExpr → Bool
  | .bin o l r => istBitOp o && gutCmp l && gutCmp r
  | _ => false

-- Level-2 predicate: level 1 plus one bit layer.
def gutBit (e : SExpr) : Bool := gutCmp e || bitNeu e

-- Every level-2 tree has legs: level-1 trees by `legsCmp`, new
-- bit nodes by `bitLegs` over level-1 legs.
theorem legsBit : ∀ (e : SExpr), gutBit e = true → Legs e := by
  intro e hg
  simp only [gutBit, Bool.or_eq_true] at hg
  obtain hold | hnew := hg
  · exact legsCmp e hold
  · cases e with
    | lit m => simp only [bitNeu, Bool.false_eq_true] at hnew
    | float s => simp only [bitNeu, Bool.false_eq_true] at hnew
    | tru => simp only [bitNeu, Bool.false_eq_true] at hnew
    | fls => simp only [bitNeu, Bool.false_eq_true] at hnew
    | «variable» s => simp only [bitNeu, Bool.false_eq_true] at hnew
    | un o x => simp only [bitNeu, Bool.false_eq_true] at hnew
    | bin o l r =>
      simp only [bitNeu, Bool.and_eq_true, and_assoc] at hnew
      obtain ⟨hop, hl, hr2⟩ := hnew
      have Hl := legsCmp l hl
      have Hr := legsCmp r hr2
      have hbo : istBitOp o = true := hop
      obtain rfl | rfl | rfl | rfl | rfl | rfl := bit_is o hop
      · exact bitLegs "&" l r hbo Hl Hr
      · exact bitLegs "|" l r hbo Hl Hr
      · exact bitLegs "^" l r hbo Hl Hr
      · exact bitLegs "<<" l r hbo Hl Hr
      · exact bitLegs ">>" l r hbo Hl Hr
      · exact bitLegs "<<%" l r hbo Hl Hr
    | field x f => simp only [bitNeu, Bool.false_eq_true] at hnew
    | index x i => simp only [bitNeu, Bool.false_eq_true] at hnew
    | arrow x f => simp only [bitNeu, Bool.false_eq_true] at hnew
    | call f xs => simp only [bitNeu, Bool.false_eq_true] at hnew
    | fnref f => simp only [bitNeu, Bool.false_eq_true] at hnew
    | built f xs => simp only [bitNeu, Bool.false_eq_true] at hnew
    | old x => simp only [bitNeu, Bool.false_eq_true] at hnew
    | res => simp only [bitNeu, Bool.false_eq_true] at hnew
    | why g f => simp only [bitNeu, Bool.false_eq_true] at hnew
    | ext xk xn xs => simp only [bitNeu, Bool.false_eq_true] at hnew

-- Level-2 goal: every `gutBit` tree parses back from its printed
-- tokens with `brennstoff` fuel.
theorem parse_druck_bit : ∀ (e : SExpr), gutBit e = true →
    parseOr (brennstoff e) (druckToks e ++ [.ende]) =
      .ok (e, [.ende]) := by
  intro e hg
  have hL := legsBit e hg
  have hr : ruhig [.ende] = true := rfl
  have hrs : ruhigSuff [.ende] = true := rfl
  have hrg : ruhigGleit [.ende] = true := rfl
  have hF : 12 * (groesse e + 1) + groesse e + 8 ≤ brennstoff e := by
    simp only [brennstoff, Std.le_refl]
  exact hL.2.2.2.2.2.2.2 [.ende] (brennstoff e) hr hrs hrg hF

-- Level-2 witnesses, corpus-flavoured (`45-gemischte-
-- registerklasse` masks a device word with `&`, shifts with
-- `<<`): each as a `parse_druck_bit` instance and a
-- kernel-computed `match` check.
theorem zeuge_bit_and :
    parseOr (brennstoff (.bin "&" (.variable "v") (.lit 1)))
    (druckToks (.bin "&" (.variable "v") (.lit 1)) ++ [.ende]) =
      .ok (.bin "&" (.variable "v") (.lit 1), [.ende]) :=
  parse_druck_bit _ (by decide)
theorem zeuge_bit_and_rech : (match parseOr
    (brennstoff (.bin "&" (.variable "v") (.lit 1)))
    (druckToks (.bin "&" (.variable "v") (.lit 1)) ++ [.ende]) with
    | .ok (.bin "&" (.variable "v") (.lit 1), [.ende]) => true
    | _ => false) = true := by
  decide
theorem zeuge_bit_shl :
    parseOr (brennstoff (.bin "<<" (.lit 1) (.variable "n")))
    (druckToks (.bin "<<" (.lit 1) (.variable "n")) ++ [.ende]) =
      .ok (.bin "<<" (.lit 1) (.variable "n"), [.ende]) :=
  parse_druck_bit _ (by decide)
theorem zeuge_bit_shl_rech : (match parseOr
    (brennstoff (.bin "<<" (.lit 1) (.variable "n")))
    (druckToks (.bin "<<" (.lit 1) (.variable "n")) ++ [.ende]) with
    | .ok (.bin "<<" (.lit 1) (.variable "n"), [.ende]) => true
    | _ => false) = true := by
  decide

-- LEVEL ADD/MUL-REST (the remaining spellings: `-`, `+%`,
-- `-%`, `+|` ride `parseAddL`; `/`, `%`, `*%` ride `parseMulL`).
-- Same loops as `+`/`*`: one generic trace per loop, then
-- op-table facts per spelling.
theorem add_is : ∀ (o : String), istAddOp o = true →
    o = "+" ∨ o = "-" ∨ o = "+%" ∨ o = "-%" ∨ o = "+|" := by
  intro o h
  simp only [istAddOp, Bool.or_eq_true] at h
  obtain h4 | hF := h
  · obtain h3 | hE := h4
    · obtain h2 | hD := h3
      · obtain hA | hB := h2
        · exact Or.inl (strKlingt o "+" hA)
        · exact Or.inr (Or.inl (strKlingt o "-" hB))
      · exact Or.inr (Or.inr (Or.inl (strKlingt o "+%" hD)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (strKlingt o "-%" hE))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (strKlingt o "+|" hF))))
theorem mul_is : ∀ (o : String), istMulOp o = true →
    o = "*" ∨ o = "/" ∨ o = "%" ∨ o = "*%" := by
  intro o h
  simp only [istMulOp, Bool.or_eq_true] at h
  obtain h3 | hD := h
  · obtain h2 | hC := h3
    · obtain hA | hB := h2
      · exact Or.inl (strKlingt o "*" hA)
      · exact Or.inr (Or.inl (strKlingt o "/" hB))
    · exact Or.inr (Or.inr (Or.inl (strKlingt o "%" hC)))
  · exact Or.inr (Or.inr (Or.inr (strKlingt o "*%" hD)))

-- Facts for an add-loop follow: `parseMulL` misses it (every
-- other level consumes or stops elsewhere), and the
-- suffix/float tails are benign. One bundle for all five
-- spellings (each case `rfl`).
theorem addbar_facts : ∀ (op : String) (T : List Token),
    istAddOp op = true →
    opMul ([.zeichen op] ++ T) = none ∧
    ruhigSuff ([.zeichen op] ++ T) = true ∧
    ruhigGleit ([.zeichen op] ++ T) = true := by
  intro op T h
  obtain rfl | rfl | rfl | rfl | rfl := add_is op h
  · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩

-- The add table hits its own spelling (all five; each `rfl`).
theorem opAdd_add_hit : ∀ (op : String) (T : List Token),
    istAddOp op = true →
    opAdd ([.zeichen op] ++ T) = some (op, T) := by
  intro op T h
  obtain rfl | rfl | rfl | rfl | rfl := add_is op h
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

-- Facts for a mul-loop follow: only the benign suffix/float
-- tails (`parseMulL` itself consumes the operator; no lower
-- loop sees it). One bundle for all four spellings.
theorem mulbar_facts : ∀ (op : String) (T : List Token),
    istMulOp op = true →
    ruhigSuff ([.zeichen op] ++ T) = true ∧
    ruhigGleit ([.zeichen op] ++ T) = true := by
  intro op T h
  obtain rfl | rfl | rfl | rfl := mul_is op h
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

-- The mul table hits its own spelling (all four; each `rfl`).
theorem opMul_mul_hit : ∀ (op : String) (T : List Token),
    istMulOp op = true →
    opMul ([.zeichen op] ++ T) = some (op, T) := by
  intro op T h
  obtain rfl | rfl | rfl | rfl := mul_is op h
  · rfl
  · rfl
  · rfl
  · rfl

end Gabbro.Grammatik.Parser
