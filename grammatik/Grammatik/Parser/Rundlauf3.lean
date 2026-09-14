/-
  File:      Grammatik/Parser/Rundlauf3.lean
  Subject:   T3 (lane 179): finish the round-trip induction -- widen the
              predicate level by level (MUSE-REPORT-172 "Open" first).

  Lane 172 proved `parse_druck_kern` for `gutKern` by a joint SIZE
  induction (`kernRB`: `RKern n` with four binary-inner invariants),
  and listed the remaining levels with exact blockers: comparisons
  (`BKernCmp`, ~150 lines), bit operators (`BKernBit`, the `+` shape
  one level up), the remaining add/mul spellings (one B-trace
  duplicate plus op-table facts each), calls with argument lists
  (`parseArgs` round trip, ~200 lines), and `sizeof`/`lenof`/
  `aligned` (resisted in lane 161).

  This file takes a different, cheaper road to the same widening.
  Observation: every B-step in Rundlauf2 uses its invariant ONLY at
  strict subterms (the operand legs), and every tower takes its B-leg
  as a hypothesis. So instead of re-running a joint size induction
  per level, this file works with predicate-free legs:

  - `Legs e`: the eight fuel-generalised round-trip legs for ONE
    fixed tree (the `RKern` leg shapes with the size bound dropped).
  - `legsKern`: every `gutKern` tree has legs (repackaged `kernRB`).
  - one generic B-step per new operator group (taking operand legs
    plus op-table facts as hypotheses, no predicate anywhere), one
    generic spelling-blind tower (B-leg to eight legs).

  Each level then defines its predicate as the previous predicate
  plus ONE new layer over the previous predicate's trees, and proves
  legs for it from the previous level's legs. No joint induction is
  re-proved at any level; each level is one green commit.

  Honest limitation (measured, not assumed): each level covers one
  layer of its operators over the previous predicate -- `==` over
  `&` needs the `&` level below the `==` node, which the order
  (comparisons first) does not give. Arbitrary NESTING of new
  operators needs the joint size induction over a recursive
  predicate (lane 172's architecture, ~500 lines to replay the four
  old B-steps over abstract legs). That is the exact remaining
  blocker for full `gut`, stated at the end of this file.
-/
import Grammatik.Parser.Rundlauf2

namespace Gabbro.Grammatik.Parser

-- The eight fuel-generalised round-trip legs for one fixed tree:
-- the `RKern` leg shapes with the size bound and the predicate
-- dropped. `parseUnary` takes no `ruhig` premise (it runs no
-- loop); `parsePrimary` takes `primFrei` (prefix trees live at
-- the unary level). Bounds copy `RKern` exactly (`+1` at
-- `parsePrimary` up to `+8` at `parseOr`).
def Legs (e : SExpr) : Prop :=
  (∀ (rest : List Token) (G : Nat), primFrei e = true →
    ruhigSuff rest = true → ruhigGleit rest = true →
    12 * (groesse e + 1) + groesse e + 1 ≤ G →
    parsePrimary G (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (rest : List Token) (G : Nat), ruhigSuff rest = true →
    ruhigGleit rest = true →
    12 * (groesse e + 1) + groesse e + 2 ≤ G →
    parseUnary G (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (rest : List Token) (G : Nat), ruhig rest = true →
    ruhigSuff rest = true → ruhigGleit rest = true →
    12 * (groesse e + 1) + groesse e + 3 ≤ G →
    parseMul G (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (rest : List Token) (G : Nat), ruhig rest = true →
    ruhigSuff rest = true → ruhigGleit rest = true →
    12 * (groesse e + 1) + groesse e + 4 ≤ G →
    parseAdd G (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (rest : List Token) (G : Nat), ruhig rest = true →
    ruhigSuff rest = true → ruhigGleit rest = true →
    12 * (groesse e + 1) + groesse e + 5 ≤ G →
    parseBit G (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (rest : List Token) (G : Nat), ruhig rest = true →
    ruhigSuff rest = true → ruhigGleit rest = true →
    12 * (groesse e + 1) + groesse e + 6 ≤ G →
    parseCmp G (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (rest : List Token) (G : Nat), ruhig rest = true →
    ruhigSuff rest = true → ruhigGleit rest = true →
    12 * (groesse e + 1) + groesse e + 7 ≤ G →
    parseAnd G (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (rest : List Token) (G : Nat), ruhig rest = true →
    ruhigSuff rest = true → ruhigGleit rest = true →
    12 * (groesse e + 1) + groesse e + 8 ≤ G →
    parseOr G (druckToks e ++ rest) = .ok (e, rest))

-- Every `gutKern` tree has legs: the `Or`-through-`Primary` legs
-- of `kernRB` at `groesse e`, repackaged (the size premise closes
-- by reflexivity).
theorem legsKern : ∀ (e : SExpr), gutKern e = true → Legs e := by
  intro e hg
  have hRB := (kernRB (groesse e)).1
  obtain ⟨rOr, rAnd, rCmp, rBit, rAdd, rMul, rUn, rPr⟩ := hRB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro rest G hpf hrs hrg hG
    exact rPr e rest G (Nat.le_refl _) hg hpf hrs hrg hG
  · intro rest G hrs hrg hG
    exact rUn e rest G (Nat.le_refl _) hg hrs hrg hG
  · intro rest G hr hrs hrg hG
    exact rMul e rest G (Nat.le_refl _) hg hr hrs hrg hG
  · intro rest G hr hrs hrg hG
    exact rAdd e rest G (Nat.le_refl _) hg hr hrs hrg hG
  · intro rest G hr hrs hrg hG
    exact rBit e rest G (Nat.le_refl _) hg hr hrs hrg hG
  · intro rest G hr hrs hrg hG
    exact rCmp e rest G (Nat.le_refl _) hg hr hrs hrg hG
  · intro rest G hr hrs hrg hG
    exact rAnd e rest G (Nat.le_refl _) hg hr hrs hrg hG
  · intro rest G hr hrs hrg hG
    exact rOr e rest G (Nat.le_refl _) hg hr hrs hrg hG

-- LEVEL CMP (comparisons `==`, `!=`, `<=`, `>=`, `<`, `>`).
--
-- A lawful comparison spelling names itself: the six cases of
-- `istCmpOp`.
theorem cmp_is : ∀ (o : String), istCmpOp o = true →
    o = "==" ∨ o = "!=" ∨ o = "<=" ∨ o = ">=" ∨ o = "<" ∨ o = ">" := by
  intro o h
  simp only [istCmpOp, Bool.or_eq_true] at h
  obtain h5 | hF := h
  · obtain h4 | hE := h5
    · obtain h3 | hD := h4
      · obtain h2 | hC := h3
        · obtain hA | hB := h2
          · exact Or.inl (strKlingt o "==" hA)
          · exact Or.inr (Or.inl (strKlingt o "!=" hB))
        · exact Or.inr (Or.inr (Or.inl (strKlingt o "<=" hC)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (strKlingt o ">=" hD))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (strKlingt o "<" hE)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (strKlingt o ">" hF)))))

-- Facts for a comparison-operator follow: every loop below
-- `parseCmp` misses it (`parseCmp` itself consumes it -- the
-- single-shot level has no loop), and the suffix/float tails are
-- benign. One bundle for all six spellings (each case `rfl`).
theorem cmpbar_facts : ∀ (op : String) (T : List Token),
    istCmpOp op = true →
    opMul ([.zeichen op] ++ T) = none ∧
    opAdd ([.zeichen op] ++ T) = none ∧
    opBit ([.zeichen op] ++ T) = none ∧
    ruhigSuff ([.zeichen op] ++ T) = true ∧
    ruhigGleit ([.zeichen op] ++ T) = true := by
  intro op T h
  obtain rfl | rfl | rfl | rfl | rfl | rfl := cmp_is op h
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩

-- The comparison table hits its own spelling (one lemma for all
-- six spellings; each case `rfl`).
theorem opVgl_cmp_hit : ∀ (op : String) (T : List Token),
    istCmpOp op = true →
    opVgl ([.zeichen op] ++ T) = some (op, T) := by
  intro op T h
  obtain rfl | rfl | rfl | rfl | rfl | rfl := cmp_is op h
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

-- The `parseBit`-level bar tower for a comparison follow: from
-- the `parseUnary` leg, the three loop levels below `parseCmp`
-- each run their child and stop on the operator. Mirror of
-- `tower_up_orbar` (which stops five levels on `||`); here the
-- tower stops at `parseBit` because `parseCmp` consumes.
theorem tower_up_cmpbar : ∀ (l : SExpr) (S1 : List Token),
    (∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 2 ≤ G →
      parseUnary G (druckToks l ++ S1) = .ok (l, S1)) →
    opMul S1 = none → opAdd S1 = none → opBit S1 = none →
    (∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 3 ≤ G →
      parseMul G (druckToks l ++ S1) = .ok (l, S1))
    ∧ (∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 4 ≤ G →
      parseAdd G (druckToks l ++ S1) = .ok (l, S1))
    ∧ (∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 5 ≤ G →
      parseBit G (druckToks l ++ S1) = .ok (l, S1)) := by
  intro l S1 hU hMul hAdd hBit
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
  have hB : ∀ (G : Nat),
      12 * (groesse l + 1) + groesse l + 5 ≤ G →
      parseBit G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hA' := hA G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    simp only [parseBit, parseBitL, hA', hBit] at ⊢
  exact ⟨hM, hA, hB⟩

-- The comparison inner trace, generic over the spelling: the
-- left operand parses at `parseBit` with the operator follow,
-- `parseCmp` consumes the operator and the right operand in one
-- shot (no loop), and `parseAnd`/`parseOr` stop at `)`. Same
-- `+10` fuel as every other B-trace. No predicate anywhere: the
-- operand legs and the op-table facts arrive as hypotheses.
theorem cmpB_step : ∀ (op : String) (l r : SExpr) (W : List Token),
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
    opBit ([.zeichen op] ++ (druckToks r ++ ([.zeichen ")"] ++ W))) = none →
    opVgl ([.zeichen op] ++ (druckToks r ++ ([.zeichen ")"] ++ W))) =
      some (op, druckToks r ++ ([.zeichen ")"] ++ W)) →
    ∀ (G : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen op] ++ druckToks r ++
        [.zeichen ")"] ++ W) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
  intro op l r W hUl hUr hMul hAdd hBit hop G hG
  have hpos_l := groesse_pos l
  have hpos_r := groesse_pos r
  simp only [List.append_assoc] at ⊢
  -- Left operand at `parseBit` with the operator follow.
  have hBl : ∀ (G5 : Nat),
      12 * (groesse l + 1) + groesse l + 5 ≤ G5 →
      parseBit G5 (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (l, [.zeichen op] ++
          (druckToks r ++ ([.zeichen ")"] ++ W))) := by
    intro G5 hG5
    have hbar := tower_up_cmpbar l ([.zeichen op] ++
      (druckToks r ++ ([.zeichen ")"] ++ W))) hUl hMul hAdd hBit
    exact hbar.2.2 G5 hG5
  -- Right operand at `parseBit` with the `)` follow.
  have hBr : ∀ (G5x : Nat),
      12 * (groesse r + 1) + groesse r + 5 ≤ G5x →
      parseBit G5x (druckToks r ++ ([.zeichen ")"] ++ W)) =
        .ok (r, [.zeichen ")"] ++ W) := by
    intro G5x hG5x
    have hup := tower_up r ([.zeichen ")"] ++ W) (hr_paren W) hUr
    exact hup.2.2.1 G5x hG5x
  -- The `parseCmp` core: `l`, consume the operator, `r`. No
  -- loop stop: the single-shot level has no loop.
  have hCmp : ∀ (G2 : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 8 ≤ G2 →
      parseCmp G2 (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
    intro G2 hG2
    have h21 : 1 ≤ G2 := by omega
    obtain ⟨G3, rfl⟩ : ∃ G3, G2 = G3 + 1 := ⟨G2 - 1, by omega⟩
    have hBl' := hBl G3 (by omega)
    have hBr' := hBr G3 (by omega)
    simp only [parseCmp, hBl', hop, hBr'] at ⊢
  -- Up the pass-through levels, each stopping at `)`.
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

-- The binary tower from a binary-inner leg, generic over the
-- spelling AND the tail: the `parsePrimary` leg runs the `(`
-- arm over the inner parse, the `parseUnary` leg falls through
-- on `(`, then `tower_up`. No proof step inspects the spelling
-- (the printer parenthesises every binary operator), so this one
-- lemma serves all six comparison spellings -- and every later
-- level. Takes NO predicate hypotheses (unlike `kern_bin_turm`,
-- whose two `gutKern` premises its own proof never uses).
theorem bin_turm3 : ∀ (op : String) (l r : SExpr),
    (∀ (T : List Token) (G : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen op] ++ druckToks r ++
        [.zeichen ")"] ++ T) =
        .ok (.bin op l r, [.zeichen ")"] ++ T)) →
    Legs (.bin op l r) := by
  intro op l r hBgen
  have hsize : groesse (.bin op l r) = groesse l + groesse r + 1 := rfl
  have hd : druckToks (.bin op l r) = [.zeichen "("] ++ druckToks l ++
      [.zeichen op] ++ druckToks r ++ [.zeichen ")"] := by
    simp [druckToks]
  have hP : ∀ (rest' : List Token) (G : Nat),
      12 * (groesse (.bin op l r) + 1) + groesse (.bin op l r) + 1 ≤ G →
      parsePrimary G (druckToks (.bin op l r) ++ rest') =
        .ok (.bin op l r, rest') := by
    intro rest' G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hB' := hBgen rest' G' (by omega)
    have hPar := paren_arm _ _ _ _ hB'
    simp only [hd, List.append_assoc] at ⊢
    simp only [List.append_assoc] at hPar
    exact hPar
  have hU : ∀ (rest' : List Token) (G : Nat),
      12 * (groesse (.bin op l r) + 1) + groesse (.bin op l r) + 2 ≤ G →
      parseUnary G (druckToks (.bin op l r) ++ rest') =
        .ok (.bin op l r, rest') := by
    intro rest' G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hP' := hP rest' G' (by omega)
    simp only [hd, List.append_assoc] at hP' ⊢
    exact un_paren_fall _ _ _ _ hP'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro rest' G hpf hrs hrg hG
    exact hP rest' G hG
  · intro rest' G hrs hrg hG
    exact hU rest' G hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up (.bin op l r) rest' hr (hU rest')).1 G hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up (.bin op l r) rest' hr (hU rest')).2.1 G hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up (.bin op l r) rest' hr (hU rest')).2.2.1 G hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up (.bin op l r) rest' hr (hU rest')).2.2.2.1 G hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up (.bin op l r) rest' hr (hU rest')).2.2.2.2.1 G hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up (.bin op l r) rest' hr (hU rest')).2.2.2.2.2 G hG

-- Comparison legs from operand legs: assemble the `parseUnary`
-- legs (suffix/float follows from the bar facts, `)` follows by
-- `rfl`-lemmas), run the generic inner trace, climb the generic
-- tower. The only comparison-specific inputs are the lawfulness
-- `hop` and the two kernel legs.
theorem cmpLegs : ∀ (op : String) (l r : SExpr),
    istCmpOp op = true → Legs l → Legs r → Legs (.bin op l r) := by
  intro op l r hop Hl Hr
  apply bin_turm3 op l r
  intro T G hG
  obtain ⟨hmMul, hmAdd, hmBit, hrsS1, hrgS1⟩ :=
    cmpbar_facts op (druckToks r ++ ([.zeichen ")"] ++ T)) hop
  have hhit := opVgl_cmp_hit op
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
  exact cmpB_step op l r T hUl hUr hmMul hmAdd hmBit hhit G hG

-- The new comparison layer: one comparison over kernel trees
-- (disjoint from `gutKern` by construction -- `gutKern` has no
-- comparison spelling).
def cmpNeu : SExpr → Bool
  | .bin o l r => istCmpOp o && gutKern l && gutKern r
  | _ => false

-- Level-1 predicate: the kernel plus one comparison layer.
def gutCmp (e : SExpr) : Bool := gutKern e || cmpNeu e

-- Every level-1 tree has legs: kernel trees by `legsKern`, new
-- comparison nodes by `cmpLegs` over kernel legs. The six
-- spellings differ only in the lawfulness fact each case
-- supplies.
theorem legsCmp : ∀ (e : SExpr), gutCmp e = true → Legs e := by
  intro e hg
  simp only [gutCmp, Bool.or_eq_true] at hg
  obtain hker | hnew := hg
  · exact legsKern e hker
  · cases e with
    | lit m => simp [cmpNeu] at hnew
    | gleit s => simp [cmpNeu] at hnew
    | wahr => simp [cmpNeu] at hnew
    | falsch => simp [cmpNeu] at hnew
    | «variable» s => simp [cmpNeu] at hnew
    | un o x => simp [cmpNeu] at hnew
    | bin o l r =>
      simp only [cmpNeu, Bool.and_eq_true, and_assoc] at hnew
      obtain ⟨hop, hl, hr2⟩ := hnew
      have Hl := legsKern l hl
      have Hr := legsKern r hr2
      have hco : istCmpOp o = true := hop
      obtain rfl | rfl | rfl | rfl | rfl | rfl := cmp_is o hop
      · exact cmpLegs "==" l r hco Hl Hr
      · exact cmpLegs "!=" l r hco Hl Hr
      · exact cmpLegs "<=" l r hco Hl Hr
      · exact cmpLegs ">=" l r hco Hl Hr
      · exact cmpLegs "<" l r hco Hl Hr
      · exact cmpLegs ">" l r hco Hl Hr
    | feld x f => simp [cmpNeu] at hnew
    | index x i => simp [cmpNeu] at hnew
    | pfeil x f => simp [cmpNeu] at hnew
    | ruf f xs => simp [cmpNeu] at hnew
    | fnwert f => simp [cmpNeu] at hnew
    | eingebaut f xs => simp [cmpNeu] at hnew
    | alt x => simp [cmpNeu] at hnew
    | ergebnis => simp [cmpNeu] at hnew
    | grund g f => simp [cmpNeu] at hnew

-- Level-1 goal: every `gutCmp` tree parses back from its printed
-- tokens with `brennstoff` fuel (the `Or` leg, `ende` follows by
-- `rfl`, fuel exactly `brennstoff`).
theorem parse_druck_cmp : ∀ (e : SExpr), gutCmp e = true →
    parseOr (brennstoff e) (druckToks e ++ [.ende]) =
      .ok (e, [.ende]) := by
  intro e hg
  have hL := legsCmp e hg
  have hr : ruhig [.ende] = true := rfl
  have hrs : ruhigSuff [.ende] = true := rfl
  have hrg : ruhigGleit [.ende] = true := rfl
  have hF : 12 * (groesse e + 1) + groesse e + 8 ≤ brennstoff e := by
    simp [brennstoff]
  exact hL.2.2.2.2.2.2.2 [.ende] (brennstoff e) hr hrs hrg hF

-- Level-1 witnesses, corpus-flavoured (`01-tabelle` compares a
-- field against a literal with `==`; `04-schleifen` bounds a
-- counter with `<`): each as a `parse_druck_cmp` instance and a
-- kernel-computed `match` check.
theorem zeuge_cmp_eq :
    parseOr (brennstoff (.bin "==" (.feld (.variable "c") "x") (.lit 0)))
    (druckToks (.bin "==" (.feld (.variable "c") "x") (.lit 0)) ++ [.ende]) =
      .ok (.bin "==" (.feld (.variable "c") "x") (.lit 0), [.ende]) :=
  parse_druck_cmp _ (by decide)
theorem zeuge_cmp_eq_rech : (match parseOr
    (brennstoff (.bin "==" (.feld (.variable "c") "x") (.lit 0)))
    (druckToks (.bin "==" (.feld (.variable "c") "x") (.lit 0)) ++ [.ende]) with
    | .ok (.bin "==" (.feld (.variable "c") "x") (.lit 0), [.ende]) => true
    | _ => false) = true := by
  decide
theorem zeuge_cmp_lt :
    parseOr (brennstoff (.bin "<" (.variable "s") (.lit 64)))
    (druckToks (.bin "<" (.variable "s") (.lit 64)) ++ [.ende]) =
      .ok (.bin "<" (.variable "s") (.lit 64), [.ende]) :=
  parse_druck_cmp _ (by decide)
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
    | lit m => simp [bitNeu] at hnew
    | gleit s => simp [bitNeu] at hnew
    | wahr => simp [bitNeu] at hnew
    | falsch => simp [bitNeu] at hnew
    | «variable» s => simp [bitNeu] at hnew
    | un o x => simp [bitNeu] at hnew
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
    | feld x f => simp [bitNeu] at hnew
    | index x i => simp [bitNeu] at hnew
    | pfeil x f => simp [bitNeu] at hnew
    | ruf f xs => simp [bitNeu] at hnew
    | fnwert f => simp [bitNeu] at hnew
    | eingebaut f xs => simp [bitNeu] at hnew
    | alt x => simp [bitNeu] at hnew
    | ergebnis => simp [bitNeu] at hnew
    | grund g f => simp [bitNeu] at hnew

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
    simp [brennstoff]
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
      | lit m => simp [addNeu] at hadd
      | gleit s => simp [addNeu] at hadd
      | wahr => simp [addNeu] at hadd
      | falsch => simp [addNeu] at hadd
      | «variable» s => simp [addNeu] at hadd
      | un o x => simp [addNeu] at hadd
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
      | feld x f => simp [addNeu] at hadd
      | index x i => simp [addNeu] at hadd
      | pfeil x f => simp [addNeu] at hadd
      | ruf f xs => simp [addNeu] at hadd
      | fnwert f => simp [addNeu] at hadd
      | eingebaut f xs => simp [addNeu] at hadd
      | alt x => simp [addNeu] at hadd
      | ergebnis => simp [addNeu] at hadd
      | grund g f => simp [addNeu] at hadd
  · cases e with
    | lit m => simp [mulNeu] at hnew
    | gleit s => simp [mulNeu] at hnew
    | wahr => simp [mulNeu] at hnew
    | falsch => simp [mulNeu] at hnew
    | «variable» s => simp [mulNeu] at hnew
    | un o x => simp [mulNeu] at hnew
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
    | feld x f => simp [mulNeu] at hnew
    | index x i => simp [mulNeu] at hnew
    | pfeil x f => simp [mulNeu] at hnew
    | ruf f xs => simp [mulNeu] at hnew
    | fnwert f => simp [mulNeu] at hnew
    | eingebaut f xs => simp [mulNeu] at hnew
    | alt x => simp [mulNeu] at hnew
    | ergebnis => simp [mulNeu] at hnew
    | grund g f => simp [mulNeu] at hnew

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
    simp [brennstoff]
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
  simp [gutOpBin, gutOpCmp, h]
theorem gutOpBin_of_bit : ∀ (o : String),
    istBitOp o = true → gutOpBin o = true := by
  intro o h
  simp [gutOpBin, gutOpBit, h]
theorem gutOpBin_of_add : ∀ (o : String),
    istAddOp o = true → gutOpBin o = true := by
  intro o h
  simp [gutOpBin, gutOpAdd, h]
theorem gutOpBin_of_mul : ∀ (o : String),
    istMulOp o = true → gutOpBin o = true := by
  intro o h
  simp [gutOpBin, gutOpMul, h]

theorem gut_of_gutCmp : ∀ (e : SExpr), gutCmp e = true → gut e = true := by
  intro e hg
  simp only [gutCmp, Bool.or_eq_true] at hg
  obtain hker | hnew := hg
  · exact gut_of_gutKern e hker
  · cases e with
    | lit m => simp [cmpNeu] at hnew
    | gleit s => simp [cmpNeu] at hnew
    | wahr => simp [cmpNeu] at hnew
    | falsch => simp [cmpNeu] at hnew
    | «variable» s => simp [cmpNeu] at hnew
    | un o x => simp [cmpNeu] at hnew
    | bin o l r =>
      simp only [cmpNeu, Bool.and_eq_true, and_assoc] at hnew
      obtain ⟨hop, hl, hr2⟩ := hnew
      have hbin := gutOpBin_of_cmp o hop
      simp only [gut, Bool.and_eq_true, and_assoc] at ⊢
      exact ⟨hbin, gut_of_gutKern l hl, gut_of_gutKern r hr2⟩
    | feld x f => simp [cmpNeu] at hnew
    | index x i => simp [cmpNeu] at hnew
    | pfeil x f => simp [cmpNeu] at hnew
    | ruf f xs => simp [cmpNeu] at hnew
    | fnwert f => simp [cmpNeu] at hnew
    | eingebaut f xs => simp [cmpNeu] at hnew
    | alt x => simp [cmpNeu] at hnew
    | ergebnis => simp [cmpNeu] at hnew
    | grund g f => simp [cmpNeu] at hnew

theorem gut_of_gutBit : ∀ (e : SExpr), gutBit e = true → gut e = true := by
  intro e hg
  simp only [gutBit, Bool.or_eq_true] at hg
  obtain hold | hnew := hg
  · exact gut_of_gutCmp e hold
  · cases e with
    | lit m => simp [bitNeu] at hnew
    | gleit s => simp [bitNeu] at hnew
    | wahr => simp [bitNeu] at hnew
    | falsch => simp [bitNeu] at hnew
    | «variable» s => simp [bitNeu] at hnew
    | un o x => simp [bitNeu] at hnew
    | bin o l r =>
      simp only [bitNeu, Bool.and_eq_true, and_assoc] at hnew
      obtain ⟨hop, hl, hr2⟩ := hnew
      have hbin := gutOpBin_of_bit o hop
      simp only [gut, Bool.and_eq_true, and_assoc] at ⊢
      exact ⟨hbin, gut_of_gutCmp l hl, gut_of_gutCmp r hr2⟩
    | feld x f => simp [bitNeu] at hnew
    | index x i => simp [bitNeu] at hnew
    | pfeil x f => simp [bitNeu] at hnew
    | ruf f xs => simp [bitNeu] at hnew
    | fnwert f => simp [bitNeu] at hnew
    | eingebaut f xs => simp [bitNeu] at hnew
    | alt x => simp [bitNeu] at hnew
    | ergebnis => simp [bitNeu] at hnew
    | grund g f => simp [bitNeu] at hnew

theorem gut_of_gutAM : ∀ (e : SExpr), gutAM e = true → gut e = true := by
  intro e hg
  simp only [gutAM, Bool.or_eq_true] at hg
  obtain hold | hnew := hg
  · obtain hold2 | hadd := hold
    · exact gut_of_gutBit e hold2
    · cases e with
      | lit m => simp [addNeu] at hadd
      | gleit s => simp [addNeu] at hadd
      | wahr => simp [addNeu] at hadd
      | falsch => simp [addNeu] at hadd
      | «variable» s => simp [addNeu] at hadd
      | un o x => simp [addNeu] at hadd
      | bin o l r =>
        simp only [addNeu, Bool.and_eq_true, and_assoc] at hadd
        obtain ⟨hop, hl, hr2⟩ := hadd
        have hbin := gutOpBin_of_add o hop
        simp only [gut, Bool.and_eq_true, and_assoc] at ⊢
        exact ⟨hbin, gut_of_gutBit l hl, gut_of_gutBit r hr2⟩
      | feld x f => simp [addNeu] at hadd
      | index x i => simp [addNeu] at hadd
      | pfeil x f => simp [addNeu] at hadd
      | ruf f xs => simp [addNeu] at hadd
      | fnwert f => simp [addNeu] at hadd
      | eingebaut f xs => simp [addNeu] at hadd
      | alt x => simp [addNeu] at hadd
      | ergebnis => simp [addNeu] at hadd
      | grund g f => simp [addNeu] at hadd
  · cases e with
    | lit m => simp [mulNeu] at hnew
    | gleit s => simp [mulNeu] at hnew
    | wahr => simp [mulNeu] at hnew
    | falsch => simp [mulNeu] at hnew
    | «variable» s => simp [mulNeu] at hnew
    | un o x => simp [mulNeu] at hnew
    | bin o l r =>
      simp only [mulNeu, Bool.and_eq_true, and_assoc] at hnew
      obtain ⟨hop, hl, hr2⟩ := hnew
      have hbin := gutOpBin_of_mul o hop
      simp only [gut, Bool.and_eq_true, and_assoc] at ⊢
      exact ⟨hbin, gut_of_gutBit l hl, gut_of_gutBit r hr2⟩
    | feld x f => simp [mulNeu] at hnew
    | index x i => simp [mulNeu] at hnew
    | pfeil x f => simp [mulNeu] at hnew
    | ruf f xs => simp [mulNeu] at hnew
    | fnwert f => simp [mulNeu] at hnew
    | eingebaut f xs => simp [mulNeu] at hnew
    | alt x => simp [mulNeu] at hnew
    | ergebnis => simp [mulNeu] at hnew
    | grund g f => simp [mulNeu] at hnew

-- LEVEL CALLS (calls with argument lists).
--
-- Lists of level-3 trees (computable, so `decide` witnesses
-- keep working).
def gutListeAM : List SExpr → Bool
  | [] => true
  | x :: xs => gutAM x && gutListeAM xs
theorem gutListeAM_Kopf : ∀ (x : SExpr) (xs : List SExpr),
    gutListeAM (x :: xs) = true → gutAM x = true := by
  intro x xs h
  simp only [gutListeAM, Bool.and_eq_true] at h
  exact h.1
theorem gutListeAM_Schwanz : ∀ (x : SExpr) (xs : List SExpr),
    gutListeAM (x :: xs) = true → gutListeAM xs = true := by
  intro x xs h
  simp only [gutListeAM, Bool.and_eq_true] at h
  exact h.2
-- A `gutListeAM` list is a `gutListe` (via the bridge) and
-- every element has legs.
theorem gutListe_of_gutListeAM : ∀ (xs : List SExpr),
    gutListeAM xs = true → gutListe xs = true := by
  intro xs h
  induction xs with
  | nil => rfl
  | cons x zs ih =>
    simp only [gutListeAM, Bool.and_eq_true] at h
    obtain ⟨hx, hzs⟩ := h
    simp only [gutListe, Bool.and_eq_true]
    exact ⟨gut_of_gutAM x hx, ih hzs⟩
theorem legsListeAM : ∀ (xs : List SExpr),
    gutListeAM xs = true → ∀ (x : SExpr), x ∈ xs → Legs x := by
  intro xs h x hm
  induction xs with
  | nil => simp at hm
  | cons y ys ih =>
    simp only [gutListeAM, Bool.and_eq_true] at h
    obtain ⟨hy, hys⟩ := h
    simp only [List.mem_cons] at hm
    obtain rfl | hm2 := hm
    · exact legsAM x hy
    · exact ih hys hm2

-- One argument through `parseArg`: mirror of lane 161's
-- `arg_einzeln`, with the `Legs` Or-leg instead of `R n` and
-- `keinDP_tree` instantiated at the tree's own size (no size
-- bound needed anywhere).
theorem arg_legs : ∀ (x : SExpr) (sep : Token) (S : List Token) (F : Nat),
    Legs x → gut x = true →
    (sep = .zeichen "," ∨ sep = .zeichen ")") →
    12 * (groesse x + 1) + groesse x + 9 ≤ F →
    parseArg F (druckToks x ++ [sep] ++ S) = .ok (x, [sep] ++ S) := by
  intro x sep S F hL hxg hsep hF
  have hF1 : 1 ≤ F := by omega
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  have hmiss : ∀ (t0 : Token) (rest : List Token),
      druckToks x ++ [sep] ++ S ≠ t0 :: .zeichen ":" :: rest := by
    intro t0 rest hcon
    have hne : druckToks x ≠ [] := by
      intro he
      have hlen := toksLang (groesse x) x (Nat.le_refl _)
      rw [he] at hlen
      simp at hlen
    obtain ⟨a, R2, hxb⟩ := List.exists_cons_of_ne_nil hne
    rw [hxb] at hcon
    simp only [List.cons_append] at hcon
    injection hcon with _ ht
    cases hR : R2 with
    | nil =>
      rw [hR] at ht
      simp only [List.nil_append, List.cons_append] at ht
      injection ht with hsep2 _
      cases hsep with
      | inl h =>
        subst h
        simp at hsep2
      | inr h =>
        subst h
        simp at hsep2
    | cons b R3 =>
      rw [hR] at ht
      simp only [List.cons_append] at ht
      injection ht with hb _
      have hbmem : b ∈ druckToks x := by simp [hxb, hR]
      have hne2 := keinDP_tree (groesse x) x (Nat.le_refl _) hxg b hbmem
      exact hne2 hb
  simp only [parseArg] at ⊢
  have hr1 : ruhig ([sep] ++ S) = true := by
    cases hsep with
    | inl h => subst h; rfl
    | inr h => subst h; rfl
  have hr2 : ruhigSuff ([sep] ++ S) = true := by
    cases hsep with
    | inl h => subst h; rfl
    | inr h => subst h; rfl
  have hr3 : ruhigGleit ([sep] ++ S) = true := by
    cases hsep with
    | inl h => subst h; rfl
    | inr h => subst h; rfl
  have hFr : 12 * (groesse x + 1) + groesse x + 8 ≤ F' := by omega
  have hOr := hL.2.2.2.2.2.2.2 ([sep] ++ S) F' hr1 hr2 hr3 hFr
  simpa only [List.append_assoc] using hOr

-- Whole argument lists through `parseArgs`: mirror of lane
-- 161's `args_rund` (head by `toksKopf` at the tree's own
-- size, element by `arg_legs`, tail by list induction).
theorem args_legs : ∀ (xs : List SExpr) (rest : List Token) (F : Nat),
    gutListeAM xs = true →
    12 * (groesseListe xs + 1) + groesseListe xs + 10 ≤ F →
    parseArgs F (druckToksListe xs ++ [.zeichen ")"] ++ rest) =
      .ok (xs, rest) := by
  intro xs
  induction xs with
  | nil =>
    intro rest F hs hF
    have hF1 : 1 ≤ F := by omega
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [parseArgs, druckToksListe, List.nil_append,
      List.cons_append]
  | cons x zs ihzs =>
    intro rest F hs hF
    cases zs with
    | nil =>
      have hx : gutAM x = true := gutListeAM_Kopf x [] hs
      have hxg : gut x = true := gut_of_gutAM x hx
      have hLx : Legs x := legsAM x hx
      have hkop : ∀ (a : Token) (R : List Token),
          druckToks x = a :: R → a ≠ .zeichen ")" :=
        toksKopf (groesse x) x (Nat.le_refl _) hxg
      have hF1 : 1 ≤ F := by omega
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      rw [args_einzeln] at ⊢
      have hmiss2 : ∀ (R2 : List Token),
          druckToks x ++ [.zeichen ")"] ++ rest ≠
            .zeichen ")" :: R2 := by
        intro R2 hcon
        have hne : druckToks x ≠ [] := by
          intro he
          have hlen := toksLang (groesse x) x (Nat.le_refl _)
          rw [he] at hlen
          simp at hlen
        obtain ⟨a, R3, hxb⟩ := List.exists_cons_of_ne_nil hne
        have ha := hkop a R3 hxb
        rw [hxb] at hcon
        simp only [List.cons_append] at hcon
        injection hcon with ha2 _
        exact ha ha2
      simp only [parseArgs, hmiss2] at ⊢
      have harg := arg_legs x (.zeichen ")") rest F' hLx hxg
        (Or.inr rfl) (by simp only [groesseListe] at hF ⊢; omega)
      simp only [harg, List.cons_append] at ⊢
      rfl
    | cons y ys =>
      have hx : gutAM x = true := gutListeAM_Kopf x (y :: ys) hs
      have hxg : gut x = true := gut_of_gutAM x hx
      have hLx : Legs x := legsAM x hx
      have hF1 : 1 ≤ F := by omega
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      rw [args_cons] at ⊢
      have hmiss2 : ∀ (R2 : List Token),
          druckToks x ++ [.zeichen ","] ++ druckToksListe (y :: ys) ++
            [.zeichen ")"] ++ rest ≠
            .zeichen ")" :: R2 := by
        intro R2 hcon
        have hkop : ∀ (a : Token) (R : List Token),
            druckToks x = a :: R → a ≠ .zeichen ")" :=
          toksKopf (groesse x) x (Nat.le_refl _) hxg
        have hne : druckToks x ≠ [] := by
          intro he
          have hlen := toksLang (groesse x) x (Nat.le_refl _)
          rw [he] at hlen
          simp at hlen
        obtain ⟨a, R3, hxb⟩ := List.exists_cons_of_ne_nil hne
        have ha := hkop a R3 hxb
        rw [hxb] at hcon
        simp only [List.cons_append] at hcon
        injection hcon with ha2 _
        exact ha ha2
      simp only [parseArgs, hmiss2] at ⊢
      have harg := arg_legs x (.zeichen ",")
        (druckToksListe (y :: ys) ++ [.zeichen ")"] ++ rest) F'
        hLx hxg (Or.inl rfl) (by simp only [groesseListe] at hF ⊢; omega)
      have hzs : gutListeAM (y :: ys) =
          true := gutListeAM_Schwanz x (y :: ys) hs
      have hxp := groesse_pos x
      have htail := ihzs rest F' hzs
        (by simp only [groesseListe] at hF ⊢; omega)
      simp only [List.append_assoc, List.cons_append, List.nil_append] at ⊢ harg htail
      simp only [harg, htail, List.cons_append, List.nil_append] at ⊢

-- Calls through `parsePrimary`: mirror of lane 161's
-- `prim_ruf` (head word, `parseKopf` ruf arm, arguments via
-- `args_legs`).
theorem prim_ruf_legs : ∀ (f : String) (xs : List SExpr)
    (rest : List Token) (F : Nat),
    (!istKeinPlatz f) = true → gutListeAM xs = true →
    ruhigSuff rest = true →
    12 * (groesse (.ruf f xs) + 1) + groesse (.ruf f xs) + 1 ≤ F →
    parsePrimary F (druckToks (.ruf f xs) ++ rest) =
      .ok (.ruf f xs, rest) := by
  intro f xs rest F hf hxs hrs hF
  have hkaf : istKeinPlatz f = false := nichtWahr_falsch _ hf
  have hF1 : 1 ≤ F := by omega
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [druckToks, List.cons_append, parsePrimary] at ⊢
  simp only [nameText, hkaf] at ⊢
  have hne : ¬(false = true) := by decide
  simp only [if_neg hne] at ⊢
  have hF2 : 1 ≤ F' := by omega
  obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
  simp only [kopf_ruf_head] at ⊢
  have hgl : 12 * (groesseListe xs + 1) + groesseListe xs + 10 ≤ F'' := by
    have hs : groesse (.ruf f xs) = groesseListe xs + 1 := rfl
    omega
  have hA := args_legs xs rest F'' hxs hgl
  simp only [List.append_assoc] at hA ⊢
  simp only [List.nil_append, hA] at ⊢

-- Call legs from head lawfulness and argument legs: the
-- `parsePrimary` leg above, the `parseUnary` fall-through on
-- the `ident` head (no prefix arm fires), then `tower_up`.
-- (`ruf` is an atom, so no parenthesised case.)
theorem rufLegs : ∀ (f : String) (xs : List SExpr),
    (!istKeinPlatz f) = true → gutListeAM xs = true →
    Legs (.ruf f xs) := by
  intro f xs hf hxs
  have hsize : groesse (.ruf f xs) = groesseListe xs + 1 := rfl
  have hP : ∀ (rest' : List Token) (G : Nat),
      ruhigSuff rest' = true → ruhigGleit rest' = true →
      12 * (groesse (.ruf f xs) + 1) + groesse (.ruf f xs) + 1 ≤ G →
      parsePrimary G (druckToks (.ruf f xs) ++ rest') =
        .ok (.ruf f xs, rest') := by
    intro rest' G hrs hrg hG
    exact prim_ruf_legs f xs rest' G hf hxs hrs hG
  have hU : ∀ (rest' : List Token) (G : Nat),
      ruhigSuff rest' = true → ruhigGleit rest' = true →
      12 * (groesse (.ruf f xs) + 1) + groesse (.ruf f xs) + 2 ≤ G →
      parseUnary G (druckToks (.ruf f xs) ++ rest') =
        .ok (.ruf f xs, rest') := by
    intro rest' G hrs hrg hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hP' := hP rest' G' hrs hrg (by omega)
    have hd : druckToks (.ruf f xs) =
        [.ident f] ++ (([.zeichen "("] ++ druckToksListe xs) ++
          [.zeichen ")"]) := by
      simp [druckToks]
    simp only [hd, List.append_assoc] at hP' ⊢
    -- The `ident` head fires no prefix arm: fall through to
    -- `parsePrimary`.
    have hU' : parseUnary (G' + 1) ([.ident f] ++
        (([.zeichen "("] ++ druckToksListe xs) ++
          ([.zeichen ")"] ++ rest'))) =
        .ok (.ruf f xs, rest') := by
      simp only [List.cons_append, List.nil_append] at hP' ⊢
      simp only [parseUnary, hP'] at ⊢
    exact hU'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro rest' G hpf hrs hrg hG
    exact hP rest' G hrs hrg hG
  · intro rest' G hrs hrg hG
    exact hU rest' G hrs hrg hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up (.ruf f xs) rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).1 G hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up (.ruf f xs) rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).2.1 G hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up (.ruf f xs) rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).2.2.1 G hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up (.ruf f xs) rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).2.2.2.1 G hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up (.ruf f xs) rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).2.2.2.2.1 G hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up (.ruf f xs) rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).2.2.2.2.2 G hG

-- The new call layer: calls over level-3 argument lists.
def rufNeu : SExpr → Bool
  | .ruf f xs => !istKeinPlatz f && gutListeAM xs
  | _ => false

-- Level-4 predicate: level 3 plus one call layer.
def gutRuf (e : SExpr) : Bool := gutAM e || rufNeu e

-- Every level-4 tree has legs: level-3 trees by `legsAM`, new
-- calls by `rufLegs` over level-3 argument legs.
theorem legsRuf : ∀ (e : SExpr), gutRuf e = true → Legs e := by
  intro e hg
  simp only [gutRuf, Bool.or_eq_true] at hg
  obtain hold | hnew := hg
  · exact legsAM e hold
  · cases e with
    | lit m => simp [rufNeu] at hnew
    | gleit s => simp [rufNeu] at hnew
    | wahr => simp [rufNeu] at hnew
    | falsch => simp [rufNeu] at hnew
    | «variable» s => simp [rufNeu] at hnew
    | un o x => simp [rufNeu] at hnew
    | bin o l r => simp [rufNeu] at hnew
    | feld x f => simp [rufNeu] at hnew
    | index x i => simp [rufNeu] at hnew
    | pfeil x f => simp [rufNeu] at hnew
    | ruf f xs =>
      simp only [rufNeu, Bool.and_eq_true] at hnew
      obtain ⟨hf, hxs⟩ := hnew
      exact rufLegs f xs hf hxs
    | fnwert f => simp [rufNeu] at hnew
    | eingebaut f xs => simp [rufNeu] at hnew
    | alt x => simp [rufNeu] at hnew
    | ergebnis => simp [rufNeu] at hnew
    | grund g f => simp [rufNeu] at hnew

-- Level-4 goal: every `gutRuf` tree parses back from its
-- printed tokens with `brennstoff` fuel.
theorem parse_druck_ruf : ∀ (e : SExpr), gutRuf e = true →
    parseOr (brennstoff e) (druckToks e ++ [.ende]) =
      .ok (e, [.ende]) := by
  intro e hg
  have hL := legsRuf e hg
  have hr : ruhig [.ende] = true := rfl
  have hrs : ruhigSuff [.ende] = true := rfl
  have hrg : ruhigGleit [.ende] = true := rfl
  have hF : 12 * (groesse e + 1) + groesse e + 8 ≤ brennstoff e := by
    simp [brennstoff]
  exact hL.2.2.2.2.2.2.2 [.ende] (brennstoff e) hr hrs hrg hF

-- Level-4 witnesses, corpus-flavoured (`107-summe-zwei-rufe`
-- calls one function from another; `01-tabelle` wraps values
-- in `Some`): a one-argument call and a two-argument call, each
-- as a `parse_druck_ruf` instance and a kernel-computed `match`
-- check.
theorem zeuge_ruf_eins :
    parseOr (brennstoff (.ruf "f" [.variable "x"]))
    (druckToks (.ruf "f" [.variable "x"]) ++ [.ende]) =
      .ok (.ruf "f" [.variable "x"], [.ende]) :=
  parse_druck_ruf _ (by decide)
theorem zeuge_ruf_eins_rech : (match parseOr
    (brennstoff (.ruf "f" [.variable "x"]))
    (druckToks (.ruf "f" [.variable "x"]) ++ [.ende]) with
    | .ok (.ruf "f" [.variable "x"], [.ende]) => true
    | _ => false) = true := by
  decide
theorem zeuge_ruf_zwei :
    parseOr (brennstoff (.ruf "g" [.variable "x", .lit 1]))
    (druckToks (.ruf "g" [.variable "x", .lit 1]) ++ [.ende]) =
      .ok (.ruf "g" [.variable "x", .lit 1], [.ende]) :=
  parse_druck_ruf _ (by decide)
theorem zeuge_ruf_zwei_rech : (match parseOr
    (brennstoff (.ruf "g" [.variable "x", .lit 1]))
    (druckToks (.ruf "g" [.variable "x", .lit 1]) ++ [.ende]) with
    | .ok (.ruf "g" [.variable "x", .lit 1], [.ende]) => true
    | _ => false) = true := by
  decide

end Gabbro.Grammatik.Parser
