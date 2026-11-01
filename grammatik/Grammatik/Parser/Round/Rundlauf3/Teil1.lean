module

public import Grammatik.Parser.Round.Rundlauf2
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic

@[expose] public section



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
    simp only [druckToks, List.cons_append, List.nil_append, List.append_assoc]
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
    | lit m => simp only [cmpNeu, Bool.false_eq_true] at hnew
    | float s => simp only [cmpNeu, Bool.false_eq_true] at hnew
    | tru => simp only [cmpNeu, Bool.false_eq_true] at hnew
    | fls => simp only [cmpNeu, Bool.false_eq_true] at hnew
    | «variable» s => simp only [cmpNeu, Bool.false_eq_true] at hnew
    | un o x => simp only [cmpNeu, Bool.false_eq_true] at hnew
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
    | field x f => simp only [cmpNeu, Bool.false_eq_true] at hnew
    | index x i => simp only [cmpNeu, Bool.false_eq_true] at hnew
    | arrow x f => simp only [cmpNeu, Bool.false_eq_true] at hnew
    | call f xs => simp only [cmpNeu, Bool.false_eq_true] at hnew
    | fnref f => simp only [cmpNeu, Bool.false_eq_true] at hnew
    | built f xs => simp only [cmpNeu, Bool.false_eq_true] at hnew
    | old x => simp only [cmpNeu, Bool.false_eq_true] at hnew
    | res => simp only [cmpNeu, Bool.false_eq_true] at hnew
    | why g f => simp only [cmpNeu, Bool.false_eq_true] at hnew
    | ext xk xn xs => simp only [cmpNeu, Bool.false_eq_true] at hnew

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
    simp only [brennstoff, Std.le_refl]
  exact hL.2.2.2.2.2.2.2 [.ende] (brennstoff e) hr hrs hrg hF

-- Level-1 witnesses, corpus-flavoured (`01-tabelle` compares a
-- field against a literal with `==`; `04-schleifen` bounds a
-- counter with `<`): each as a `parse_druck_cmp` instance and a
-- kernel-computed `match` check.
theorem zeuge_cmp_eq :
    parseOr (brennstoff (.bin "==" (.field (.variable "c") "x") (.lit 0)))
    (druckToks (.bin "==" (.field (.variable "c") "x") (.lit 0)) ++ [.ende]) =
      .ok (.bin "==" (.field (.variable "c") "x") (.lit 0), [.ende]) :=
  parse_druck_cmp _ (by decide)
theorem zeuge_cmp_eq_rech : (match parseOr
    (brennstoff (.bin "==" (.field (.variable "c") "x") (.lit 0)))
    (druckToks (.bin "==" (.field (.variable "c") "x") (.lit 0)) ++ [.ende]) with
    | .ok (.bin "==" (.field (.variable "c") "x") (.lit 0), [.ende]) => true
    | _ => false) = true := by
  decide
theorem zeuge_cmp_lt :
    parseOr (brennstoff (.bin "<" (.variable "s") (.lit 64)))
    (druckToks (.bin "<" (.variable "s") (.lit 64)) ++ [.ende]) =
      .ok (.bin "<" (.variable "s") (.lit 64), [.ende]) :=
  parse_druck_cmp _ (by decide)
end Gabbro.Grammatik.Parser
