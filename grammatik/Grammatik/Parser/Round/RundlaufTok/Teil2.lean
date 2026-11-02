module

public import Grammatik.Parser.Round.RundlaufTok.Teil2a
public import Grammatik.Parser.Round.RundlaufVoll
public import Grammatik.Parser.Round.RundlaufTok.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Parser

theorem mulB_stepM : ∀ (m : Nat) (op : String) (l r : SExpr) (W : List Token),
    (∀ (G : Nat), m + 2 ≤ G →
      parseUnary G (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (l, [.zeichen op] ++
          (druckToks r ++ ([.zeichen ")"] ++ W)))) →
    (∀ (G : Nat), m + 2 ≤ G →
      parseUnary G (druckToks r ++ ([.zeichen ")"] ++ W)) =
        .ok (r, [.zeichen ")"] ++ W)) →
    opMul ([.zeichen op] ++ (druckToks r ++ ([.zeichen ")"] ++ W))) =
      some (op, druckToks r ++ ([.zeichen ")"] ++ W)) →
    ruhigSuff ([.zeichen op] ++ (druckToks r ++ ([.zeichen ")"] ++ W))) = true →
    ruhigGleit ([.zeichen op] ++ (druckToks r ++ ([.zeichen ")"] ++ W))) = true →
    ∀ (G : Nat),
      m + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen op] ++ druckToks r ++
        [.zeichen ")"] ++ W) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
  intro m op l r W hUl hUr hop hrsS1 hrgS1 G hG
  have hpos_l := groesse_pos l
  have hpos_r := groesse_pos r
  simp only [List.append_assoc] at ⊢
  -- The `parseAdd` core with the operator consumed inside
  -- `parseMul` (mirror of `kernB_step_star`, spelling
  -- generalised).
  have hAdd : ∀ (G4 : Nat),
      m + 6 ≤ G4 →
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
      m + 7 ≤ G3 →
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
      m + 8 ≤ G2 →
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
      m + 9 ≤ G1 →
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
      m + 10 ≤ G0 →
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


/-- Legs from a primary leg and a unary leg (the upper six by `tower_upM`). -/
theorem legsB_aus (m : Nat) (e : SExpr)
    (hP : ∀ (rest : List Token) (G : Nat), primFrei e = true → ruhigSuff rest = true →
      ruhigGleit rest = true → m + 1 ≤ G → parsePrimary G (druckToks e ++ rest) = .ok (e, rest))
    (hU : ∀ (rest : List Token) (G : Nat), ruhigSuff rest = true → ruhigGleit rest = true →
      m + 2 ≤ G → parseUnary G (druckToks e ++ rest) = .ok (e, rest)) : LegsB m e := by
  refine ⟨hP, hU, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro rest G hr hrs hrg hG
    exact (tower_upM m e rest hr (fun G hG => hU rest G hrs hrg hG)).1 G hG
  · intro rest G hr hrs hrg hG
    exact (tower_upM m e rest hr (fun G hG => hU rest G hrs hrg hG)).2.1 G hG
  · intro rest G hr hrs hrg hG
    exact (tower_upM m e rest hr (fun G hG => hU rest G hrs hrg hG)).2.2.1 G hG
  · intro rest G hr hrs hrg hG
    exact (tower_upM m e rest hr (fun G hG => hU rest G hrs hrg hG)).2.2.2.1 G hG
  · intro rest G hr hrs hrg hG
    exact (tower_upM m e rest hr (fun G hG => hU rest G hrs hrg hG)).2.2.2.2.1 G hG
  · intro rest G hr hrs hrg hG
    exact (tower_upM m e rest hr (fun G hG => hU rest G hrs hrg hG)).2.2.2.2.2 G hG

theorem unary_name_fall (G : Nat) (t : Token) (M R : List Token) (v : SExpr)
    (ht : (∃ g, t = .ident g) ∨ (∃ w, t = .wort w))
    (h : parsePrimary G (t :: M) = .ok (v, R)) : parseUnary (G + 1) (t :: M) = .ok (v, R) := by
  rcases ht with ⟨g, rfl⟩ | ⟨w, rfl⟩ <;> simp only [parseUnary, h]

/-- Legs of a tree printed with a name head (`ident` or `wort`: no prefix arm fires): its primary
    leg suffices. -/
theorem legsB_kopf (m : Nat) (t : Token) {S : List Token} (e : SExpr)
    (ht : (∃ g, t = .ident g) ∨ (∃ w, t = .wort w))
    (hd : druckToks e = [t] ++ S)
    (hP : ∀ (rest : List Token) (G : Nat), ruhigSuff rest = true → ruhigGleit rest = true →
      m + 1 ≤ G → parsePrimary G (druckToks e ++ rest) = .ok (e, rest)) : LegsB m e := by
  apply legsB_aus m e (fun rest G _ hrs hrg hG => hP rest G hrs hrg hG)
  intro rest G hrs hrg hG
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
  have hP' := hP rest G' hrs hrg (by omega)
  rw [hd] at hP' ⊢
  simp only [List.append_assoc, List.singleton_append] at hP' ⊢
  exact unary_name_fall G' t _ _ _ ht hP'

/-- The binary tower from an inner trace at bound `m`: the primary leg runs the `(` arm, the unary
    leg falls through on `(`. -/
theorem bin_turmM (m : Nat) (op : String) (l r : SExpr)
    (hB : ∀ (T : List Token) (G : Nat), m + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen op] ++ druckToks r ++ [.zeichen ")"] ++ T) =
        .ok (.bin op l r, [.zeichen ")"] ++ T)) :
    LegsB (m + 10) (.bin op l r) := by
  have hd : druckToks (.bin op l r) = [.zeichen "("] ++ druckToks l ++
      [.zeichen op] ++ druckToks r ++ [.zeichen ")"] := by
    simp only [druckToks, List.cons_append, List.nil_append, List.append_assoc]
  have hP : ∀ (rest' : List Token) (G : Nat), m + 10 + 1 ≤ G →
      parsePrimary G (druckToks (.bin op l r) ++ rest') = .ok (.bin op l r, rest') := by
    intro rest' G hG
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hB' := hB rest' G' (by omega)
    have hPar := paren_arm _ _ _ _ hB'
    simp only [hd, List.append_assoc] at ⊢
    simp only [List.append_assoc] at hPar
    exact hPar
  apply legsB_aus _ _ (fun rest G _ _ _ hG => hP rest G hG)
  intro rest' G _ _ hG
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
  have hP' := hP rest' G' (by omega)
  simp only [hd, List.append_assoc] at hP' ⊢
  exact un_paren_fall _ _ _ _ hP'

/-- The `||` inner trace over a bound (mirror of `orB_step`). -/
theorem orB_stepM : ∀ (m : Nat) (l r : SExpr) (W : List Token),
    (∀ (G : Nat), m + 2 ≤ G →
      parseUnary G (druckToks l ++ ([.zeichen "||"] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (l, [.zeichen "||"] ++ (druckToks r ++ ([.zeichen ")"] ++ W)))) →
    (∀ (G : Nat), m + 7 ≤ G →
      parseAnd G (druckToks r ++ ([.zeichen ")"] ++ W)) = .ok (r, [.zeichen ")"] ++ W)) →
    ∀ (G : Nat), m + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen "||"] ++ druckToks r ++
        [.zeichen ")"] ++ W) =
        .ok (.bin "||" l r, [.zeichen ")"] ++ W) := by
  intro m l r W hUl hAr G0 hG0
  simp only [List.append_assoc] at ⊢
  have hup := tower_up_orbarM m l ([.zeichen "||"] ++
    (druckToks r ++ ([.zeichen ")"] ++ W))) hUl
    (opMul_orbar _) (opAdd_orbar _) (opBit_orbar _) (opVgl_orbar _)
    (opUnd_orbar _)
  obtain ⟨G1, rfl⟩ : ∃ G1, G0 = G1 + 1 := ⟨G0 - 1, by omega⟩
  have hN' := hup.2.2.2.2 G1 (by omega)
  obtain ⟨G1x, rfl⟩ : ∃ G1x, G1 = G1x + 1 := ⟨G1 - 1, by omega⟩
  have hop := opOder_or_some (druckToks r ++ ([.zeichen ")"] ++ W))
  have hMr := hAr G1x (by omega)
  obtain ⟨G1y, rfl⟩ : ∃ G1y, G1x = G1y + 1 := ⟨G1x - 1, by omega⟩
  have hstop := opOder_paren W
  simp only [parseOr, parseOrL, hN', hop, hMr, hstop] at ⊢

end Gabbro.Grammatik.Parser
