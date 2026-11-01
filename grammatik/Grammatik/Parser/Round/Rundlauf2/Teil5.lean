module

public import Grammatik.Parser.Round.Rundlauf
public import Grammatik.Parser.Round.Rundlauf2.Teil4

@[expose] public section

namespace Gabbro.Grammatik.Parser

-- The `*` inner trace (`BKernStar` from `RKern`): like
-- `kernB_step`, but the inner operator consumes at the
-- `parseMul` level -- `parseMul` runs `parseUnary` on `l`,
-- `parseMulL` consumes `*` and `r`, stops at `)`, and every
-- level above stops at `)`. Same `+10` fuel (same strip
-- count); only the `parseUnary` leg of `RKern` is used.
theorem kernB_step_star : ∀ (n : Nat), RKern n → BKernStar (n + 1) := by
  intro n rkn l r W F hsum hgl hgr hF
  obtain ⟨-, -, -, -, -, -, hUn, -⟩ := rkn
  have hpos_l := groesse_pos l
  have hpos_r := groesse_pos r
  have hln : groesse l ≤ n := by omega
  have hrn : groesse r ≤ n := by omega
  simp only [List.append_assoc] at ⊢
  -- The `parseAdd` core with `*` consumed inside `parseMul`.
  have hAdd : ∀ (G4 : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 6 ≤ G4 →
      parseAdd G4 (druckToks l ++ ([.zeichen "*"] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin "*" l r, [.zeichen ")"] ++ W) := by
    intro G4 hG4
    have h41 : 1 ≤ G4 := by omega
    obtain ⟨G5, rfl⟩ : ∃ G5, G4 = G5 + 1 := ⟨G4 - 1, by omega⟩
    have h42 : 1 ≤ G5 := by omega
    obtain ⟨G6, rfl⟩ : ∃ G6, G5 = G6 + 1 := ⟨G5 - 1, by omega⟩
    have hUl := hUn l ([.zeichen "*"] ++
      (druckToks r ++ ([.zeichen ")"] ++ W))) G6 hln hgl
      (hrs_star _) (hrg_star _) (by omega)
    have h43 : 1 ≤ G6 := by omega
    obtain ⟨G6x, rfl⟩ : ∃ G6x, G6 = G6x + 1 := ⟨G6 - 1, by omega⟩
    have hop := opMul_star_some (druckToks r ++ ([.zeichen ")"] ++ W))
    have hUr := hUn r ([.zeichen ")"] ++ W) G6x hrn hgr
      (hrs_paren W) (hrg_paren W) (by omega)
    have h44 : 1 ≤ G6x := by omega
    obtain ⟨G6y, rfl⟩ : ∃ G6y, G6x = G6y + 1 := ⟨G6x - 1, by omega⟩
    have hstopM := opMul_paren W
    have hstopA := stopAdd ([.zeichen ")"] ++ W) (hr_paren W)
    simp only [parseAdd, parseMul, parseMulL, hUl, hop, hUr, hstopM] at ⊢
    -- Four strips numeral-fold the loop fuel to `+ 3`, which no
    -- equation fires on: unfold once more by explicit rewrite.
    have h45 : G6y + 3 = (G6y + 2) + 1 := by omega
    rw [h45] at ⊢
    simp only [parseAddL, hstopA] at ⊢
  -- Up the pass-through levels, each stopping at `)`.
  have hBit : ∀ (G3 : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 7 ≤ G3 →
      parseBit G3 (druckToks l ++ ([.zeichen "*"] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin "*" l r, [.zeichen ")"] ++ W) := by
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
      parseCmp G2 (druckToks l ++ ([.zeichen "*"] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin "*" l r, [.zeichen ")"] ++ W) := by
    intro G2 hG2
    have h21 : 1 ≤ G2 := by omega
    obtain ⟨G3, rfl⟩ : ∃ G3, G2 = G3 + 1 := ⟨G2 - 1, by omega⟩
    have hBit' := hBit G3 (by omega)
    have hstop := opVgl_paren W
    simp only [parseCmp, hBit', hstop] at ⊢
  have hAnd : ∀ (G1 : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 9 ≤ G1 →
      parseAnd G1 (druckToks l ++ ([.zeichen "*"] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin "*" l r, [.zeichen ")"] ++ W) := by
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
      parseOr G0 (druckToks l ++ ([.zeichen "*"] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin "*" l r, [.zeichen ")"] ++ W) := by
    intro G0 hG0
    have h01 : 1 ≤ G0 := by omega
    obtain ⟨G1, rfl⟩ : ∃ G1, G0 = G1 + 1 := ⟨G0 - 1, by omega⟩
    have hAnd' := hAnd G1 (by omega)
    have h02 : 1 ≤ G1 := by omega
    obtain ⟨G1x, rfl⟩ : ∃ G1x, G1 = G1x + 1 := ⟨G1 - 1, by omega⟩
    have hstop := opOder_paren W
    simp only [parseOr, parseOrL, hAnd', hstop] at ⊢
  exact hOr F hF

-- The `||` inner trace (`BKernOr` from `RKern`): the left
-- operand runs the `||`-follow up-tower (every loop below
-- `Or` stops on the concrete `||`), then `parseOrL` consumes
-- `||` and `r` and stops at `)`. Same `+10` fuel.
theorem kernB_step_or : ∀ (n : Nat), RKern n → BKernOr (n + 1) := by
  intro n rkn l r W F hsum hgl hgr hF
  obtain ⟨-, hAnd, -, -, -, -, hUn, -⟩ := rkn
  have hpos_l := groesse_pos l
  have hpos_r := groesse_pos r
  have hln : groesse l ≤ n := by omega
  have hrn : groesse r ≤ n := by omega
  simp only [List.append_assoc] at ⊢
  have hUleg : ∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 2 ≤ G →
      parseUnary G (druckToks l ++ ([.zeichen "||"] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (l, [.zeichen "||"] ++
          (druckToks r ++ ([.zeichen ")"] ++ W))) := by
    intro G hG
    exact hUn l ([.zeichen "||"] ++
      (druckToks r ++ ([.zeichen ")"] ++ W))) G hln hgl
      (hrs_orbar _) (hrg_orbar _) hG
  have hup := tower_up_orbar l ([.zeichen "||"] ++
    (druckToks r ++ ([.zeichen ")"] ++ W))) hUleg
    (opMul_orbar _) (opAdd_orbar _) (opBit_orbar _) (opVgl_orbar _)
    (opUnd_orbar _)
  have hOr : ∀ (G0 : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G0 →
      parseOr G0 (druckToks l ++ ([.zeichen "||"] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin "||" l r, [.zeichen ")"] ++ W) := by
    intro G0 hG0
    have h01 : 1 ≤ G0 := by omega
    obtain ⟨G1, rfl⟩ : ∃ G1, G0 = G1 + 1 := ⟨G0 - 1, by omega⟩
    have hN' := hup.2.2.2.2 G1 (by omega)
    have h02 : 1 ≤ G1 := by omega
    obtain ⟨G1x, rfl⟩ : ∃ G1x, G1 = G1x + 1 := ⟨G1 - 1, by omega⟩
    have hop := opOder_or_some (druckToks r ++ ([.zeichen ")"] ++ W))
    have hMr := hAnd r ([.zeichen ")"] ++ W) G1x hrn hgr
      (hr_paren W) (hrs_paren W) (hrg_paren W) (by omega)
    have h03 : 1 ≤ G1x := by omega
    obtain ⟨G1y, rfl⟩ : ∃ G1y, G1x = G1y + 1 := ⟨G1x - 1, by omega⟩
    have hstop := opOder_paren W
    simp only [parseOr, parseOrL, hN', hop, hMr, hstop] at ⊢
  exact hOr F hF

-- The `&&` inner trace (`BKernAnd` from `RKern`): the left
-- operand runs the `&&`-follow up-tower (every loop below
-- `And` stops on the concrete `&&`, the single comparison
-- misses it), then `parseAndL` consumes `&&` and `r`, stops
-- at `)`, and the outer `parseOrL` stops too. Same `+10` fuel.
theorem kernB_step_and : ∀ (n : Nat), RKern n → BKernAnd (n + 1) := by
  intro n rkn l r W F hsum hgl hgr hF
  obtain ⟨-, -, hCmp, -, -, -, hUn, -⟩ := rkn
  have hpos_l := groesse_pos l
  have hpos_r := groesse_pos r
  have hln : groesse l ≤ n := by omega
  have hrn : groesse r ≤ n := by omega
  simp only [List.append_assoc] at ⊢
  have hUleg : ∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 2 ≤ G →
      parseUnary G (druckToks l ++ ([.zeichen "&&"] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (l, [.zeichen "&&"] ++
          (druckToks r ++ ([.zeichen ")"] ++ W))) := by
    intro G hG
    exact hUn l ([.zeichen "&&"] ++
      (druckToks r ++ ([.zeichen ")"] ++ W))) G hln hgl
      (hrs_andbar _) (hrg_andbar _) hG
  have hup := tower_up_andbar l ([.zeichen "&&"] ++
    (druckToks r ++ ([.zeichen ")"] ++ W))) hUleg
    (opMul_andbar _) (opAdd_andbar _) (opBit_andbar _) (opVgl_andbar _)
  have hAnd : ∀ (G1 : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 9 ≤ G1 →
      parseAnd G1 (druckToks l ++ ([.zeichen "&&"] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin "&&" l r, [.zeichen ")"] ++ W) := by
    intro G1 hG1
    have h11 : 1 ≤ G1 := by omega
    obtain ⟨G2, rfl⟩ : ∃ G2, G1 = G2 + 1 := ⟨G1 - 1, by omega⟩
    have hC' := hup.2.2.2 G2 (by omega)
    have h12 : 1 ≤ G2 := by omega
    obtain ⟨G2x, rfl⟩ : ∃ G2x, G2 = G2x + 1 := ⟨G2 - 1, by omega⟩
    have hop := opUnd_and_some (druckToks r ++ ([.zeichen ")"] ++ W))
    have hMr := hCmp r ([.zeichen ")"] ++ W) G2x hrn hgr
      (hr_paren W) (hrs_paren W) (hrg_paren W) (by omega)
    have h13 : 1 ≤ G2x := by omega
    obtain ⟨G2y, rfl⟩ : ∃ G2y, G2x = G2y + 1 := ⟨G2x - 1, by omega⟩
    have hstop := opUnd_paren W
    simp only [parseAnd, parseAndL, hC', hop, hMr, hstop] at ⊢
  have hOr : ∀ (G0 : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G0 →
      parseOr G0 (druckToks l ++ ([.zeichen "&&"] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin "&&" l r, [.zeichen ")"] ++ W) := by
    intro G0 hG0
    have h01 : 1 ≤ G0 := by omega
    obtain ⟨G1, rfl⟩ : ∃ G1, G0 = G1 + 1 := ⟨G0 - 1, by omega⟩
    have hAnd' := hAnd G1 (by omega)
    have h02 : 1 ≤ G1 := by omega
    obtain ⟨G1x, rfl⟩ : ∃ G1x, G1 = G1x + 1 := ⟨G1 - 1, by omega⟩
    have hstop := opOder_paren W
    simp only [parseOr, parseOrL, hAnd', hstop] at ⊢
  exact hOr F hF

-- The `un` legs from the induction hypothesis, generalised
-- over the prefix spelling: atoms take the primary leg (via
-- `primFrei_of_atom`), parenthesised children the `parseOr` leg
-- with `)` follow. Returns the seven generalised legs (no
-- primary: `primFrei` is false for `un`).
theorem turm_un : ∀ (n : Nat), RKern n →
    ∀ (o : String) (x : SExpr) (rest : List Token),
    (strEq o "!" || strEq o "-" || strEq o "~") = true →
    groesse (.un o x) ≤ n + 1 → gutKern x = true →
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
    (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 2 ≤ G →
      parseUnary G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 3 ≤ G →
      parseMul G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 4 ≤ G →
      parseAdd G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 5 ≤ G →
      parseBit G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 6 ≤ G →
      parseCmp G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 7 ≤ G →
      parseAnd G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 8 ≤ G →
      parseOr G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest)) := by
  intro n rkn o x rest hop hs hgx hr hrs hrg
  obtain ⟨rOr, -, -, -, -, -, -, rPr⟩ := rkn
  have hsize : groesse (.un o x) = groesse x + 1 := rfl
  have hxn : groesse x ≤ n := by omega
  cases hat : istAtom x with
  | true =>
    have hpf : primFrei x = true := primFrei_of_atom x hat hgx
    have hPx : ∀ (G : Nat), 12 * (groesse x + 1) + groesse x + 1 ≤ G →
        parsePrimary G (druckToks x ++ rest) = .ok (x, rest) := by
      intro G hG
      exact rPr x rest G hxn hgx hpf hrs hrg hG
    exact kern_un_atom_turm o x rest hop hat hr hPx
  | false =>
    have hOx : ∀ (G : Nat), 12 * (groesse x + 1) + groesse x + 8 ≤ G →
        parseOr G (druckToks x ++ ([.zeichen ")"] ++ rest)) =
          .ok (x, [.zeichen ")"] ++ rest) := by
      intro G hG
      exact rOr x ([.zeichen ")"] ++ rest) G hxn hgx
        (hr_paren rest) (hrs_paren rest) (hrg_paren rest) hG
    exact kern_un_paren_turm o x rest hop hat hr hOx

-- The `bin "+"` legs from the binary-inner invariant: a thin
-- wrapper adapting `BKern n` to the leg shape `kern_bin_turm`
-- takes. Returns the eight generalised legs.
theorem turm_bin : ∀ (n : Nat), BKern n →
    ∀ (l r : SExpr) (rest : List Token),
    groesse (.bin "+" l r) ≤ n + 1 →
    gutKern l = true → gutKern r = true →
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
    (∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 1 ≤ G →
      parsePrimary G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 2 ≤ G →
      parseUnary G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 3 ≤ G →
      parseMul G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 4 ≤ G →
      parseAdd G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 5 ≤ G →
      parseBit G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 6 ≤ G →
      parseCmp G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 7 ≤ G →
      parseAnd G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 8 ≤ G →
      parseOr G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest)) := by
  intro n bkn l r rest hs hl hr2 hrr hrs hrg
  have hsize : groesse (.bin "+" l r) = groesse l + groesse r + 1 := rfl
  have hsum : groesse l + groesse r ≤ n := by omega
  have hB : ∀ (G : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen "+"] ++ druckToks r ++
        [.zeichen ")"] ++ rest) =
        .ok (.bin "+" l r, [.zeichen ")"] ++ rest) := by
    intro G hG
    exact bkn l r rest G hsum hl hr2 hG
  exact kern_bin_turm l r rest hl hr2 hrr hrs hrg hB

-- The `bin "*"` legs from the star invariant: word for word
-- the `+` wrapper with the spelling swapped.
theorem turm_bin_star : ∀ (n : Nat), BKernStar n →
    ∀ (l r : SExpr) (rest : List Token),
    groesse (.bin "*" l r) ≤ n + 1 →
    gutKern l = true → gutKern r = true →
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
    (∀ (G : Nat), 12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 1 ≤ G →
      parsePrimary G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 2 ≤ G →
      parseUnary G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 3 ≤ G →
      parseMul G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 4 ≤ G →
      parseAdd G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 5 ≤ G →
      parseBit G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 6 ≤ G →
      parseCmp G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 7 ≤ G →
      parseAnd G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 8 ≤ G →
      parseOr G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest)) := by
  intro n bStar l r rest hs hl hr2 hrr hrs hrg
  have hsize : groesse (.bin "*" l r) = groesse l + groesse r + 1 := rfl
  have hsum : groesse l + groesse r ≤ n := by omega
  have hB : ∀ (G : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen "*"] ++ druckToks r ++
        [.zeichen ")"] ++ rest) =
        .ok (.bin "*" l r, [.zeichen ")"] ++ rest) := by
    intro G hG
    exact bStar l r rest G hsum hl hr2 hG
  exact kern_bin_star_turm l r rest hl hr2 hrr hrs hrg hB

-- The `bin "||"` legs from the or invariant: word for word
-- the `*` wrapper with the spelling swapped.
theorem turm_bin_or : ∀ (n : Nat), BKernOr n →
    ∀ (l r : SExpr) (rest : List Token),
    groesse (.bin "||" l r) ≤ n + 1 →
    gutKern l = true → gutKern r = true →
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
    (∀ (G : Nat), 12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 1 ≤ G →
      parsePrimary G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 2 ≤ G →
      parseUnary G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 3 ≤ G →
      parseMul G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 4 ≤ G →
      parseAdd G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 5 ≤ G →
      parseBit G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 6 ≤ G →
      parseCmp G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 7 ≤ G →
      parseAnd G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 8 ≤ G →
      parseOr G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest)) := by
  intro n bOr l r rest hs hl hr2 hrr hrs hrg
  have hsize : groesse (.bin "||" l r) = groesse l + groesse r + 1 := rfl
  have hsum : groesse l + groesse r ≤ n := by omega
  have hB : ∀ (G : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen "||"] ++ druckToks r ++
        [.zeichen ")"] ++ rest) =
        .ok (.bin "||" l r, [.zeichen ")"] ++ rest) := by
    intro G hG
    exact bOr l r rest G hsum hl hr2 hG
  exact kern_bin_or_turm l r rest hl hr2 hrr hrs hrg hB

-- The `bin "&&"` legs from the and invariant: word for word
-- the `||` wrapper with the spelling swapped.
theorem turm_bin_and : ∀ (n : Nat), BKernAnd n →
    ∀ (l r : SExpr) (rest : List Token),
    groesse (.bin "&&" l r) ≤ n + 1 →
    gutKern l = true → gutKern r = true →
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
    (∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 1 ≤ G →
      parsePrimary G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 2 ≤ G →
      parseUnary G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 3 ≤ G →
      parseMul G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 4 ≤ G →
      parseAdd G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 5 ≤ G →
      parseBit G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 6 ≤ G →
      parseCmp G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 7 ≤ G →
      parseAnd G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 8 ≤ G →
      parseOr G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest)) := by
  intro n bAnd l r rest hs hl hr2 hrr hrs hrg
  have hsize : groesse (.bin "&&" l r) = groesse l + groesse r + 1 := rfl
  have hsum : groesse l + groesse r ≤ n := by omega
  have hB : ∀ (G : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen "&&"] ++ druckToks r ++
        [.zeichen ")"] ++ rest) =
        .ok (.bin "&&" l r, [.zeichen ")"] ++ rest) := by
    intro G hG
    exact bAnd l r rest G hsum hl hr2 hG
  exact kern_bin_and_turm l r rest hl hr2 hrr hrs hrg hB

end Gabbro.Grammatik.Parser
