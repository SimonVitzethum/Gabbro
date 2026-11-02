/-
  File:      Grammatik/Parser/Round/RundlaufVoll.lean
  Subject:   Layer L2a of the syntax round trip, the pieces for the WHOLE printable class `gut`: the
             invariant `R n` repackaged from legs at size `n` (`R_of_legs`), the generic operand-leg
             steps for `||`/`&&` (`orLegs`, `andLegs`), the prefix towers (`unLegs`), the
             leaf legs and the case split of `gut` over `built` (`gut_built_faelle`).

  The joint induction over `gut` itself runs in `RundlaufTok` at a TOKEN bound (`legs_tok`,
  `parse_druck_tok`, `parseTop_druck_gut`); the size bound of this file (thirteen fuel per node) does
  not reach the fixed-fuel readers, so its own induction was dropped when calls through a place
  (`o.is_some()`) joined `gut`.

  `gut` is the printability predicate of lane 161 (Rundlauf.lean): it excludes exactly the shapes with
  no token spelling that parses back (booked there): reserved heads (`istKeinPlatz`), unknown
  operator spellings, suffixes on non-places, `sizeof`/`lenof`/`old` over non-places, `sizeof`/
  `lenof` over a bare type word, `G::F` with an integer, sugared-width or `Self` head, and every
  `ext` form except a call through a suffixed place (predicates and strings -- `druckExtToks` prints
  them, outside the theorem).
-/
module
public import Grammatik.Parser.Round.Rundlauf4.Teil2
public import Grammatik.Parser.Round.RundlaufLex.Teil2
@[expose] public section


namespace Gabbro.Grammatik.Parser

/-- The name token is an identifier or a word. -/
theorem nameTok_form (a : String) : (∃ g, nameTok a = .ident g) ∨ (∃ w, nameTok a = .wort w) := by
  unfold nameTok; split
  · exact Or.inr ⟨a, rfl⟩
  · exact Or.inl ⟨a, rfl⟩

/-! ### `||` and `&&` over abstract operand legs -/

/-- The `||` inner trace over abstract legs: the left operand climbs the `||`-follow up-tower to
    `parseAnd`, `parseOrL` consumes `||` and runs the right operand at `parseAnd`, the loop stops at
    `)`. The mirror of `kernB_step_or` with the `RKern` legs replaced by hypotheses. -/
theorem orB_step : ∀ (l r : SExpr) (W : List Token),
    (∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 2 ≤ G →
      parseUnary G (druckToks l ++ ([.zeichen "||"] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (l, [.zeichen "||"] ++ (druckToks r ++ ([.zeichen ")"] ++ W)))) →
    (∀ (G : Nat), 12 * (groesse r + 1) + groesse r + 7 ≤ G →
      parseAnd G (druckToks r ++ ([.zeichen ")"] ++ W)) = .ok (r, [.zeichen ")"] ++ W)) →
    ∀ (G : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen "||"] ++ druckToks r ++
        [.zeichen ")"] ++ W) =
        .ok (.bin "||" l r, [.zeichen ")"] ++ W) := by
  intro l r W hUl hAr G0 hG0
  have hpos_l := groesse_pos l
  have hpos_r := groesse_pos r
  simp only [List.append_assoc] at ⊢
  have hup := tower_up_orbar l ([.zeichen "||"] ++
    (druckToks r ++ ([.zeichen ")"] ++ W))) hUl
    (opMul_orbar _) (opAdd_orbar _) (opBit_orbar _) (opVgl_orbar _)
    (opUnd_orbar _)
  have h01 : 1 ≤ G0 := by omega
  obtain ⟨G1, rfl⟩ : ∃ G1, G0 = G1 + 1 := ⟨G0 - 1, by omega⟩
  have hN' := hup.2.2.2.2 G1 (by omega)
  have h02 : 1 ≤ G1 := by omega
  obtain ⟨G1x, rfl⟩ : ∃ G1x, G1 = G1x + 1 := ⟨G1 - 1, by omega⟩
  have hop := opOder_or_some (druckToks r ++ ([.zeichen ")"] ++ W))
  have hMr := hAr G1x (by omega)
  have h03 : 1 ≤ G1x := by omega
  obtain ⟨G1y, rfl⟩ : ∃ G1y, G1x = G1y + 1 := ⟨G1x - 1, by omega⟩
  have hstop := opOder_paren W
  simp only [parseOr, parseOrL, hN', hop, hMr, hstop] at ⊢

/-- The `&&` inner trace over abstract legs (mirror of `kernB_step_and`). -/
theorem andB_step : ∀ (l r : SExpr) (W : List Token),
    (∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 2 ≤ G →
      parseUnary G (druckToks l ++ ([.zeichen "&&"] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (l, [.zeichen "&&"] ++ (druckToks r ++ ([.zeichen ")"] ++ W)))) →
    (∀ (G : Nat), 12 * (groesse r + 1) + groesse r + 6 ≤ G →
      parseCmp G (druckToks r ++ ([.zeichen ")"] ++ W)) = .ok (r, [.zeichen ")"] ++ W)) →
    ∀ (G : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen "&&"] ++ druckToks r ++
        [.zeichen ")"] ++ W) =
        .ok (.bin "&&" l r, [.zeichen ")"] ++ W) := by
  intro l r W hUl hCr F hF
  have hpos_l := groesse_pos l
  have hpos_r := groesse_pos r
  simp only [List.append_assoc] at ⊢
  have hup := tower_up_andbar l ([.zeichen "&&"] ++
    (druckToks r ++ ([.zeichen ")"] ++ W))) hUl
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
    have hMr := hCr G2x (by omega)
    have h13 : 1 ≤ G2x := by omega
    obtain ⟨G2y, rfl⟩ : ∃ G2y, G2x = G2y + 1 := ⟨G2x - 1, by omega⟩
    have hstop := opUnd_paren W
    simp only [parseAnd, parseAndL, hC', hop, hMr, hstop] at ⊢
  have h01 : 1 ≤ F := by omega
  obtain ⟨G1, rfl⟩ : ∃ G1, F = G1 + 1 := ⟨F - 1, by omega⟩
  have hAnd' := hAnd G1 (by omega)
  have h02 : 1 ≤ G1 := by omega
  obtain ⟨G1x, rfl⟩ : ∃ G1x, G1 = G1x + 1 := ⟨G1 - 1, by omega⟩
  have hstop := opOder_paren W
  simp only [parseOr, parseOrL, hAnd', hstop] at ⊢

theorem orLegs : ∀ (l r : SExpr), Legs l → Legs r → Legs (.bin "||" l r) := by
  intro l r Hl Hr
  apply bin_turm3 "||" l r
  intro T G hG
  apply orB_step l r T _ _ G hG
  · intro G' hG'
    exact Hl.2.1 _ G' (hrs_orbar _) (hrg_orbar _) hG'
  · intro G' hG'
    exact Hr.2.2.2.2.2.2.1 _ G' (hr_paren T) (hrs_paren T) (hrg_paren T) hG'

theorem andLegs : ∀ (l r : SExpr), Legs l → Legs r → Legs (.bin "&&" l r) := by
  intro l r Hl Hr
  apply bin_turm3 "&&" l r
  intro T G hG
  apply andB_step l r T _ _ G hG
  · intro G' hG'
    exact Hl.2.1 _ G' (hrs_andbar _) (hrg_andbar _) hG'
  · intro G' hG'
    exact Hr.2.2.2.2.2.1 _ G' (hr_paren T) (hrs_paren T) (hrg_paren T) hG'


end Gabbro.Grammatik.Parser
