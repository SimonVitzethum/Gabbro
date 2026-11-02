module
public import Grammatik.Parser.Round.Rundlauf2.Teil7a

public import Grammatik.Parser.Round.Rundlauf
public import Grammatik.Parser.Round.Rundlauf2.Teil6

@[expose] public section

namespace Gabbro.Grammatik.Parser

theorem kern_bin_prim_and : ∀ (l r : SExpr) (rest : List Token),
    (∀ (G : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen "&&"] ++ druckToks r ++
        [.zeichen ")"] ++ rest) =
        .ok (.bin "&&" l r, [.zeichen ")"] ++ rest)) →
    ∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 1 ≤ G →
      parsePrimary G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest) := by
  intro l r rest hB G hG
  have hsize : groesse (.bin "&&" l r) = groesse l + groesse r + 1 := rfl
  have hd : druckToks (.bin "&&" l r) = [.zeichen "("] ++ druckToks l ++
      [.zeichen "&&"] ++ druckToks r ++ [.zeichen ")"] := by
    simp only [druckToks, List.cons_append, List.nil_append, List.append_assoc]
  have hG1 : 1 ≤ G := by omega
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
  have hB' := hB G' (by omega)
  have hPar := paren_arm _ _ _ _ hB'
  simp only [hd, List.append_assoc] at ⊢
  simp only [List.append_assoc] at hPar
  exact hPar

-- The `bin "+"` primary leg from a binary-inner leg: no
-- follow premises at all (the `(` arm runs the inner parse).
-- Extracted for the `RKern`-primary component, which has no
-- `ruhig` (same proof as `kern_bin_turm`'s leg).
theorem kern_bin_prim : ∀ (l r : SExpr) (rest : List Token),
    (∀ (G : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen "+"] ++ druckToks r ++
        [.zeichen ")"] ++ rest) =
        .ok (.bin "+" l r, [.zeichen ")"] ++ rest)) →
    ∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 1 ≤ G →
      parsePrimary G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest) := by
  intro l r rest hB G hG
  have hsize : groesse (.bin "+" l r) = groesse l + groesse r + 1 := rfl
  have hd : druckToks (.bin "+" l r) = [.zeichen "("] ++ druckToks l ++
      [.zeichen "+"] ++ druckToks r ++ [.zeichen ")"] := by
    simp only [druckToks, List.cons_append, List.nil_append, List.append_assoc]
  have hG1 : 1 ≤ G := by omega
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
  have hB' := hB G' (by omega)
  have hPar := paren_arm _ _ _ _ hB'
  simp only [hd, List.append_assoc] at ⊢
  simp only [List.append_assoc] at hPar
  exact hPar

theorem kernAdd_step : ∀ (n : Nat), RKern n → BKern n → BKernStar n → BKernOr n → BKernAnd n →
    (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n + 1 →
      gutKern e = true → ruhig rest = true → ruhigSuff rest = true →
      ruhigGleit rest = true →
      12 * (groesse e + 1) + groesse e + 4 ≤ F →
      parseAdd F (druckToks e ++ rest) = .ok (e, rest)) := by
  intro n rkn bkn bStar bOr bAnd e rest F hs hg hr hrs hrg hF
  cases e with
  | lit m => exact (turm_lit m rest hr hrs hrg).2.2.2.1 F (by omega)
  | float s => exact (turm_gleit s rest hr hrs hrg).2.2.2.1 F (by omega)
  | tru => exact (turm_wahr rest hr hrs hrg).2.2.2.1 F (by omega)
  | fls => exact (turm_falsch rest hr hrs hrg).2.2.2.1 F (by omega)
  | «variable» a =>
    have hka : (!istKopfWort a) = true := by
      simp only [gutKern] at hg
      exact hg
    exact (turm_var a rest hka hr hrs hrg).2.2.2.1 F (by omega)
  | un o x =>
    rw [gutKern_un] at hg
    simp only [Bool.and_eq_true] at hg
    obtain ⟨hop, hgx⟩ := hg
    exact (turm_un n rkn o x rest hop hs hgx hr hrs hrg).2.2.1 F (by omega)
  | bin o l r =>
    rw [gutKern_bin] at hg
    simp only [Bool.and_eq_true, and_assoc] at hg
    obtain ⟨hop, hl, hr2⟩ := hg
    obtain rfl | rfl | rfl | rfl := bin_is_pm o hop
    · exact (turm_bin n bkn l r rest hs hl hr2 hr hrs hrg).2.2.2.1 F (by omega)
    · exact (turm_bin_star n bStar l r rest hs hl hr2 hr hrs hrg).2.2.2.1 F (by omega)
    · exact (turm_bin_or n bOr l r rest hs hl hr2 hr hrs hrg).2.2.2.1 F (by omega)
    · exact (turm_bin_and n bAnd l r rest hs hl hr2 hr hrs hrg).2.2.2.1 F (by omega)
  | field x f =>
    rw [gutKern_feld] at hg
    have hpp : gutKernPlatz (.field x f) = true := by
      rw [gutKernPlatz_feld]; exact hg
    exact (turm_platz n rkn (.field x f) rest hs hpp hr hrs hrg).2.2.2.1 F (by omega)
  | index x i =>
    rw [gutKern_index] at hg
    simp only [Bool.and_eq_true] at hg
    obtain ⟨hpx, hi⟩ := hg
    have hpp : gutKernPlatz (.index x i) = true := by
      rw [gutKernPlatz_index]; simp only [Bool.and_eq_true]; exact ⟨hpx, hi⟩
    exact (turm_platz n rkn (.index x i) rest hs hpp hr hrs hrg).2.2.2.1 F (by omega)
  | arrow x f =>
    rw [gutKern_pfeil] at hg
    have hpp : gutKernPlatz (.arrow x f) = true := by
      rw [gutKernPlatz_pfeil]; exact hg
    exact (turm_platz n rkn (.arrow x f) rest hs hpp hr hrs hrg).2.2.2.1 F (by omega)
  | call f xs => simp only [gutKern, Bool.false_eq_true] at hg
  | fnref f => simp only [gutKern, Bool.false_eq_true] at hg
  | built f xs => simp only [gutKern, Bool.false_eq_true] at hg
  | old x => simp only [gutKern, Bool.false_eq_true] at hg
  | res => simp only [gutKern, Bool.false_eq_true] at hg
  | why g f => simp only [gutKern, Bool.false_eq_true] at hg
  | ext xk xn xs => simp only [gutKern, Bool.false_eq_true] at hg

theorem kernMul_step : ∀ (n : Nat), RKern n → BKern n → BKernStar n → BKernOr n → BKernAnd n →
    (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n + 1 →
      gutKern e = true → ruhig rest = true → ruhigSuff rest = true →
      ruhigGleit rest = true →
      12 * (groesse e + 1) + groesse e + 3 ≤ F →
      parseMul F (druckToks e ++ rest) = .ok (e, rest)) := by
  intro n rkn bkn bStar bOr bAnd e rest F hs hg hr hrs hrg hF
  cases e with
  | lit m => exact (turm_lit m rest hr hrs hrg).2.2.1 F (by omega)
  | float s => exact (turm_gleit s rest hr hrs hrg).2.2.1 F (by omega)
  | tru => exact (turm_wahr rest hr hrs hrg).2.2.1 F (by omega)
  | fls => exact (turm_falsch rest hr hrs hrg).2.2.1 F (by omega)
  | «variable» a =>
    have hka : (!istKopfWort a) = true := by
      simp only [gutKern] at hg
      exact hg
    exact (turm_var a rest hka hr hrs hrg).2.2.1 F (by omega)
  | un o x =>
    rw [gutKern_un] at hg
    simp only [Bool.and_eq_true] at hg
    obtain ⟨hop, hgx⟩ := hg
    exact (turm_un n rkn o x rest hop hs hgx hr hrs hrg).2.1 F (by omega)
  | bin o l r =>
    rw [gutKern_bin] at hg
    simp only [Bool.and_eq_true, and_assoc] at hg
    obtain ⟨hop, hl, hr2⟩ := hg
    obtain rfl | rfl | rfl | rfl := bin_is_pm o hop
    · exact (turm_bin n bkn l r rest hs hl hr2 hr hrs hrg).2.2.1 F (by omega)
    · exact (turm_bin_star n bStar l r rest hs hl hr2 hr hrs hrg).2.2.1 F (by omega)
    · exact (turm_bin_or n bOr l r rest hs hl hr2 hr hrs hrg).2.2.1 F (by omega)
    · exact (turm_bin_and n bAnd l r rest hs hl hr2 hr hrs hrg).2.2.1 F (by omega)
  | field x f =>
    rw [gutKern_feld] at hg
    have hpp : gutKernPlatz (.field x f) = true := by
      rw [gutKernPlatz_feld]; exact hg
    exact (turm_platz n rkn (.field x f) rest hs hpp hr hrs hrg).2.2.1 F (by omega)
  | index x i =>
    rw [gutKern_index] at hg
    simp only [Bool.and_eq_true] at hg
    obtain ⟨hpx, hi⟩ := hg
    have hpp : gutKernPlatz (.index x i) = true := by
      rw [gutKernPlatz_index]; simp only [Bool.and_eq_true]; exact ⟨hpx, hi⟩
    exact (turm_platz n rkn (.index x i) rest hs hpp hr hrs hrg).2.2.1 F (by omega)
  | arrow x f =>
    rw [gutKern_pfeil] at hg
    have hpp : gutKernPlatz (.arrow x f) = true := by
      rw [gutKernPlatz_pfeil]; exact hg
    exact (turm_platz n rkn (.arrow x f) rest hs hpp hr hrs hrg).2.2.1 F (by omega)
  | call f xs => simp only [gutKern, Bool.false_eq_true] at hg
  | fnref f => simp only [gutKern, Bool.false_eq_true] at hg
  | built f xs => simp only [gutKern, Bool.false_eq_true] at hg
  | old x => simp only [gutKern, Bool.false_eq_true] at hg
  | res => simp only [gutKern, Bool.false_eq_true] at hg
  | why g f => simp only [gutKern, Bool.false_eq_true] at hg
  | ext xk xn xs => simp only [gutKern, Bool.false_eq_true] at hg

end Gabbro.Grammatik.Parser
