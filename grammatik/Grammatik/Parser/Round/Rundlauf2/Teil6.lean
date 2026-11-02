module
public import Grammatik.Parser.Round.Rundlauf2.Teil6a

public import Grammatik.Parser.Round.Rundlauf
public import Grammatik.Parser.Round.Rundlauf2.Teil5

@[expose] public section

namespace Gabbro.Grammatik.Parser

-- Kernel places through `parsePrimary`: decompose by
-- `zerlege_kern`, read the head, run the chain by
-- `kern_suff_rund`. The `parseKopf` steps reuse lane 161's
-- spelling-blind lemmas.
theorem kern_prim_platz : ∀ (n : Nat) (rkn : RKern n)
    (p : SExpr) (rest : List Token) (F : Nat),
    groesse p ≤ n + 1 → gutKernPlatz p = true → ruhigSuff rest = true →
    12 * (groesse p + 1) + groesse p + 1 ≤ F →
    parsePrimary F (druckToks p ++ rest) = .ok (p, rest) := by
  intro n rkn p rest F hs hg hr hF
  obtain ⟨a, suff, rfl, hka, hgs, hsz⟩ := zerlege_kern (n + 1) p hs hg
  have hF1 : 1 ≤ F := by omega
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  have hF2 : 1 ≤ F' := by omega
  obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
  rw [druckToks_applySuff] at ⊢
  simp only [druckToks, List.cons_append]
  rw [parsePrimary_nameTok _ _ _ (nichtWahr_falsch _ hka)]
  simp only [parseKopf, nameText_nameTok] at ⊢
  simp only [List.nil_append] at ⊢
  simp only [sammleSeg_suffToks, hr] at ⊢
  have hmiss : ∀ (R : List Token),
      suffToks suff ++ rest ≠ .zeichen "(" :: R := by
    intro R hcon
    exact suffToks_nopar suff rest R hr hcon
  simp only [hmiss] at ⊢
  have hs2 : suffGroesse suff + groesse (.variable a) ≤ n + 1 := by
    simp only [groesse] at ⊢
    omega
  have hF3 : 12 * (suffGroesse suff + groesse (.variable a) + 1) +
      suffGroesse suff ≤ F'' := by
    simp only [groesse, groesse_applySuff] at hs hF ⊢
    omega
  exact kern_suff_rund n rkn suff (.variable a) rest F'' hs2 hgs hr hF3

-- The place tower, uniform over all place shapes: the
-- `parsePrimary` leg by `kern_prim_platz`, the `parseUnary`
-- leg by decomposing (`zerlege_kern` exposes the head
-- variable, so the prefix-operator match falls through to
-- `parsePrimary`), then `tower_up` for the six loop levels.
-- The place weak legs (no `ruhig`: the Unary step lacks
-- it): `parsePrimary` by `kern_prim_platz`, `parseUnary` by
-- decomposing.
theorem turm_platz_PU : ∀ (n : Nat), RKern n →
    ∀ (p : SExpr) (rest : List Token),
    groesse p ≤ n + 1 → gutKernPlatz p = true →
    ruhigSuff rest = true → ruhigGleit rest = true →
    (∀ (G : Nat), 12 * (groesse p + 1) + groesse p + 1 ≤ G →
      parsePrimary G (druckToks p ++ rest) = .ok (p, rest))
    ∧ (∀ (G : Nat), 12 * (groesse p + 1) + groesse p + 2 ≤ G →
      parseUnary G (druckToks p ++ rest) = .ok (p, rest)) := by
  intro n rkn p rest hs hpp hrs hrg
  have hP : ∀ (G : Nat),
      12 * (groesse p + 1) + groesse p + 1 ≤ G →
      parsePrimary G (druckToks p ++ rest) = .ok (p, rest) := by
    intro G hG
    exact kern_prim_platz n rkn p rest G hs hpp hrs hG
  have hU : ∀ (G : Nat),
      12 * (groesse p + 1) + groesse p + 2 ≤ G →
      parseUnary G (druckToks p ++ rest) = .ok (p, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    obtain ⟨a, suff, rfl, hka, hgs, hsz⟩ :=
      zerlege_kern (n + 1) p hs hpp
    have hP' := hP G' (by omega)
    rw [druckToks_applySuff] at hP' ⊢
    simp only [druckToks, List.cons_append, List.nil_append] at hP' ⊢
    first | rw [parseUnary_nameTok] | simp only [parseUnary] at ⊢
    exact hP'
  exact ⟨hP, hU⟩

theorem turm_platz : ∀ (n : Nat), RKern n →
    ∀ (p : SExpr) (rest : List Token),
    groesse p ≤ n + 1 → gutKernPlatz p = true →
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
    (∀ (G : Nat), 12 * (groesse p + 1) + groesse p + 1 ≤ G →
      parsePrimary G (druckToks p ++ rest) = .ok (p, rest))
    ∧ (∀ (G : Nat), 12 * (groesse p + 1) + groesse p + 2 ≤ G →
      parseUnary G (druckToks p ++ rest) = .ok (p, rest))
    ∧ (∀ (G : Nat), 12 * (groesse p + 1) + groesse p + 3 ≤ G →
      parseMul G (druckToks p ++ rest) = .ok (p, rest))
    ∧ (∀ (G : Nat), 12 * (groesse p + 1) + groesse p + 4 ≤ G →
      parseAdd G (druckToks p ++ rest) = .ok (p, rest))
    ∧ (∀ (G : Nat), 12 * (groesse p + 1) + groesse p + 5 ≤ G →
      parseBit G (druckToks p ++ rest) = .ok (p, rest))
    ∧ (∀ (G : Nat), 12 * (groesse p + 1) + groesse p + 6 ≤ G →
      parseCmp G (druckToks p ++ rest) = .ok (p, rest))
    ∧ (∀ (G : Nat), 12 * (groesse p + 1) + groesse p + 7 ≤ G →
      parseAnd G (druckToks p ++ rest) = .ok (p, rest))
    ∧ (∀ (G : Nat), 12 * (groesse p + 1) + groesse p + 8 ≤ G →
      parseOr G (druckToks p ++ rest) = .ok (p, rest)) := by
  intro n rkn p rest hs hpp hr hrs hrg
  have hPU := turm_platz_PU n rkn p rest hs hpp hrs hrg
  have hup := tower_up p rest hr hPU.2
  exact ⟨hPU.1, hPU.2, hup.1, hup.2.1, hup.2.2.1,
    hup.2.2.2.1, hup.2.2.2.2.1, hup.2.2.2.2.2⟩

-- The main induction, one level per lemma: each step lifts
-- one `RKern` component from `n` to `n + 1` by cases over the
-- tree (atoms via the standalone towers, `un` via `turm_un`,
-- `bin` via `turm_bin`, everything else contradicts `gutKern`).
-- Projections: atom/bin 8-tuples end `.2.2.2.2.2.2.2` at `Or`.
theorem kernOr_step : ∀ (n : Nat), RKern n → BKern n → BKernStar n → BKernOr n → BKernAnd n →
    (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n + 1 →
      gutKern e = true → ruhig rest = true → ruhigSuff rest = true →
      ruhigGleit rest = true →
      12 * (groesse e + 1) + groesse e + 8 ≤ F →
      parseOr F (druckToks e ++ rest) = .ok (e, rest)) := by
  intro n rkn bkn bStar bOr bAnd e rest F hs hg hr hrs hrg hF
  cases e with
  | lit m => exact (turm_lit m rest hr hrs hrg).2.2.2.2.2.2.2 F (by omega)
  | float s => exact (turm_gleit s rest hr hrs hrg).2.2.2.2.2.2.2 F (by omega)
  | tru => exact (turm_wahr rest hr hrs hrg).2.2.2.2.2.2.2 F (by omega)
  | fls => exact (turm_falsch rest hr hrs hrg).2.2.2.2.2.2.2 F (by omega)
  | «variable» a =>
    have hka : (!istKopfWort a) = true := by
      simp only [gutKern] at hg
      exact hg
    exact (turm_var a rest hka hr hrs hrg).2.2.2.2.2.2.2 F (by omega)
  | un o x =>
    rw [gutKern_un] at hg
    simp only [Bool.and_eq_true] at hg
    obtain ⟨hop, hgx⟩ := hg
    exact (turm_un n rkn o x rest hop hs hgx hr hrs hrg).2.2.2.2.2.2 F (by omega)
  | bin o l r =>
    rw [gutKern_bin] at hg
    simp only [Bool.and_eq_true, and_assoc] at hg
    obtain ⟨hop, hl, hr2⟩ := hg
    obtain rfl | rfl | rfl | rfl := bin_is_pm o hop
    · exact (turm_bin n bkn l r rest hs hl hr2 hr hrs hrg).2.2.2.2.2.2.2 F (by omega)
    · exact (turm_bin_star n bStar l r rest hs hl hr2 hr hrs hrg).2.2.2.2.2.2.2 F (by omega)
    · exact (turm_bin_or n bOr l r rest hs hl hr2 hr hrs hrg).2.2.2.2.2.2.2 F (by omega)
    · exact (turm_bin_and n bAnd l r rest hs hl hr2 hr hrs hrg).2.2.2.2.2.2.2 F (by omega)
  | field x f =>
    rw [gutKern_feld] at hg
    have hpp : gutKernPlatz (.field x f) = true := by
      rw [gutKernPlatz_feld]; exact hg
    exact (turm_platz n rkn (.field x f) rest hs hpp hr hrs hrg).2.2.2.2.2.2.2 F (by omega)
  | index x i =>
    rw [gutKern_index] at hg
    simp only [Bool.and_eq_true] at hg
    obtain ⟨hpx, hi⟩ := hg
    have hpp : gutKernPlatz (.index x i) = true := by
      rw [gutKernPlatz_index]; simp only [Bool.and_eq_true]; exact ⟨hpx, hi⟩
    exact (turm_platz n rkn (.index x i) rest hs hpp hr hrs hrg).2.2.2.2.2.2.2 F (by omega)
  | arrow x f =>
    rw [gutKern_pfeil] at hg
    have hpp : gutKernPlatz (.arrow x f) = true := by
      rw [gutKernPlatz_pfeil]; exact hg
    exact (turm_platz n rkn (.arrow x f) rest hs hpp hr hrs hrg).2.2.2.2.2.2.2 F (by omega)
  | call f xs => simp only [gutKern, Bool.false_eq_true] at hg
  | fnref f => simp only [gutKern, Bool.false_eq_true] at hg
  | built f xs => simp only [gutKern, Bool.false_eq_true] at hg
  | old x => simp only [gutKern, Bool.false_eq_true] at hg
  | res => simp only [gutKern, Bool.false_eq_true] at hg
  | why g f => simp only [gutKern, Bool.false_eq_true] at hg
  | ext xk xn xs => simp only [gutKern, Bool.false_eq_true] at hg

theorem kernAnd_step : ∀ (n : Nat), RKern n → BKern n → BKernStar n → BKernOr n → BKernAnd n →
    (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n + 1 →
      gutKern e = true → ruhig rest = true → ruhigSuff rest = true →
      ruhigGleit rest = true →
      12 * (groesse e + 1) + groesse e + 7 ≤ F →
      parseAnd F (druckToks e ++ rest) = .ok (e, rest)) := by
  intro n rkn bkn bStar bOr bAnd e rest F hs hg hr hrs hrg hF
  cases e with
  | lit m => exact (turm_lit m rest hr hrs hrg).2.2.2.2.2.2.1 F (by omega)
  | float s => exact (turm_gleit s rest hr hrs hrg).2.2.2.2.2.2.1 F (by omega)
  | tru => exact (turm_wahr rest hr hrs hrg).2.2.2.2.2.2.1 F (by omega)
  | fls => exact (turm_falsch rest hr hrs hrg).2.2.2.2.2.2.1 F (by omega)
  | «variable» a =>
    have hka : (!istKopfWort a) = true := by
      simp only [gutKern] at hg
      exact hg
    exact (turm_var a rest hka hr hrs hrg).2.2.2.2.2.2.1 F (by omega)
  | un o x =>
    rw [gutKern_un] at hg
    simp only [Bool.and_eq_true] at hg
    obtain ⟨hop, hgx⟩ := hg
    exact (turm_un n rkn o x rest hop hs hgx hr hrs hrg).2.2.2.2.2.1 F (by omega)
  | bin o l r =>
    rw [gutKern_bin] at hg
    simp only [Bool.and_eq_true, and_assoc] at hg
    obtain ⟨hop, hl, hr2⟩ := hg
    obtain rfl | rfl | rfl | rfl := bin_is_pm o hop
    · exact (turm_bin n bkn l r rest hs hl hr2 hr hrs hrg).2.2.2.2.2.2.1 F (by omega)
    · exact (turm_bin_star n bStar l r rest hs hl hr2 hr hrs hrg).2.2.2.2.2.2.1 F (by omega)
    · exact (turm_bin_or n bOr l r rest hs hl hr2 hr hrs hrg).2.2.2.2.2.2.1 F (by omega)
    · exact (turm_bin_and n bAnd l r rest hs hl hr2 hr hrs hrg).2.2.2.2.2.2.1 F (by omega)
  | field x f =>
    rw [gutKern_feld] at hg
    have hpp : gutKernPlatz (.field x f) = true := by
      rw [gutKernPlatz_feld]; exact hg
    exact (turm_platz n rkn (.field x f) rest hs hpp hr hrs hrg).2.2.2.2.2.2.1 F (by omega)
  | index x i =>
    rw [gutKern_index] at hg
    simp only [Bool.and_eq_true] at hg
    obtain ⟨hpx, hi⟩ := hg
    have hpp : gutKernPlatz (.index x i) = true := by
      rw [gutKernPlatz_index]; simp only [Bool.and_eq_true]; exact ⟨hpx, hi⟩
    exact (turm_platz n rkn (.index x i) rest hs hpp hr hrs hrg).2.2.2.2.2.2.1 F (by omega)
  | arrow x f =>
    rw [gutKern_pfeil] at hg
    have hpp : gutKernPlatz (.arrow x f) = true := by
      rw [gutKernPlatz_pfeil]; exact hg
    exact (turm_platz n rkn (.arrow x f) rest hs hpp hr hrs hrg).2.2.2.2.2.2.1 F (by omega)
  | call f xs => simp only [gutKern, Bool.false_eq_true] at hg
  | fnref f => simp only [gutKern, Bool.false_eq_true] at hg
  | built f xs => simp only [gutKern, Bool.false_eq_true] at hg
  | old x => simp only [gutKern, Bool.false_eq_true] at hg
  | res => simp only [gutKern, Bool.false_eq_true] at hg
  | why g f => simp only [gutKern, Bool.false_eq_true] at hg
  | ext xk xn xs => simp only [gutKern, Bool.false_eq_true] at hg

end Gabbro.Grammatik.Parser
