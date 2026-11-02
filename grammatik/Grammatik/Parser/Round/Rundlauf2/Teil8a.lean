module

public import Grammatik.Parser.Round.Rundlauf
public import Grammatik.Parser.Round.Rundlauf2.Teil7

@[expose] public section

namespace Gabbro.Grammatik.Parser

-- The `parseUnary` step: no `ruhig` premise (loops never see
-- the tail here), so atoms prove their fall-through legs
-- directly from the primary legs, and `un`/`bin` replay their
-- tower proofs with induction-hypothesis legs.
theorem kernUnary_step : ∀ (n : Nat), RKern n → BKern n → BKernStar n → BKernOr n → BKernAnd n →
    (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n + 1 →
      gutKern e = true → ruhigSuff rest = true →
      ruhigGleit rest = true →
      12 * (groesse e + 1) + groesse e + 2 ≤ F →
      parseUnary F (druckToks e ++ rest) = .ok (e, rest)) := by
  intro n rkn bkn bStar bOr bAnd e rest F hs hg hrs hrg hF
  have rkn' := rkn
  obtain ⟨rOr, -, -, -, -, -, -, rPr⟩ := rkn
  cases e with
  | lit m =>
    have hP : ∀ (G : Nat), 12 * (groesse (.lit m) + 1) + groesse (.lit m) + 1 ≤ G →
        parsePrimary G (druckToks (.lit m) ++ rest) = .ok (.lit m, rest) := by
      intro G hG
      exact prim_lit m rest G (by omega)
    have hG1 : 1 ≤ F := by omega
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [druckToks, List.cons_append, List.nil_append] at ⊢
    first | rw [parseUnary_nameTok] | simp only [parseUnary] at ⊢
    exact hP F' (by omega)
  | float s =>
    have hP : ∀ (G : Nat), 12 * (groesse (.float s) + 1) + groesse (.float s) + 1 ≤ G →
        parsePrimary G (druckToks (.float s) ++ rest) = .ok (.float s, rest) := by
      intro G hG
      exact prim_gleit s rest G hrg (by omega)
    have hG1 : 1 ≤ F := by omega
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [druckToks, List.cons_append, List.nil_append] at ⊢
    first | rw [parseUnary_nameTok] | simp only [parseUnary] at ⊢
    exact hP F' (by omega)
  | tru =>
    have hP : ∀ (G : Nat), 12 * (groesse .tru + 1) + groesse .tru + 1 ≤ G →
        parsePrimary G (druckToks .tru ++ rest) = .ok (.tru, rest) := by
      intro G hG
      exact prim_wahr rest G (by omega)
    have hG1 : 1 ≤ F := by omega
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [druckToks, List.cons_append, List.nil_append] at ⊢
    first | rw [parseUnary_nameTok] | simp only [parseUnary] at ⊢
    exact hP F' (by omega)
  | fls =>
    have hP : ∀ (G : Nat), 12 * (groesse .fls + 1) + groesse .fls + 1 ≤ G →
        parsePrimary G (druckToks .fls ++ rest) = .ok (.fls, rest) := by
      intro G hG
      exact prim_falsch rest G (by omega)
    have hG1 : 1 ≤ F := by omega
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [druckToks, List.cons_append, List.nil_append] at ⊢
    first | rw [parseUnary_nameTok] | simp only [parseUnary] at ⊢
    exact hP F' (by omega)
  | «variable» a =>
    have hka : (!istKopfWort a) = true := by
      simp only [gutKern] at hg
      exact hg
    have hP : ∀ (G : Nat), 12 * (groesse (.variable a) + 1) + groesse (.variable a) + 1 ≤ G →
        parsePrimary G (druckToks (.variable a) ++ rest) =
          .ok (.variable a, rest) := by
      intro G hG
      exact kern_prim_var a rest G hka hrs (by omega)
    have hG1 : 1 ≤ F := by omega
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [druckToks, List.cons_append, List.nil_append] at ⊢
    first | rw [parseUnary_nameTok] | simp only [parseUnary] at ⊢
    exact hP F' (by omega)
  | un o x =>
    rw [gutKern_un] at hg
    simp only [Bool.and_eq_true] at hg
    obtain ⟨hop, hgx⟩ := hg
    have hsize : groesse (.un o x) = groesse x + 1 := rfl
    have hxn : groesse x ≤ n := by omega
    have hG1 : 1 ≤ F := by omega
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    cases hat : istAtom x with
    | true =>
      have hpf : primFrei x = true := primFrei_of_atom x hat hgx
      have hPx : ∀ (G : Nat), 12 * (groesse x + 1) + groesse x + 1 ≤ G →
          parsePrimary G (druckToks x ++ rest) = .ok (x, rest) := by
        intro G hG
        exact rPr x rest G hxn hgx hpf hrs hrg hG
      have hd : druckToks (.un o x) =
          [.zeichen o] ++ druckToks x := by
        simp only [druckToks, un_ne_klammer _ hop, Bool.false_eq_true, ↓reduceIte, hat, List.cons_append,
  List.nil_append]
      have hP' := hPx F' (by omega)
      simp only [hd, List.append_assoc] at ⊢
      exact bang_arm_gen _ _ _ _ _ hop hP' (atom_bed x rest)
    | false =>
      have hOx : ∀ (G : Nat), 12 * (groesse x + 1) + groesse x + 8 ≤ G →
          parseOr G (druckToks x ++ ([.zeichen ")"] ++ rest)) =
            .ok (x, [.zeichen ")"] ++ rest) := by
        intro G hG
        exact rOr x ([.zeichen ")"] ++ rest) G hxn hgx
          (hr_paren rest) (hrs_paren rest) (hrg_paren rest) hG
      have hd : druckToks (.un o x) = [.zeichen o] ++
          (([.zeichen "("] ++ druckToks x) ++ [.zeichen ")"]) := by
        simp only [druckToks, un_ne_klammer _ hop, Bool.false_eq_true, ↓reduceIte, hat, List.cons_append,
  List.nil_append]
      have hF2 : 1 ≤ F' := by omega
      obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
      have hO' := hOx F'' (by omega)
      have hPar := paren_arm _ _ _ _ hO'
      have hBang := bang_arm_gen _ _ _ _ _ hop hPar (Or.inr (nonatom_bed x hat))
      simp only [hd, List.append_assoc] at ⊢
      exact hBang
  | bin o l r =>
    rw [gutKern_bin] at hg
    simp only [Bool.and_eq_true, and_assoc] at hg
    obtain ⟨hop, hl, hr2⟩ := hg
    obtain rfl | rfl | rfl | rfl := bin_is_pm o hop
    · have hsize : groesse (.bin "+" l r) = groesse l + groesse r + 1 := rfl
      have hsum : groesse l + groesse r ≤ n := by omega
      have hd : druckToks (.bin "+" l r) = [.zeichen "("] ++ druckToks l ++
          [.zeichen "+"] ++ druckToks r ++ [.zeichen ")"] := by
        simp only [druckToks, List.cons_append, List.nil_append, List.append_assoc]
      have hB : ∀ (G : Nat),
          12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
          parseOr G (druckToks l ++ [.zeichen "+"] ++ druckToks r ++
            [.zeichen ")"] ++ rest) =
            .ok (.bin "+" l r, [.zeichen ")"] ++ rest) := by
        intro G hG
        exact bkn l r rest G hsum hl hr2 hG
      have hG1 : 1 ≤ F := by omega
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      have hP' := kern_bin_prim l r rest hB F' (by omega)
      simp only [hd, List.append_assoc] at hP' ⊢
      exact un_paren_fall _ _ _ _ hP'
    · have hsize : groesse (.bin "*" l r) = groesse l + groesse r + 1 := rfl
      have hsum : groesse l + groesse r ≤ n := by omega
      have hd : druckToks (.bin "*" l r) = [.zeichen "("] ++ druckToks l ++
          [.zeichen "*"] ++ druckToks r ++ [.zeichen ")"] := by
        simp only [druckToks, List.cons_append, List.nil_append, List.append_assoc]
      have hB : ∀ (G : Nat),
          12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
          parseOr G (druckToks l ++ [.zeichen "*"] ++ druckToks r ++
            [.zeichen ")"] ++ rest) =
            .ok (.bin "*" l r, [.zeichen ")"] ++ rest) := by
        intro G hG
        exact bStar l r rest G hsum hl hr2 hG
      have hG1 : 1 ≤ F := by omega
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      have hP' := kern_bin_prim_star l r rest hB F' (by omega)
      simp only [hd, List.append_assoc] at hP' ⊢
      exact un_paren_fall _ _ _ _ hP'
    · have hsize : groesse (.bin "||" l r) = groesse l + groesse r + 1 := rfl
      have hsum : groesse l + groesse r ≤ n := by omega
      have hd : druckToks (.bin "||" l r) = [.zeichen "("] ++ druckToks l ++
          [.zeichen "||"] ++ druckToks r ++ [.zeichen ")"] := by
        simp only [druckToks, List.cons_append, List.nil_append, List.append_assoc]
      have hB : ∀ (G : Nat),
          12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
          parseOr G (druckToks l ++ [.zeichen "||"] ++ druckToks r ++
            [.zeichen ")"] ++ rest) =
            .ok (.bin "||" l r, [.zeichen ")"] ++ rest) := by
        intro G hG
        exact bOr l r rest G hsum hl hr2 hG
      have hG1 : 1 ≤ F := by omega
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      have hP' := kern_bin_prim_or l r rest hB F' (by omega)
      simp only [hd, List.append_assoc] at hP' ⊢
      exact un_paren_fall _ _ _ _ hP'
    · have hsize : groesse (.bin "&&" l r) = groesse l + groesse r + 1 := rfl
      have hsum : groesse l + groesse r ≤ n := by omega
      have hd : druckToks (.bin "&&" l r) = [.zeichen "("] ++ druckToks l ++
          [.zeichen "&&"] ++ druckToks r ++ [.zeichen ")"] := by
        simp only [druckToks, List.cons_append, List.nil_append, List.append_assoc]
      have hB : ∀ (G : Nat),
          12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
          parseOr G (druckToks l ++ [.zeichen "&&"] ++ druckToks r ++
            [.zeichen ")"] ++ rest) =
            .ok (.bin "&&" l r, [.zeichen ")"] ++ rest) := by
        intro G hG
        exact bAnd l r rest G hsum hl hr2 hG
      have hG1 : 1 ≤ F := by omega
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      have hP' := kern_bin_prim_and l r rest hB F' (by omega)
      simp only [hd, List.append_assoc] at hP' ⊢
      exact un_paren_fall _ _ _ _ hP'
  | field x f =>
    rw [gutKern_feld] at hg
    have hpp : gutKernPlatz (.field x f) = true := by
      rw [gutKernPlatz_feld]; exact hg
    exact (turm_platz_PU n rkn' (.field x f) rest hs hpp hrs hrg).2 F (by omega)
  | index x i =>
    rw [gutKern_index] at hg
    simp only [Bool.and_eq_true] at hg
    obtain ⟨hpx, hi⟩ := hg
    have hpp : gutKernPlatz (.index x i) = true := by
      rw [gutKernPlatz_index]; simp only [Bool.and_eq_true]; exact ⟨hpx, hi⟩
    exact (turm_platz_PU n rkn' (.index x i) rest hs hpp hrs hrg).2 F (by omega)
  | arrow x f =>
    rw [gutKern_pfeil] at hg
    have hpp : gutKernPlatz (.arrow x f) = true := by
      rw [gutKernPlatz_pfeil]; exact hg
    exact (turm_platz_PU n rkn' (.arrow x f) rest hs hpp hrs hrg).2 F (by omega)
  | call f xs => simp only [gutKern, Bool.false_eq_true] at hg
  | fnref f => simp only [gutKern, Bool.false_eq_true] at hg
  | built f xs => simp only [gutKern, Bool.false_eq_true] at hg
  | old x => simp only [gutKern, Bool.false_eq_true] at hg
  | res => simp only [gutKern, Bool.false_eq_true] at hg
  | why g f => simp only [gutKern, Bool.false_eq_true] at hg
  | ext xk xn xs => simp only [gutKern, Bool.false_eq_true] at hg


end Gabbro.Grammatik.Parser
