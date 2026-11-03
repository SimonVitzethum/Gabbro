module

public import Grammatik.Parser.Round.RundlaufVoll
public import Grammatik.Parser.Round.RundlaufTok.Teil2

@[expose] public section

namespace Gabbro.Grammatik.Parser

/-- The `&&` inner trace over a bound (mirror of `andB_step`). -/
theorem andB_stepM : ∀ (m : Nat) (l r : SExpr) (W : List Token),
    (∀ (G : Nat), m + 2 ≤ G →
      parseUnary G (druckToks l ++ ([.zeichen "&&"] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (l, [.zeichen "&&"] ++ (druckToks r ++ ([.zeichen ")"] ++ W)))) →
    (∀ (G : Nat), m + 6 ≤ G →
      parseCmp G (druckToks r ++ ([.zeichen ")"] ++ W)) = .ok (r, [.zeichen ")"] ++ W)) →
    ∀ (G : Nat), m + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen "&&"] ++ druckToks r ++
        [.zeichen ")"] ++ W) =
        .ok (.bin "&&" l r, [.zeichen ")"] ++ W) := by
  intro m l r W hUl hCr F hF
  simp only [List.append_assoc] at ⊢
  have hup := tower_up_andbarM m l ([.zeichen "&&"] ++
    (druckToks r ++ ([.zeichen ")"] ++ W))) hUl
    (opMul_andbar _) (opAdd_andbar _) (opBit_andbar _) (opVgl_andbar _)
  have hAnd : ∀ (G1 : Nat), m + 9 ≤ G1 →
      parseAnd G1 (druckToks l ++ ([.zeichen "&&"] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin "&&" l r, [.zeichen ")"] ++ W) := by
    intro G1 hG1
    obtain ⟨G2, rfl⟩ : ∃ G2, G1 = G2 + 1 := ⟨G1 - 1, by omega⟩
    have hC' := hup.2.2.2 G2 (by omega)
    obtain ⟨G2x, rfl⟩ : ∃ G2x, G2 = G2x + 1 := ⟨G2 - 1, by omega⟩
    have hop := opUnd_and_some (druckToks r ++ ([.zeichen ")"] ++ W))
    have hMr := hCr G2x (by omega)
    obtain ⟨G2y, rfl⟩ : ∃ G2y, G2x = G2y + 1 := ⟨G2x - 1, by omega⟩
    have hstop := opUnd_paren W
    simp only [parseAnd, parseAndL, hC', hop, hMr, hstop] at ⊢
  obtain ⟨G1, rfl⟩ : ∃ G1, F = G1 + 1 := ⟨F - 1, by omega⟩
  have hAnd' := hAnd G1 (by omega)
  obtain ⟨G1x, rfl⟩ : ∃ G1x, G1 = G1x + 1 := ⟨G1 - 1, by omega⟩
  have hstop := opOder_paren W
  simp only [parseOr, parseOrL, hAnd', hstop] at ⊢

/-- Every lawful binary spelling over two operands at one bound `m`: the parent is at `m + 10`. -/
theorem binLegsM (m : Nat) (o : String) (l r : SExpr) (ho : gutOpBin o = true)
    (Hl : LegsB m l) (Hr : LegsB m r) : LegsB (m + 10) (.bin o l r) := by
  apply bin_turmM m o l r
  intro T G hG
  have hUr : ∀ (G' : Nat), m + 2 ≤ G' →
      parseUnary G' (druckToks r ++ ([.zeichen ")"] ++ T)) = .ok (r, [.zeichen ")"] ++ T) :=
    fun G' hG' => Hr.2.1 _ G' (hrs_paren T) (hrg_paren T) hG'
  simp only [gutOpBin, Bool.or_eq_true] at ho
  rcases ho with ((((ho | ho) | ho) | ho) | ho) | ho
  · have : o = "||" := strKlingt o "||" ho
    subst this
    exact orB_stepM m l r T (fun G' hG' => Hl.2.1 _ G' (hrs_orbar _) (hrg_orbar _) hG')
      (fun G' hG' => Hr.2.2.2.2.2.2.1 _ G' (hr_paren T) (hrs_paren T) (hrg_paren T) hG') G hG
  · have : o = "&&" := strKlingt o "&&" ho
    subst this
    exact andB_stepM m l r T (fun G' hG' => Hl.2.1 _ G' (hrs_andbar _) (hrg_andbar _) hG')
      (fun G' hG' => Hr.2.2.2.2.2.1 _ G' (hr_paren T) (hrs_paren T) (hrg_paren T) hG') G hG
  · obtain ⟨hmMul, hmAdd, hmBit, hrsS1, hrgS1⟩ :=
      cmpbar_facts o (druckToks r ++ ([.zeichen ")"] ++ T)) ho
    exact cmpB_stepM m o l r T (fun G' hG' => Hl.2.1 _ G' hrsS1 hrgS1 hG') hUr hmMul hmAdd hmBit
      (opVgl_cmp_hit o _ ho) G hG
  · obtain ⟨hmMul, hmAdd, hrsS1, hrgS1⟩ :=
      bitbar_facts o (druckToks r ++ ([.zeichen ")"] ++ T)) ho
    exact bitB_stepM m o l r T (fun G' hG' => Hl.2.1 _ G' hrsS1 hrgS1 hG') hUr hmMul hmAdd
      (opBit_bit_hit o _ ho) G hG
  · obtain ⟨hmMul, hrsS1, hrgS1⟩ :=
      addbar_facts o (druckToks r ++ ([.zeichen ")"] ++ T)) ho
    exact addB_stepM m o l r T (fun G' hG' => Hl.2.1 _ G' hrsS1 hrgS1 hG') hUr hmMul
      (opAdd_add_hit o _ ho) hrsS1 hrgS1 G hG
  · obtain ⟨hrsS1, hrgS1⟩ :=
      mulbar_facts o (druckToks r ++ ([.zeichen ")"] ++ T)) ho
    exact mulB_stepM m o l r T (fun G' hG' => Hl.2.1 _ G' hrsS1 hrgS1 hG') hUr
      (opMul_mul_hit o _ ho) hrsS1 hrgS1 G hG

/-! ### Prefix operators -/

/-- A prefix over an ATOM operand costs no fuel beyond the operand's bound. -/
theorem unLegsM_atom (m : Nat) (o : String) (x : SExpr) (ho : gutOpUn o = true)
    (hat : istAtom x = true) (Hx : LegsB m x) : LegsB m (.un o x) := by
  have hpf := primFrei_of_istAtom x hat
  have hd : druckToks (.un o x) = [.zeichen o] ++ druckToks x := by
    simp only [druckToks, un_ne_klammer _ ho, Bool.false_eq_true, ↓reduceIte, hat, List.cons_append,
  List.nil_append]
  apply legsB_aus m _ (fun rest G h => by simp only [primFrei, Bool.false_eq_true] at h)
  intro rest G hrs hrg hG
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
  have hP' := Hx.1 rest G' hpf hrs hrg (by omega)
  simp only [hd, List.append_assoc] at ⊢
  exact bang_arm_gen _ _ _ _ _ ho hP' (atom_bed x rest)

/-- A prefix over a parenthesised operand: eight more (the `(` arm runs `parseOr`). -/
theorem unLegsM_klammer (m : Nat) (o : String) (x : SExpr) (ho : gutOpUn o = true)
    (hat : istAtom x = false) (Hx : LegsB m x) : LegsB (m + 8) (.un o x) := by
  have hd : druckToks (.un o x) = [.zeichen o] ++
      (([.zeichen "("] ++ druckToks x) ++ [.zeichen ")"]) := by
    simp only [druckToks, un_ne_klammer _ ho, Bool.false_eq_true, ↓reduceIte, hat, List.cons_append,
  List.nil_append]
  apply legsB_aus _ _ (fun rest G h => by simp only [primFrei, Bool.false_eq_true] at h)
  intro rest G hrs hrg hG
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
  obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
  have hO' := Hx.2.2.2.2.2.2.2 _ G'' (hr_paren rest) (hrs_paren rest) (hrg_paren rest)
    (by omega)
  have hPar := paren_arm _ _ _ _ hO'
  have hBang := bang_arm_gen _ _ _ _ _ ho hPar (Or.inr (nonatom_bed x hat))
  simp only [hd, List.append_assoc] at ⊢
  exact hBang

/-- `-(n)`: the parenthesised arm of `-` over a numeral, eight more. -/
theorem negLitLegsM (m : Nat) (n : Nat) (Hx : LegsB m (.lit n)) : LegsB (m + 8) (.un "-()" (.lit n)) := by
  have hs0 : strEq "-()" "-()" = true := by decide
  have hd : druckToks (.un "-()" (.lit n)) = [.zeichen "-", .zeichen "("] ++ (druckToks (.lit n) ++ [.zeichen ")"]) := by
    simp only [druckToks, hs0, ite_true, List.append_assoc]
  apply legsB_aus _ _ (fun rest G h => by simp only [primFrei, Bool.false_eq_true] at h)
  intro rest G hrs hrg hG
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
  obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
  have hO' := Hx.2.2.2.2.2.2.2 _ G'' (hr_paren rest) (hrs_paren rest) (hrg_paren rest)
    (by omega)
  have hPar := paren_arm _ _ _ _ hO'
  have hN := negklammer_arm _ _ _ n hPar
  simp only [hd, List.append_assoc] at ⊢
  simpa only [List.append_assoc] using hN

/-! ### The token measure -/

/-- The fuel bound of the token measure: six per printed token, twenty-six spare (the leaves'
    size bound is twenty-five). -/
def fb (e : SExpr) : Nat := 6 * (druckToks e).length + 26

/-! ### Places -/

/-- Every index payload of a suffix chain has legs at its token bound. -/
def SuffLegs (suff : List SuffFrag) : Prop := ∀ i, SuffFrag.idx i ∈ suff → LegsB (fb i) i

theorem suffLegs_tail {f : SuffFrag} {s : List SuffFrag} (h : SuffLegs (f :: s)) : SuffLegs s :=
  fun i hi => h i (List.mem_cons_of_mem _ hi)

/-- Suffix chains through `parseSuffixe` at token fuel (lane 161's `suff_rund`, restated). -/
theorem suffM : ∀ (suff : List SuffFrag) (base : SExpr) (rest : List Token) (F : Nat),
    SuffLegs suff → ruhigSuff rest = true →
    6 * (suffToks suff).length + 29 ≤ F →
    parseSuffixe F base (suffToks suff ++ rest) = .ok (applySuff base suff, rest) := by
  intro suff
  induction suff with
  | nil =>
    intro base rest F _ hr hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [suffToks, List.nil_append]
    exact stopSuffix F' base rest hr
  | cons frag suff ih =>
    intro base rest F hs hr hF
    have hs' := suffLegs_tail hs
    cases frag with
    | dot f =>
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      simp only [suffToks, List.cons_append]
      simp only [parseSuffixe, nameText_nameTok]
      simp only [applySuff]
      simp only [suffToks, List.length_cons] at hF
      exact ih _ rest F' hs' hr (by omega)
    | arrow f =>
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      simp only [suffToks, List.cons_append]
      simp only [parseSuffixe, nameText_nameTok]
      simp only [applySuff]
      simp only [suffToks, List.length_cons] at hF
      exact ih _ rest F' hs' hr (by omega)
    | idx i =>
      have hLi := hs i (by simp only [List.mem_cons, true_or])
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      simp only [suffToks, List.length_cons, List.length_append, List.length_singleton] at hF
      simp only [suffToks, List.cons_append]
      simp only [parseSuffixe]
      have hr1 : ruhig ([.zeichen "]"] ++ suffToks suff ++ rest) = true := rfl
      have hr2 : ruhigSuff ([.zeichen "]"] ++ suffToks suff ++ rest) = true := rfl
      have hr3 : ruhigGleit ([.zeichen "]"] ++ suffToks suff ++ rest) = true := rfl
      have hOi := hLi.2.2.2.2.2.2.2 ([.zeichen "]"] ++ suffToks suff ++ rest) F' hr1 hr2 hr3
        (by simp only [fb]; omega)
      simp only [List.append_assoc, List.cons_append, List.nil_append] at ⊢ hOi
      simp only [hOi, List.cons_append]
      simp only [applySuff]
      exact ih _ rest F' hs' hr (by omega)

/-- Places through `parseOrt` at token fuel. -/
theorem ortM (a : String) (suff : List SuffFrag) (rest : List Token) (F : Nat)
    (hka : (!istKopfWort a) = true) (hs : SuffLegs suff) (hr : ruhigSuff rest = true)
    (hF : 6 * (suffToks suff).length + 30 ≤ F) :
    parseOrt F (druckToks (applySuff (.variable a) suff) ++ rest) =
      .ok (applySuff (.variable a) suff, rest) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  rw [druckToks_applySuff]
  have hkaf : istKeinPlatz a = false := kopf_kp (nichtWahr_falsch _ hka)
  simp only [parseOrt, druckToks, nameText_nameTok, hkaf, List.cons_append, List.nil_append,
    List.append_assoc]
  simp only [Bool.false_eq_true, ite_false]
  exact suffM suff (.variable a) rest F' hs hr (by omega)

/-- Places through `parsePrimary` at token fuel (lane 161's `prim_platz`, restated). -/
theorem prim_platzM (a : String) (suff : List SuffFrag) (rest : List Token) (F : Nat)
    (hka : (!istKopfWort a) = true) (hs : SuffLegs suff) (hr : ruhigSuff rest = true)
    (hF : 6 * (suffToks suff).length + 31 ≤ F) :
    parsePrimary F (druckToks (applySuff (.variable a) suff) ++ rest) =
      .ok (applySuff (.variable a) suff, rest) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
  rw [druckToks_applySuff]
  simp only [druckToks, List.cons_append]
  rw [parsePrimary_nameTok _ _ _ (nichtWahr_falsch _ hka)]
  simp only [parseKopf, nameText_nameTok]
  simp only [List.nil_append]
  simp only [sammleSeg_suffToks, hr]
  have hmiss : ∀ (R : List Token), suffToks suff ++ rest ≠ .zeichen "(" :: R := by
    intro R hcon
    exact suffToks_nopar suff rest R hr hcon
  rw [rufKopf_ohne _ _ _ _ (suffToks_nogeneric suff rest hr) hmiss]
  exact suffM suff (.variable a) rest F'' hs hr (by omega)


end Gabbro.Grammatik.Parser
