module

public import Grammatik.Parser.Round.RundlaufVoll
public import Grammatik.Parser.Round.RundlaufTok.Teil2

@[expose] public section

namespace Gabbro.Grammatik.Parser

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
  simp only [hmiss]
  exact suffM suff (.variable a) rest F'' hs hr (by omega)

/-- Size and printability of index payloads. -/
theorem suff_idx_mem : ∀ (suff : List SuffFrag) (i : SExpr), SuffFrag.idx i ∈ suff →
    suffGut suff = true → groesse i ≤ suffGroesse suff ∧ gut i = true := by
  intro suff
  induction suff with
  | nil => intro i h; simp only [List.not_mem_nil] at h
  | cons f s ih =>
    intro i h hg
    simp only [List.mem_cons] at h
    cases f with
    | dot g =>
      simp only [suffGut] at hg
      rcases h with h | h
      · cases h
      · obtain ⟨h1, h2⟩ := ih i h hg; exact ⟨by simp only [suffGroesse]; omega, h2⟩
    | arrow g =>
      simp only [suffGut] at hg
      rcases h with h | h
      · cases h
      · obtain ⟨h1, h2⟩ := ih i h hg; exact ⟨by simp only [suffGroesse]; omega, h2⟩
    | idx j =>
      simp only [suffGut, Bool.and_eq_true] at hg
      rcases h with h | h
      · cases h; simp only [suffGroesse]; exact ⟨by omega, hg.1⟩
      · obtain ⟨h1, h2⟩ := ih i h hg.2; exact ⟨by simp only [suffGroesse]; omega, h2⟩

/-! ### Calls -/

/-- One argument through `parseArg` at token fuel (mirror of `arg_legs`). -/
theorem argM (x : SExpr) (sep : Token) (S : List Token) (F : Nat)
    (hL : LegsB (fb x) x) (hxg : gut x = true)
    (hsep : sep = .zeichen "," ∨ sep = .zeichen ")") (hF : fb x + 9 ≤ F) :
    parseArg F (druckToks x ++ [sep] ++ S) = .ok (x, [sep] ++ S) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  have hmiss : ∀ (t0 : Token) (rest : List Token),
      druckToks x ++ [sep] ++ S ≠ t0 :: .zeichen ":" :: rest := by
    intro t0 rest hcon
    have hne : druckToks x ≠ [] := by
      intro he
      have hlen := toksLang (groesse x) x (Nat.le_refl _)
      rw [he] at hlen
      simp only [List.length_nil, Nat.le_zero_eq, Nat.succ_ne_self] at hlen
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
      | inl h => subst h; simp only [Token.zeichen.injEq, String.reduceEq] at hsep2
      | inr h => subst h; simp only [Token.zeichen.injEq, String.reduceEq] at hsep2
    | cons b R3 =>
      rw [hR] at ht
      simp only [List.cons_append] at ht
      injection ht with hb _
      have hbmem : b ∈ druckToks x := by simp only [hxb, hR, List.mem_cons, true_or, or_true]
      exact keinDP_tree (groesse x) x (Nat.le_refl _) hxg b hbmem hb
  simp only [parseArg]
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
  have hOr := hL.2.2.2.2.2.2.2 ([sep] ++ S) F' hr1 hr2 hr3 (by omega)
  simpa only [List.append_assoc] using hOr

theorem kopf_nicht_zu (x : SExpr) (hxg : gut x = true) (S : List Token) (R2 : List Token) :
    druckToks x ++ S ≠ .zeichen ")" :: R2 := by
  intro hcon
  have hkop := toksKopf (groesse x) x (Nat.le_refl _) hxg
  have hne : druckToks x ≠ [] := by
    intro he
    have hlen := toksLang (groesse x) x (Nat.le_refl _)
    rw [he] at hlen
    simp only [List.length_nil, Nat.le_zero_eq, Nat.succ_ne_self] at hlen
  obtain ⟨a, R3, hxb⟩ := List.exists_cons_of_ne_nil hne
  have ha := hkop a R3 hxb
  rw [hxb] at hcon
  simp only [List.cons_append] at hcon
  injection hcon with ha2 _
  exact ha ha2

/-- Whole argument lists through `parseArgs` at token fuel (mirror of `args_legs`). -/
theorem argsM : ∀ (xs : List SExpr) (rest : List Token) (F : Nat),
    (∀ x ∈ xs, LegsB (fb x) x ∧ gut x = true) →
    6 * (druckToksListe xs).length + 36 ≤ F →
    parseArgs F (druckToksListe xs ++ [.zeichen ")"] ++ rest) = .ok (xs, rest) := by
  intro xs
  induction xs with
  | nil =>
    intro rest F _ hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [parseArgs, druckToksListe, List.nil_append, List.cons_append]
  | cons x zs ihzs =>
    intro rest F hs hF
    obtain ⟨hLx, hxg⟩ := hs x (by simp only [List.mem_cons, true_or])
    have hzs : ∀ y ∈ zs, LegsB (fb y) y ∧ gut y = true :=
      fun y hy => hs y (List.mem_cons_of_mem _ hy)
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    cases zs with
    | nil =>
      rw [args_einzeln] at ⊢ hF
      have hmiss2 : ∀ (R2 : List Token),
          druckToks x ++ [.zeichen ")"] ++ rest ≠ .zeichen ")" :: R2 := by
        intro R2; rw [List.append_assoc]; exact kopf_nicht_zu x hxg _ R2
      simp only [parseArgs, hmiss2]
      have harg := argM x (.zeichen ")") rest F' hLx hxg (Or.inr rfl)
        (by simp only [fb] at ⊢; omega)
      simp only [harg, List.cons_append]
      rfl
    | cons y ys =>
      rw [args_cons] at ⊢ hF
      simp only [List.length_append, List.length_cons, List.length_nil] at hF
      have hmiss2 : ∀ (R2 : List Token),
          druckToks x ++ [.zeichen ","] ++ druckToksListe (y :: ys) ++
            [.zeichen ")"] ++ rest ≠ .zeichen ")" :: R2 := by
        intro R2; simp only [List.append_assoc]; exact kopf_nicht_zu x hxg _ R2
      simp only [parseArgs, hmiss2]
      have harg := argM x (.zeichen ",")
        (druckToksListe (y :: ys) ++ [.zeichen ")"] ++ rest) F'
        hLx hxg (Or.inl rfl) (by simp only [fb] at ⊢; omega)
      have htail := ihzs rest F' hzs (by omega)
      simp only [List.append_assoc, List.cons_append, List.nil_append] at ⊢ harg htail
      simp only [harg, htail, List.cons_append, List.nil_append]

/-- Calls through `parsePrimary` at token fuel (mirror of `prim_ruf_legs`). -/
theorem prim_rufM (f : String) (xs : List SExpr) (rest : List Token) (F : Nat)
    (hf : (!istKopfWort f) = true) (hxs : ∀ x ∈ xs, LegsB (fb x) x ∧ gut x = true)
    (hF : 6 * (druckToksListe xs).length + 38 ≤ F) :
    parsePrimary F (druckToks (.call f xs) ++ rest) = .ok (.call f xs, rest) := by
  have hkaf' : istKopfWort f = false := nichtWahr_falsch _ hf
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [druckToks, List.cons_append]
  rw [parsePrimary_nameTok _ _ _ hkaf']
  obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
  simp only [kopf_ruf_head]
  have hA := argsM xs rest F'' hxs (by omega)
  simp only [List.append_assoc] at hA ⊢
  simp only [List.nil_append, hA]

/-! ### Calls through a place (`o.is_some()`, `p->f(x)`) -/

/-- Every fragment prints at least one token. -/
theorem suffLen_le : ∀ (suff : List SuffFrag), suff.length ≤ (suffToks suff).length
  | [] => Nat.le_refl _
  | .dot _ :: s => by have := suffLen_le s; simp only [suffToks, List.length_cons]; omega
  | .arrow _ :: s => by have := suffLen_le s; simp only [suffToks, List.length_cons]; omega
  | .idx i :: s => by
    have := suffLen_le s
    simp only [suffToks, List.length_cons, List.length_append, List.length_singleton]; omega

/-- A suffix chain read off any follow: `parseSuffixe` spends one fuel per fragment and stands at the
    applied chain before the follow. -/
theorem suffWeiterM : ∀ (suff : List SuffFrag) (base : SExpr) (R : List Token) (F : Nat),
    SuffLegs suff → 6 * (suffToks suff).length + 29 ≤ F →
    parseSuffixe F base (suffToks suff ++ R) = parseSuffixe (F - suff.length) (applySuff base suff) R := by
  intro suff
  induction suff with
  | nil => intro base R F _ _; simp only [suffToks, List.nil_append, List.length_nil, Nat.sub_zero, applySuff]
  | cons frag suff ih =>
    intro base R F hs hF
    have hs' := suffLegs_tail hs
    simp only [List.length_cons]
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    rw [Nat.add_sub_add_right]
    cases frag with
    | dot f =>
      simp only [suffToks, List.cons_append]
      simp only [parseSuffixe, nameText_nameTok]
      simp only [applySuff]
      simp only [suffToks, List.length_cons] at hF
      exact ih _ R F' hs' (by omega)
    | arrow f =>
      simp only [suffToks, List.cons_append]
      simp only [parseSuffixe, nameText_nameTok]
      simp only [applySuff]
      simp only [suffToks, List.length_cons] at hF
      exact ih _ R F' hs' (by omega)
    | idx i =>
      have hLi := hs i (by simp only [List.mem_cons, true_or])
      simp only [suffToks, List.length_cons, List.length_append, List.length_singleton] at hF
      simp only [suffToks, List.cons_append]
      simp only [parseSuffixe]
      have hr1 : ruhig ([.zeichen "]"] ++ suffToks suff ++ R) = true := rfl
      have hr2 : ruhigSuff ([.zeichen "]"] ++ suffToks suff ++ R) = true := rfl
      have hr3 : ruhigGleit ([.zeichen "]"] ++ suffToks suff ++ R) = true := rfl
      have hOi := hLi.2.2.2.2.2.2.2 ([.zeichen "]"] ++ suffToks suff ++ R) F' hr1 hr2 hr3
        (by simp only [fb]; omega)
      simp only [List.append_assoc, List.cons_append, List.nil_append] at ⊢ hOi
      simp only [hOi, List.cons_append]
      simp only [applySuff]
      exact ih _ R F' hs' (by omega)

/-- A chain that is not a bare name reads `(` as a call through it. -/
theorem suff_ruf (G : Nat) (c : SExpr) (T : List Token) (hc : istVar c = false) :
    parseSuffixe (G + 1) c (.zeichen "(" :: T) =
      match parseArgs G T with
      | .ok (args, rest') => parseSuffixe G (.ext .call [] (c :: args)) rest'
      | .error e => .error e := by
  cases c with
  | «variable» s => simp only [istVar, Bool.true_eq_false] at hc
  | _ => simp only [parseSuffixe] <;> rfl

theorem istVar_applySuff : ∀ (suff : List SuffFrag) (base : SExpr), istVar base = false →
    istVar (applySuff base suff) = false
  | [], _, h => h
  | .dot _ :: s, _, _ => istVar_applySuff s _ rfl
  | .arrow _ :: s, _, _ => istVar_applySuff s _ rfl
  | .idx _ :: s, _, _ => istVar_applySuff s _ rfl

theorem istVar_kette (a : String) (suff : List SuffFrag) (hne : suff ≠ []) :
    istVar (applySuff (.variable a) suff) = false := by
  cases suff with
  | nil => exact absurd rfl hne
  | cons f s => cases f <;> exact istVar_applySuff s _ rfl

end Gabbro.Grammatik.Parser
