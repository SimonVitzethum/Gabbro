/-
  File:      Grammatik/Parser/Round/RundlaufVoll.lean
  Subject:   Layer L2a of the syntax round trip: the expression round trip for the WHOLE printable
             class `gut`, by the joint size induction that Rundlauf3's header names as the remaining
             blocker.

  Rundlauf3/4 widened the predicate one layer at a time (`gutKern` ... `gutPrim`), each layer over
  the previous one, so a `==` over a `&` over a call was out of reach. Here the size induction runs
  over `gut` itself:

    `legs_gut_n n : ∀ e, groesse e ≤ n → gut e = true → Legs e`

  Step `n + 1`: the hypothesis at `n` is repackaged as lane 161's size-bounded invariant `R n`
  (`R_of_legs`), which feeds the general lemmas lane 161 proved over `R n` and never closed the
  induction for (`prim_platz`, `prim_ruf`, `prim_alt`, `ort_platz_all` -- places with arbitrary
  `gut` index payloads, calls with arbitrary `gut` arguments, `old`/`sizeof`/`lenof` over arbitrary
  places). Binary operators take the generic operand-leg steps of Rundlauf3 (`cmpLegs`, `bitLegs`,
  `addLegs`, `mulLegs`) plus the two new ones here (`orLegs`, `andLegs`, the `||`/`&&` inner traces
  over abstract legs); prefixes take the spelling-blind towers of Rundlauf2 (`kern_un_atom_turm`,
  `kern_un_paren_turm`, which carry no predicate) over the operand's legs (`unLegs`).

  Main statements:
  - `legs_gut : ∀ e, gut e = true → Legs e`;
  - `parse_druck_gut : ∀ e, gut e = true → parseOr (brennstoff e) (druckToks e ++ [.ende]) =
     .ok (e, [.ende])`;
  The size bound (thirteen fuel per node) does not reach the fixed-fuel readers (`parseTop`, fuel
  `8 * length + 32`); `RundlaufTok` restates the induction at a TOKEN bound and closes `parseTop`
  and the composition with L1.

  `gut` is the printability predicate of lane 161 (Rundlauf.lean), unchanged: it excludes exactly
  the shapes with no token spelling that parses back (booked there): reserved heads
  (`istKeinPlatz`), unknown operator spellings, suffixes on non-places, `sizeof`/`lenof`/`old` over
  non-places, `sizeof`/`lenof` over a bare type word, `G::F` with an integer, sugared-width or
  `Self` head, and every `ext` form (predicates, strings, calls through places -- `druckExtToks`
  prints them, outside the theorem).
-/
import Grammatik.Parser.Round.Rundlauf4
import Grammatik.Parser.Round.RundlaufLex

namespace Gabbro.Grammatik.Parser

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

/-- Every lawful binary spelling, over operands with legs. -/
theorem binLegs : ∀ (o : String) (l r : SExpr),
    gutOpBin o = true → Legs l → Legs r → Legs (.bin o l r) := by
  intro o l r ho Hl Hr
  simp only [gutOpBin, Bool.or_eq_true] at ho
  rcases ho with ((((ho | ho) | ho) | ho) | ho) | ho
  · have : o = "||" := strKlingt o "||" ho
    subst this; exact orLegs l r Hl Hr
  · have : o = "&&" := strKlingt o "&&" ho
    subst this; exact andLegs l r Hl Hr
  · exact cmpLegs o l r ho Hl Hr
  · exact bitLegs o l r ho Hl Hr
  · exact addLegs o l r ho Hl Hr
  · exact mulLegs o l r ho Hl Hr

/-! ### Prefix operators over abstract legs -/

theorem primFrei_of_istAtom : ∀ (x : SExpr), istAtom x = true → primFrei x = true := by
  intro x hat
  cases x <;> simp_all [istAtom, primFrei]

/-- A prefix tree over an operand with legs. The primary component is vacuous (`primFrei` is
    false for `un`); the rest are the spelling-blind towers of Rundlauf2. -/
theorem unLegs : ∀ (o : String) (x : SExpr), gutOpUn o = true → Legs x → Legs (.un o x) := by
  intro o x ho Hx
  have hT : ∀ (rest : List Token), ruhig rest = true → ruhigSuff rest = true →
      ruhigGleit rest = true →
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
    intro rest hr hrs hrg
    cases hat : istAtom x with
    | true =>
      have hpf := primFrei_of_istAtom x hat
      exact kern_un_atom_turm o x rest ho hat hr (fun G hG => Hx.1 rest G hpf hrs hrg hG)
    | false =>
      exact kern_un_paren_turm o x rest ho hat hr
        (fun G hG => Hx.2.2.2.2.2.2.2 _ G (hr_paren rest) (hrs_paren rest) (hrg_paren rest) hG)
  -- The unary leg holds without `ruhig` (no loop runs at or below it): rebuild it directly.
  have hU : ∀ (rest : List Token) (G : Nat), ruhigSuff rest = true → ruhigGleit rest = true →
      12 * (groesse (.un o x) + 1) + groesse (.un o x) + 2 ≤ G →
      parseUnary G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest) := by
    intro rest G hrs hrg hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hsize : groesse (.un o x) = groesse x + 1 := rfl
    cases hat : istAtom x with
    | true =>
      have hpf := primFrei_of_istAtom x hat
      have hd : druckToks (.un o x) = [.zeichen o] ++ druckToks x := by
        simp [druckToks, hat]
      have hP' := Hx.1 rest G' hpf hrs hrg (by omega)
      simp only [hd, List.append_assoc] at ⊢
      exact bang_arm_gen _ _ _ _ _ ho hP'
    | false =>
      have hd : druckToks (.un o x) = [.zeichen o] ++
          (([.zeichen "("] ++ druckToks x) ++ [.zeichen ")"]) := by
        simp [druckToks, hat]
      have hF2 : 1 ≤ G' := by omega
      obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
      have hO' := Hx.2.2.2.2.2.2.2 _ G'' (hr_paren rest) (hrs_paren rest) (hrg_paren rest)
        (by omega)
      have hPar := paren_arm _ _ _ _ hO'
      have hBang := bang_arm_gen _ _ _ _ _ ho hPar
      simp only [hd, List.append_assoc] at ⊢
      exact hBang
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro rest G hpf; simp [primFrei] at hpf
  · exact hU
  · intro rest G hr hrs hrg hG; exact (hT rest hr hrs hrg).2.1 G hG
  · intro rest G hr hrs hrg hG; exact (hT rest hr hrs hrg).2.2.1 G hG
  · intro rest G hr hrs hrg hG; exact (hT rest hr hrs hrg).2.2.2.1 G hG
  · intro rest G hr hrs hrg hG; exact (hT rest hr hrs hrg).2.2.2.2.1 G hG
  · intro rest G hr hrs hrg hG; exact (hT rest hr hrs hrg).2.2.2.2.2.1 G hG
  · intro rest G hr hrs hrg hG; exact (hT rest hr hrs hrg).2.2.2.2.2.2 G hG

/-! ### The size-bounded invariant from legs -/

/-- Lane 161's `R n` from legs of every printable tree up to size `n`: every leg of `R` is the
    matching leg of `Legs` at a looser fuel bound. -/
theorem R_of_legs : ∀ (n : Nat),
    (∀ (e : SExpr), groesse e ≤ n → gut e = true → Legs e) → R n := by
  intro n H
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e rest F hs hg hr hrs hrg hF
    exact (H e hs hg).2.2.2.2.2.2.2 rest F hr hrs hrg hF
  · intro e rest F hs hg hr hrs hrg hF
    exact (H e hs hg).2.2.2.2.2.2.1 rest F hr hrs hrg (by omega)
  · intro e rest F hs hg hr hrs hrg hF
    exact (H e hs hg).2.2.2.2.2.1 rest F hr hrs hrg (by omega)
  · intro e rest F hs hg hr hrs hrg hF
    exact (H e hs hg).2.2.2.2.1 rest F hr hrs hrg (by omega)
  · intro e rest F hs hg hr hrs hrg hF
    exact (H e hs hg).2.2.2.1 rest F hr hrs hrg (by omega)
  · intro e rest F hs hg hr hrs hrg hF
    exact (H e hs hg).2.2.1 rest F hr hrs hrg (by omega)
  · intro e rest F hs hg hr hrs hrg hF
    exact (H e hs hg).2.1 rest F hrs hrg (by omega)
  · intro e rest F hs hg hpf hrs hrg hF
    exact (H e hs hg).1 rest F hpf hrs hrg hF

/-! ### `sizeof`/`lenof` over arbitrary places -/

theorem prim_emb1_gen : ∀ (n : Nat) (Rn : R n) (w : String) (x : SExpr)
    (rest : List Token) (F : Nat),
    (w = "sizeof" ∨ w = "lenof") → groesse x ≤ n → gutPlatz x = true →
    (!istTypWortVar x) = true → ruhigSuff rest = true →
    12 * (groesse (.built w [x]) + 1) + groesse (.built w [x]) + 1 ≤ F →
    parsePrimary F (druckToks (.built w [x]) ++ rest) =
      .ok (.built w [x], rest) := by
  intro n Rn w x rest F hw hs hp htw hrs hF
  have hF1 : 1 ≤ F := by omega
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  have hF2 : 1 ≤ F' := by omega
  obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
  have hFp : 12 * (groesse x + 1) + groesse x ≤ F'' := by
    simp only [groesse, groesseListe] at hF ⊢
    omega
  have hO := ort_platz_all n Rn x ([.zeichen ")"] ++ rest) F'' hs hp (hrs_paren rest) hFp
  obtain rfl | rfl := hw
  · simp only [druckToks, args_einzeln, List.cons_append, parsePrimary] at ⊢
    simp only [parseEingebaut_ein] at ⊢
    simp only [List.append_assoc, List.cons_append, List.nil_append] at ⊢ hO
    simp only [hO] at ⊢
    exact eingebaut_ein_ok "sizeof" x rest hp htw
  · simp only [druckToks, args_einzeln, List.cons_append, parsePrimary] at ⊢
    simp only [parseEingebaut_ein] at ⊢
    simp only [List.append_assoc, List.cons_append, List.nil_append] at ⊢ hO
    simp only [hO] at ⊢
    exact eingebaut_ein_ok "lenof" x rest hp htw

/-! ### The printable builtins -/

/-- What `gut` admits under `built`: `sizeof`/`lenof` over one non-type-word place, `aligned` over
    two printable trees. -/
theorem gut_built_faelle : ∀ (w : String) (xs : List SExpr), gut (.built w xs) = true →
    (∃ x, (w = "sizeof" ∨ w = "lenof") ∧ xs = [x] ∧ gutPlatz x = true ∧
      (!istTypWortVar x) = true) ∨
    (∃ a b, w = "aligned" ∧ xs = [a, b] ∧ gut a = true ∧ gut b = true) := by
  intro w xs h
  unfold gut at h
  split at h
  all_goals first
    | (simp at h; done)
    | skip
  all_goals
    rename_i heq
    first
      | (injection heq with h1 h2; subst h1; subst h2
         simp only [Bool.and_eq_true] at h
         first
           | exact Or.inl ⟨_, Or.inl rfl, rfl, h.1, h.2⟩
           | exact Or.inl ⟨_, Or.inr rfl, rfl, h.1, h.2⟩
           | exact Or.inr ⟨_, _, rfl, rfl, h.1, h.2⟩)
      | (injection heq)

/-! ### The joint size induction -/

theorem legs_gut_n : ∀ (n : Nat) (e : SExpr), groesse e ≤ n → gut e = true → Legs e := by
  intro n
  induction n with
  | zero =>
    intro e hs _
    have := groesse_pos e
    omega
  | succ n ih =>
    have Rn : R n := R_of_legs n ih
    intro e hs hg
    -- Places (`field`/`index`/`arrow`): the primary leg is lane 161's `prim_platz`, the print
    -- starts with the head identifier.
    have platz : gutPlatz e = true → Legs e := by
      intro hp
      obtain ⟨a, suff, rfl, _, _, _⟩ := zerlege (n + 1) e hs hp
      have hd : druckToks (applySuff (.variable a) suff) = [.ident a] ++ suffToks suff := by
        rw [druckToks_applySuff]; rfl
      apply identTurm a _ hd
      intro rest' G hrs _ hG
      exact prim_platz n Rn _ rest' G hs hp hrs hG
    cases e with
    | lit m => exact legsKern _ rfl
    | float s => exact legsKern _ rfl
    | tru => exact legsKern _ rfl
    | fls => exact legsKern _ rfl
    | «variable» s => exact legsKern _ hg
    | field x f => exact platz hg
    | index x i => exact platz hg
    | arrow x f => exact platz hg
    | un o x =>
      simp only [gut, Bool.and_eq_true] at hg
      have hx : groesse x ≤ n := by simp only [groesse] at hs; omega
      exact unLegs o x hg.1 (ih x hx hg.2)
    | bin o l r =>
      simp only [gut, Bool.and_eq_true] at hg
      have hl : groesse l ≤ n := by simp only [groesse] at hs; omega
      have hr : groesse r ≤ n := by simp only [groesse] at hs; omega
      exact binLegs o l r hg.1.1 (ih l hl hg.1.2) (ih r hr hg.2)
    | call f xs =>
      have hd : druckToks (.call f xs) = [.ident f] ++
          ([.zeichen "("] ++ druckToksListe xs ++ [.zeichen ")"]) := by
        simp [druckToks]
      apply identTurm f _ hd
      intro rest' G hrs _ hG
      exact prim_ruf n Rn f xs rest' G hs hg hrs hG
    | fnref p => exact fnwertLegs p
    | built w xs =>
      rcases gut_built_faelle w xs hg with ⟨x, hw, rfl, hp, htw⟩ | ⟨a, b, rfl, rfl, ha, hb⟩
      · have hx : groesse x ≤ n := by
          simp only [groesse, groesseListe] at hs; omega
        apply embTower w [x]
        intro rest' G hrs _ hG
        exact prim_emb1_gen n Rn w x rest' G hw hx hp htw hrs hG
      · have ha' : groesse a ≤ n := by
          simp only [groesse, groesseListe] at hs; omega
        have hb' : groesse b ≤ n := by
          simp only [groesse, groesseListe] at hs; omega
        exact alignedLegs a b (ih a ha' ha) (ih b hb' hb)
    | old x =>
      have hd : druckToks (.old x) = [.wort "old"] ++
          (([.zeichen "("] ++ druckToks x) ++ [.zeichen ")"]) := by
        simp [druckToks]
      apply wortTurm _ _ hd
      intro rest' G hrs _ hG
      exact prim_alt n Rn x rest' G hs hg hrs hG
    | res => exact ergebnisLegs
    | why g f =>
      simp only [gut, Bool.and_eq_true] at hg
      exact grundLegs g f hg.1.1.1 hg.1.1.2 hg.1.2 hg.2
    | ext k ns xs => simp [gut] at hg

/-- **Every printable expression has all eight round-trip legs.** -/
theorem legs_gut : ∀ (e : SExpr), gut e = true → Legs e :=
  fun e hg => legs_gut_n (groesse e) e (Nat.le_refl _) hg

/-- **L2a: every printable expression parses back from its tokens** (with `brennstoff` fuel). -/
theorem parse_druck_gut : ∀ (e : SExpr), gut e = true →
    parseOr (brennstoff e) (druckToks e ++ [.ende]) = .ok (e, [.ende]) := by
  intro e hg
  have hF : 12 * (groesse e + 1) + groesse e + 8 ≤ brennstoff e := by
    simp [brennstoff]
  exact (legs_gut e hg).2.2.2.2.2.2.2 [.ende] (brennstoff e) rfl rfl rfl hF

/-! ### Witnesses -/

/-- A tree no earlier level reaches: a comparison over a bit operator over a call with a place
    argument whose index payload is a sum, under `!`, in an `||` -- every new step at once. -/
def zeugeTief : SExpr :=
  .bin "||"
    (.un "!" (.bin "==" (.bin "&" (.call "lies" [.index (.variable "k") (.bin "+" (.variable "i")
      (.lit 1))]) (.lit 255)) (.old (.field (.variable "k") "stand"))))
    (.bin "&&" (.built "sizeof" [.index (.variable "k") (.call "f" [])]) (.fnref "g"))

theorem zeugeTief_gut : gut zeugeTief = true := by decide

theorem parse_druck_gut_zeuge :
    parseOr (brennstoff zeugeTief) (druckToks zeugeTief ++ [.ende]) = .ok (zeugeTief, [.ende]) :=
  parse_druck_gut zeugeTief zeugeTief_gut

end Gabbro.Grammatik.Parser

#print axioms Gabbro.Grammatik.Parser.legs_gut
#print axioms Gabbro.Grammatik.Parser.parse_druck_gut
#print axioms Gabbro.Grammatik.Parser.parse_druck_gut_zeuge
