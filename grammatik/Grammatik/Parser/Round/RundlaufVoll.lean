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
public import Grammatik.Parser.Round.RundlaufVolla
public import Grammatik.Parser.Round.Rundlauf4.Teil2
public import Grammatik.Parser.Round.RundlaufLex.Teil2
@[expose] public section


namespace Gabbro.Grammatik.Parser
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
        simp only [druckToks, un_ne_klammer _ ho, Bool.false_eq_true, ↓reduceIte, hat, List.cons_append,
  List.nil_append]
      have hP' := Hx.1 rest G' hpf hrs hrg (by omega)
      simp only [hd, List.append_assoc] at ⊢
      exact bang_arm_gen _ _ _ _ _ ho hP' (atom_bed x rest)
    | false =>
      have hd : druckToks (.un o x) = [.zeichen o] ++
          (([.zeichen "("] ++ druckToks x) ++ [.zeichen ")"]) := by
        simp only [druckToks, un_ne_klammer _ ho, Bool.false_eq_true, ↓reduceIte, hat, List.cons_append,
  List.nil_append]
      have hF2 : 1 ≤ G' := by omega
      obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
      have hO' := Hx.2.2.2.2.2.2.2 _ G'' (hr_paren rest) (hrs_paren rest) (hrg_paren rest)
        (by omega)
      have hPar := paren_arm _ _ _ _ hO'
      have hBang := bang_arm_gen _ _ _ _ _ ho hPar (Or.inr (nonatom_bed x hat))
      simp only [hd, List.append_assoc] at ⊢
      exact hBang
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro rest G hpf; simp only [primFrei, Bool.false_eq_true] at hpf
  · exact hU
  · intro rest G hr hrs hrg hG; exact (hT rest hr hrs hrg).2.1 G hG
  · intro rest G hr hrs hrg hG; exact (hT rest hr hrs hrg).2.2.1 G hG
  · intro rest G hr hrs hrg hG; exact (hT rest hr hrs hrg).2.2.2.1 G hG
  · intro rest G hr hrs hrg hG; exact (hT rest hr hrs hrg).2.2.2.2.1 G hG
  · intro rest G hr hrs hrg hG; exact (hT rest hr hrs hrg).2.2.2.2.2.1 G hG
  · intro rest G hr hrs hrg hG; exact (hT rest hr hrs hrg).2.2.2.2.2.2 G hG

/-- `-(n)`, the negation of a numeral: the parenthesised arm of `-` (`negklammer_arm`) over the numeral's legs. -/
theorem negLitLegs (n : Nat) (Hx : Legs (.lit n)) : Legs (.un "-()" (.lit n)) := by
  have hs0 : strEq "-()" "-()" = true := by decide
  have hd : druckToks (.un "-()" (.lit n)) = [.zeichen "-", .zeichen "("] ++ (druckToks (.lit n) ++ [.zeichen ")"]) := by
    simp only [druckToks, hs0, ite_true, List.append_assoc]
  have hU : ∀ (rest : List Token) (G : Nat), ruhigSuff rest = true → ruhigGleit rest = true →
      12 * (groesse (.un "-()" (.lit n)) + 1) + groesse (.un "-()" (.lit n)) + 2 ≤ G →
      parseUnary G (druckToks (.un "-()" (.lit n)) ++ rest) = .ok (.un "-()" (.lit n), rest) := by
    intro rest G hrs hrg hG
    have hsize : groesse (.un "-()" (.lit n)) = groesse (.lit n) + 1 := rfl
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    have hO' := Hx.2.2.2.2.2.2.2 _ G'' (hr_paren rest) (hrs_paren rest) (hrg_paren rest) (by omega)
    have hPar := paren_arm _ _ _ _ hO'
    have hN := negklammer_arm _ _ _ n hPar
    simp only [hd, List.append_assoc] at ⊢
    simpa only [List.append_assoc] using hN
  have hT : ∀ (rest : List Token), ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true → _ :=
    fun rest hr hrs hrg => tower_up (.un "-()" (.lit n)) rest hr (fun G hG => hU rest G hrs hrg hG)
  refine ⟨?_, hU, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro rest G hpf; simp only [primFrei, Bool.false_eq_true] at hpf
  · intro rest G hr hrs hrg hG; exact (hT rest hr hrs hrg).1 G hG
  · intro rest G hr hrs hrg hG; exact (hT rest hr hrs hrg).2.1 G hG
  · intro rest G hr hrs hrg hG; exact (hT rest hr hrs hrg).2.2.1 G hG
  · intro rest G hr hrs hrg hG; exact (hT rest hr hrs hrg).2.2.2.1 G hG
  · intro rest G hr hrs hrg hG; exact (hT rest hr hrs hrg).2.2.2.2.1 G hG
  · intro rest G hr hrs hrg hG; exact (hT rest hr hrs hrg).2.2.2.2.2 G hG

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
  · simp only [druckToks, strEq_eq, String.reduceEq, ↓reduceIte,
      args_einzeln, List.cons_append, parsePrimary] at ⊢
    simp only [parseEingebaut_ein] at ⊢
    simp only [List.append_assoc, List.cons_append, List.nil_append] at ⊢ hO
    simp only [hO] at ⊢
    exact eingebaut_ein_ok "sizeof" x rest hp htw
  · simp only [druckToks, strEq_eq, String.reduceEq, ↓reduceIte,
      args_einzeln, List.cons_append, parsePrimary] at ⊢
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
    | (simp only [Bool.false_eq_true] at h; done)
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

/-! ### Witnesses -/

/-- A tree no earlier level reaches: a comparison over a bit operator over a call with a place
    argument whose index payload is a sum, under `!`, in an `||` -- every new step at once. -/
def zeugeTief : SExpr :=
  .bin "||"
    (.un "!" (.bin "==" (.bin "&" (.call "lies" [.index (.variable "k") (.bin "+" (.variable "i")
      (.lit 1))]) (.lit 255)) (.old (.field (.variable "k") "stand"))))
    (.bin "&&" (.built "sizeof" [.index (.variable "k") (.call "f" [])]) (.fnref "g"))

theorem zeugeTief_gut : gut zeugeTief = true := by decide

end Gabbro.Grammatik.Parser

