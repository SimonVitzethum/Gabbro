module

public import Grammatik.Korpus.Zeugnis.Zeugnis.T1

@[expose] public section



namespace Gabbro.Grammatik

/-- Soundness: a valid certificate IMPLIES the judgment -- there EXISTS an
    accepted derivation, the `Expr` term the grammar admits. The induction is
    over the certificate; each case hands the recomputed side conditions to
    the corresponding `Expr` constructor. (An `∃`, not the term itself: the
    judgment is the proposition that the derivation exists -- the witness-pair
    shape of S4/V5.) -/
theorem zeugnis_sound {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (c : CertExpr D) (lo hi : Int) (h : GueltigAbleitung D Γ Λ c lo hi) :
    ∃ _ : Expr D Γ Λ (.int lo hi), True := by
  induction c generalizing lo hi with
  | lit n =>
    simp only [GueltigAbleitung, certRange, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Expr.lit n, trivial⟩
  | add a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange D Γ Λ a with
    | none => simp only [ha, reduceCtorEq] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases hb : certRange D Γ Λ b with
      | none => simp only [ha, hb, reduceCtorEq] at h
      | some q =>
        obtain ⟨l2, h2⟩ := q
        simp only [ha, hb, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨ea, _⟩ := iha _ _ ha
        obtain ⟨eb, _⟩ := ihb _ _ hb
        exact ⟨Expr.add ea eb, trivial⟩
  | sub a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange D Γ Λ a with
    | none => simp only [ha, reduceCtorEq] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases hb : certRange D Γ Λ b with
      | none => simp only [ha, hb, reduceCtorEq] at h
      | some q =>
        obtain ⟨l2, h2⟩ := q
        simp only [ha, hb, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨ea, _⟩ := iha _ _ ha
        obtain ⟨eb, _⟩ := ihb _ _ hb
        exact ⟨Expr.sub ea eb, trivial⟩
  | neg a iha =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange D Γ Λ a with
    | none => simp only [ha, reduceCtorEq] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      simp only [ha, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨ea, _⟩ := iha _ _ ha
      exact ⟨Expr.neg ea, trivial⟩
  | mul a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange D Γ Λ a with
    | none => simp only [ha, reduceCtorEq] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases hb : certRange D Γ Λ b with
      | none => simp only [ha, hb, reduceCtorEq] at h
      | some q =>
        obtain ⟨l2, h2⟩ := q
        simp only [ha, hb, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨ea, _⟩ := iha _ _ ha
        obtain ⟨eb, _⟩ := ihb _ _ hb
        exact ⟨Expr.mul ea eb, trivial⟩
  | div a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange D Γ Λ a with
    | none => simp only [ha, reduceCtorEq] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases hb : certRange D Γ Λ b with
      | none => simp only [ha, hb, reduceCtorEq] at h
      | some q =>
        obtain ⟨l2, _⟩ := q
        simp only [ha, hb] at h
        by_cases hc : 0 ≤ l1 ∧ 1 ≤ l2
        · rw [if_pos hc] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ea, _⟩ := iha _ _ ha
          obtain ⟨eb, _⟩ := ihb _ _ hb
          exact ⟨Expr.div hc.1 hc.2 ea eb, trivial⟩
        · simp only [hc, ↓reduceIte, reduceCtorEq] at h
  | rem a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange D Γ Λ a with
    | none => simp only [ha, reduceCtorEq] at h
    | some p =>
      obtain ⟨l1, _⟩ := p
      cases hb : certRange D Γ Λ b with
      | none => simp only [ha, hb, reduceCtorEq] at h
      | some q =>
        obtain ⟨l2, h2⟩ := q
        simp only [ha, hb] at h
        by_cases hc : 0 ≤ l1 ∧ 1 ≤ l2
        · rw [if_pos hc] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ea, _⟩ := iha _ _ ha
          obtain ⟨eb, _⟩ := ihb _ _ hb
          exact ⟨Expr.rem hc.1 hc.2 ea eb, trivial⟩
        · simp only [hc, ↓reduceIte, reduceCtorEq] at h
  | sdiv a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange D Γ Λ a with
    | none => simp only [ha, reduceCtorEq] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases hb : certRange D Γ Λ b with
      | none => simp only [ha, hb, reduceCtorEq] at h
      | some q =>
        obtain ⟨l2, h2⟩ := q
        simp only [ha, hb] at h
        by_cases hc : 1 ≤ l2 ∨ h2 ≤ -1
        · rw [if_pos hc] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ea, _⟩ := iha _ _ ha
          obtain ⟨eb, _⟩ := ihb _ _ hb
          exact ⟨Expr.sdiv hc ea eb, trivial⟩
        · simp only [Int.reduceNeg, hc, ↓reduceIte, reduceCtorEq] at h
  | srem a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange D Γ Λ a with
    | none => simp only [ha, reduceCtorEq] at h
    | some p =>
      obtain ⟨_, _⟩ := p
      cases hb : certRange D Γ Λ b with
      | none => simp only [ha, hb, reduceCtorEq] at h
      | some q =>
        obtain ⟨l2, h2⟩ := q
        simp only [ha, hb] at h
        by_cases hc : 1 ≤ l2 ∨ h2 ≤ -1
        · rw [if_pos hc] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ea, _⟩ := iha _ _ ha
          obtain ⟨eb, _⟩ := ihb _ _ hb
          exact ⟨Expr.srem hc ea eb, trivial⟩
        · simp only [Int.reduceNeg, hc, ↓reduceIte, reduceCtorEq] at h
  | band a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange D Γ Λ a with
    | none => simp only [ha, reduceCtorEq] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases hb : certRange D Γ Λ b with
      | none => simp only [ha, hb, reduceCtorEq] at h
      | some q =>
        obtain ⟨l2, _⟩ := q
        simp only [ha, hb] at h
        by_cases hc : 0 ≤ l1 ∧ 0 ≤ l2
        · rw [if_pos hc] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ea, _⟩ := iha _ _ ha
          obtain ⟨eb, _⟩ := ihb _ _ hb
          exact ⟨Expr.band hc.1 hc.2 ea eb, trivial⟩
        · simp only [hc, ↓reduceIte, reduceCtorEq] at h
  | bor w a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange D Γ Λ a with
    | none => simp only [ha, reduceCtorEq] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases hb : certRange D Γ Λ b with
      | none => simp only [ha, hb, reduceCtorEq] at h
      | some q =>
        obtain ⟨l2, h2⟩ := q
        simp only [ha, hb] at h
        by_cases hc : 0 ≤ l1 ∧ 0 ≤ l2 ∧ h1 < 2 ^ w ∧ h2 < 2 ^ w
        · rw [if_pos hc] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ea, _⟩ := iha _ _ ha
          obtain ⟨eb, _⟩ := ihb _ _ hb
          obtain ⟨h0, h0', hw1, hw2⟩ := hc
          exact ⟨Expr.bor w h0 h0' hw1 hw2 ea eb, trivial⟩
        · simp only [hc, ↓reduceIte, reduceCtorEq] at h
  | bxor w a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange D Γ Λ a with
    | none => simp only [ha, reduceCtorEq] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases hb : certRange D Γ Λ b with
      | none => simp only [ha, hb, reduceCtorEq] at h
      | some q =>
        obtain ⟨l2, h2⟩ := q
        simp only [ha, hb] at h
        by_cases hc : 0 ≤ l1 ∧ 0 ≤ l2 ∧ h1 < 2 ^ w ∧ h2 < 2 ^ w
        · rw [if_pos hc] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ea, _⟩ := iha _ _ ha
          obtain ⟨eb, _⟩ := ihb _ _ hb
          obtain ⟨h0, h0', hw1, hw2⟩ := hc
          exact ⟨Expr.bxor w h0 h0' hw1 hw2 ea eb, trivial⟩
        · simp only [hc, ↓reduceIte, reduceCtorEq] at h
  | shl w a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange D Γ Λ a with
    | none => simp only [ha, reduceCtorEq] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases hb : certRange D Γ Λ b with
      | none => simp only [ha, hb, reduceCtorEq] at h
      | some q =>
        obtain ⟨l2, h2⟩ := q
        simp only [ha, hb] at h
        by_cases hc : 0 ≤ l1 ∧ 0 ≤ l2 ∧ h1 < 2 ^ w ∧ h2 < (w : Int)
        · rw [if_pos hc] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ea, _⟩ := iha _ _ ha
          obtain ⟨eb, _⟩ := ihb _ _ hb
          obtain ⟨hc1, hc2, hcw1, hcw2⟩ := hc
          exact ⟨Expr.shl w hcw1 hcw2 hc1 hc2 ea eb, trivial⟩
        · simp only [hc, ↓reduceIte, reduceCtorEq] at h
  | shr w a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange D Γ Λ a with
    | none => simp only [ha, reduceCtorEq] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases hb : certRange D Γ Λ b with
      | none => simp only [ha, hb, reduceCtorEq] at h
      | some q =>
        obtain ⟨l2, h2⟩ := q
        simp only [ha, hb] at h
        by_cases hc : 0 ≤ l1 ∧ 0 ≤ l2 ∧ h1 < 2 ^ w ∧ h2 < (w : Int)
        · rw [if_pos hc] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ea, _⟩ := iha _ _ ha
          obtain ⟨eb, _⟩ := ihb _ _ hb
          obtain ⟨hc1, hc2, hcw1, hcw2⟩ := hc
          exact ⟨Expr.shr w hcw1 hcw2 hc1 hc2 ea eb, trivial⟩
        · simp only [hc, ↓reduceIte, reduceCtorEq] at h
  | wide lo' hi' a iha =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange D Γ Λ a with
    | none => simp only [ha, reduceCtorEq] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      simp only [ha] at h
      by_cases hc : lo' ≤ l1 ∧ h1 ≤ hi'
      · rw [if_pos hc] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨ea, _⟩ := iha _ _ ha
        exact ⟨Expr.widen hc.1 hc.2 ea, trivial⟩
      · simp only [hc, ↓reduceIte, reduceCtorEq] at h
  | var k =>
    simp only [GueltigAbleitung, certRange] at h
    cases hk : ctxTyp Γ k with
    | none => simp only [hk, reduceCtorEq] at h
    | some p =>
      obtain ⟨lo', hi'⟩ := p
      simp only [hk, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨x, _⟩ := ctxTyp_var Γ k _ _ hk
      exact ⟨Expr.var x, trivial⟩
  | glob g =>
    simp only [GueltigAbleitung, certRange] at h
    cases ht : intVonTyp (D.gtyp g) with
    | none => simp only [ht, reduceCtorEq] at h
    | some p =>
      obtain ⟨lo', hi'⟩ := p
      simp only [ht] at h
      by_cases hc : gdarf D g Λ
      · rw [if_pos hc] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have heq := intVonTyp_eq ht
        exact ⟨heq ▸ Expr.glob g hc, trivial⟩
      · simp only [hc, ↓reduceIte, reduceCtorEq] at h
  | slot t f i ih =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange D Γ Λ i with
    | none =>
      cases ht : intVonTyp (D.typ t f) with
      | none => simp only [ha, ht, reduceCtorEq] at h
      | some _ => simp only [ha, ht, reduceCtorEq] at h
    | some p =>
      obtain ⟨l, h'⟩ := p
      cases ht : intVonTyp (D.typ t f) with
      | none => simp only [ha, ht, reduceCtorEq] at h
      | some q =>
        obtain ⟨lo', hi'⟩ := q
        simp only [ha, ht] at h
        by_cases hc : l = 0 ∧ h' = D.count t - 1 ∧ darf D t Λ
        · rw [if_pos hc] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ei, _⟩ := ih _ _ ha
          have heq := intVonTyp_eq ht
          obtain ⟨hc1, hc2, hc3⟩ := hc
          subst hc1
          subst hc2
          exact ⟨heq ▸ Expr.slot t f ei hc3, trivial⟩
        · simp only [hc, ↓reduceIte, reduceCtorEq] at h


end Gabbro.Grammatik
