/- Part 2 of 4 of `Zeugnis` (split by instrumente/teile/lean-teilen.py; the umbrella `Zeugnis.lean` imports all parts). -/
import Grammatik.Korrespondenz.Zeugnis.Zeugnis.T1

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
    | none => simp [ha] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases hb : certRange D Γ Λ b with
      | none => simp [ha, hb] at h
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
    | none => simp [ha] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases hb : certRange D Γ Λ b with
      | none => simp [ha, hb] at h
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
    | none => simp [ha] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      simp only [ha, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨ea, _⟩ := iha _ _ ha
      exact ⟨Expr.neg ea, trivial⟩
  | mul a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange D Γ Λ a with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases hb : certRange D Γ Λ b with
      | none => simp [ha, hb] at h
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
    | none => simp [ha] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases hb : certRange D Γ Λ b with
      | none => simp [ha, hb] at h
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
        · simp [hc] at h
  | rem a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange D Γ Λ a with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨l1, _⟩ := p
      cases hb : certRange D Γ Λ b with
      | none => simp [ha, hb] at h
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
        · simp [hc] at h
  | sdiv a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange D Γ Λ a with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases hb : certRange D Γ Λ b with
      | none => simp [ha, hb] at h
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
        · simp [hc] at h
  | srem a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange D Γ Λ a with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨_, _⟩ := p
      cases hb : certRange D Γ Λ b with
      | none => simp [ha, hb] at h
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
        · simp [hc] at h
  | band a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange D Γ Λ a with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases hb : certRange D Γ Λ b with
      | none => simp [ha, hb] at h
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
        · simp [hc] at h
  | bor w a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange D Γ Λ a with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases hb : certRange D Γ Λ b with
      | none => simp [ha, hb] at h
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
        · simp [hc] at h
  | bxor w a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange D Γ Λ a with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases hb : certRange D Γ Λ b with
      | none => simp [ha, hb] at h
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
        · simp [hc] at h
  | shl w a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange D Γ Λ a with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases hb : certRange D Γ Λ b with
      | none => simp [ha, hb] at h
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
        · simp [hc] at h
  | shr w a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange D Γ Λ a with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases hb : certRange D Γ Λ b with
      | none => simp [ha, hb] at h
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
        · simp [hc] at h
  | wide lo' hi' a iha =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange D Γ Λ a with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      simp only [ha] at h
      by_cases hc : lo' ≤ l1 ∧ h1 ≤ hi'
      · rw [if_pos hc] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨ea, _⟩ := iha _ _ ha
        exact ⟨Expr.widen hc.1 hc.2 ea, trivial⟩
      · simp [hc] at h
  | var k =>
    simp only [GueltigAbleitung, certRange] at h
    cases hk : ctxTyp Γ k with
    | none => simp [hk] at h
    | some p =>
      obtain ⟨lo', hi'⟩ := p
      simp only [hk, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨x, _⟩ := ctxTyp_var Γ k _ _ hk
      exact ⟨Expr.var x, trivial⟩
  | glob g =>
    simp only [GueltigAbleitung, certRange] at h
    cases ht : intVonTyp (D.gtyp g) with
    | none => simp [ht] at h
    | some p =>
      obtain ⟨lo', hi'⟩ := p
      simp only [ht] at h
      by_cases hc : gdarf D g Λ
      · rw [if_pos hc] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have heq := intVonTyp_eq ht
        exact ⟨heq ▸ Expr.glob g hc, trivial⟩
      · simp [hc] at h
  | slot t f i ih =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange D Γ Λ i with
    | none =>
      cases ht : intVonTyp (D.typ t f) with
      | none => simp [ha, ht] at h
      | some _ => simp [ha, ht] at h
    | some p =>
      obtain ⟨l, h'⟩ := p
      cases ht : intVonTyp (D.typ t f) with
      | none => simp [ha, ht] at h
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
        · simp [hc] at h

/-! ## The test world: one concrete declaration for the decide probes

    `decide` needs closed terms: it evaluates the table, and evaluation
    cannot look through an abstract `D`. So the probes below pin ONE world --
    one guarded global of `0 .. 7`, one guarded table with one int field of
    `0 .. 10` over eleven rows, one lock that guards both, one nullary
    procedure and one unary one. Every probe names this world explicitly;
    nothing about the soundness theorems depends on it. -/

/-- Nullary test signature: no params, no result, no reasons, no rights,
    no marks, no held locks. -/
def TestSig0 : Signatur Unit Unit Unit Empty :=
  ⟨[], none, 0, [], fun _ => false, fun _ => false, [], [], none⟩

/-- Unary test signature: one int param -- for the negative call probe. -/
def TestSig1 : Signatur Unit Unit Unit Empty :=
  ⟨[.int 0 5], none, 0, [], fun _ => false, fun _ => false, [], [], none⟩

/-- A one-glob, one-table, one-lock test world: every access is guarded. -/
def TestD : Deklaration where
  Tab := Unit
  count := fun _ => 11
  Feld := fun _ => Unit
  typ := fun _ _ => .int 0 10
  erlaubt := fun _ _ _ _ => true
  tabNr := fun _ => some ()
  Glob := Unit
  gtyp := fun _ => .int 0 7
  nutzlast := fun _ => []
  atomar := fun _ => true
  geteilt := fun _ => false
  ggeteilt := fun _ => false
  Lock := Unit
  rang := fun _ => 0
  maskiert := fun _ => false
  Marke := Empty
  stufen := fun e => e.elim
  braucht := fun _ => [.inl ()]
  gbraucht := fun _ => [.inl ()]
  eigner := fun _ => []
  Fn := Bool
  sig := fun | false => 0 | true => 1
  sigNr := fun | 0 => TestSig0 | 1 => TestSig1 | _ => TestSig0
  eigner_nie_erzeugt := fun _ _ m _ _ => m.elim
  Inv := Empty
  traeger := fun e => e.elim
  invs := []
  Ax := Empty
  aparams := fun e => e.elim
  aerg := fun e => e.elim
  aschreibt := fun e => e.elim
  agschreibt := fun e => e.elim
  Reg := Empty
  rtyp := fun e => e.elim
  rklasse := fun e => e.elim
  spiegel := fun e => e.elim
  rzusage := fun e => e.elim
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t h => by simp at h
  invarianten_gehalten := fun _ i => i.elim
  ggeteilt_bewacht := fun g h => by simp at h

/-- Procedure contract: no result, holds nothing, produces nothing. -/
def TestV : Vertrag TestD :=
  ⟨fun _ => true, fun _ => true, none, 0, [], [], none⟩

/-- Value contract: returns an int in `1 .. 1`. -/
def TestVw : Vertrag TestD :=
  ⟨fun _ => true, fun _ => true, some (.int 1 1), 0, [], [], none⟩

/-- The nullary call fits the procedure contract at empty resources: no
    rights to check (both write maps are `false`), nothing consumed, and the
    held-lock check is vacuous in both directions over the empty lists. -/
theorem TestHp : RufPasst TestD TestV (TestD.signatur false) [] where
  hw := fun t h => by simp [Deklaration.signatur, TestD, TestSig0, TestSig1] at h
  hg := fun g h => by simp [Deklaration.signatur, TestD, TestSig0, TestSig1] at h
  hk := ⟨[], List.Perm.refl _, List.Sublist.refl _⟩
  hh := RufPasst.hh_von fun L => iff_of_false List.not_mem_nil List.not_mem_nil
  hx := RufPasst.hx_von fun L => iff_of_false List.not_mem_nil List.not_mem_nil

/-- Same fit for the unary callee: `RufPasst` never constrained the params,
    so the same vacuous proofs go through -- and the table still rejects the
    call, on `params = []`. -/
theorem TestHp1 : RufPasst TestD TestV (TestD.signatur true) [] where
  hw := fun t h => by simp [Deklaration.signatur, TestD, TestSig0, TestSig1] at h
  hg := fun g h => by simp [Deklaration.signatur, TestD, TestSig0, TestSig1] at h
  hk := ⟨[], List.Perm.refl _, List.Sublist.refl _⟩
  hh := RufPasst.hh_von fun L => iff_of_false List.not_mem_nil List.not_mem_nil
  hx := RufPasst.hx_von fun L => iff_of_false List.not_mem_nil List.not_mem_nil

/-! ## Witness pairs: acceptance and rejection, both by `decide` -/

/-- `1 + 2` printed as `(3, 3)`: Lean accepts the print. -/
example : GueltigAbleitung TestD [] [] (.add (.lit 1) (.lit 2)) 3 3 := by decide

/-- `5 / 2` printed as `(0, 5)`: nonneg dividend, positive divisor (M102). -/
example : GueltigAbleitung TestD [] [] (.div (.lit 5) (.lit 2)) 0 5 := by decide

/-- `5` widened to `0 .. 10`: a checked `weiter` in the safe direction. -/
example : GueltigAbleitung TestD [] [] (.wide 0 10 (.lit 5)) 0 10 := by decide

/-- MISMATCHED print: `1 + 2` claimed as `(0, 0)` -- provably not valid.
    This is the loud failure: no acceptance proof can be built from it. -/
example : ¬ GueltigAbleitung TestD [] [] (.add (.lit 1) (.lit 2)) 0 0 := by decide

/-- FORGED proof: `5 / 0` -- the divisor range admits zero, so the table
    yields no range at all. -/
example : ¬ GueltigAbleitung TestD [] [] (.div (.lit 5) (.lit 0)) 0 5 := by decide

/-- FORGED widening: `20` claimed in `0 .. 10` -- outside, no certificate. -/
example : ¬ GueltigAbleitung TestD [] [] (.wide 0 10 (.lit 20)) 0 10 := by decide

/-! ### CUT-1 and CUT-2 probes: signed division, bitwise, shifts -/

/-- `7 sdiv 2` printed as `(-7, 7)`: the divisor excludes zero (SG-3, second sentence). -/
example : GueltigAbleitung TestD [] [] (.sdiv (.lit 7) (.lit 2)) (-7) 7 := by decide

/-- FORGED proof: `7 sdiv 0` -- same claim as above, but the divisor admits zero. -/
example : ¬ GueltigAbleitung TestD [] [] (.sdiv (.lit 7) (.lit 0)) (-7) 7 := by decide

/-- `7 srem 2` printed as `(-1, 1)`: the remainder range comes from the DIVISOR. -/
example : GueltigAbleitung TestD [] [] (.srem (.lit 7) (.lit 2)) (-1) 1 := by decide

/-- FORGED proof: `7 srem 0` -- same claim as above, but the divisor admits zero. -/
example : ¬ GueltigAbleitung TestD [] [] (.srem (.lit 7) (.lit 0)) (-1) 1 := by decide

/-- `6 band 3` printed as `(0, 6)`: both operands nonneg (M137). -/
example : GueltigAbleitung TestD [] [] (.band (.lit 6) (.lit 3)) 0 6 := by decide

/-- FORGED proof: a negative operand under `band` -- no range at all. -/
example : ¬ GueltigAbleitung TestD [] [] (.band (.sub (.lit 0) (.lit 1)) (.lit 3)) 0 0 := by decide

/-- `6 bor 3` in width 3 printed as `(0, 7)`: both bounds fit under `2 ^ 3`. -/
example : GueltigAbleitung TestD [] [] (.bor 3 (.lit 6) (.lit 3)) 0 7 := by decide

/-- FORGED proof: width 2 does not hold `6` -- the width side condition fails. -/
example : ¬ GueltigAbleitung TestD [] [] (.bor 2 (.lit 6) (.lit 3)) 0 3 := by decide

/-- `6 bxor 3` in width 3 printed as `(0, 7)`: same width rule as `bor`. -/
example : GueltigAbleitung TestD [] [] (.bxor 3 (.lit 6) (.lit 3)) 0 7 := by decide

/-- FORGED proof: width 2 does not hold `6` under `bxor` either. -/
example : ¬ GueltigAbleitung TestD [] [] (.bxor 2 (.lit 6) (.lit 3)) 0 3 := by decide

/-- `3 shl 2` printed as `(0, 12)`: `3 * 2 ^ 2`, both operands nonneg,
    operand bound `3 < 2^32`, amount `2 < 32` (PLAN-BITS.md section 2). -/
example : GueltigAbleitung TestD [] [] (.shl 32 (.lit 3) (.lit 2)) 0 12 := by decide

/-- FORGED proof: a negative value shifted -- no range at all. -/
example : ¬ GueltigAbleitung TestD [] [] (.shl 32 (.sub (.lit 0) (.lit 1)) (.lit 2)) 0 0 := by decide

/-- FORGED proof: the amount `32` reaches the width -- the C UB row. -/
example : ¬ GueltigAbleitung TestD [] [] (.shl 32 (.lit 3) (.lit 32)) 0 0 := by decide

/-- `12 shr 2` printed as `(0, 12)`: a right shift never widens (M137). -/
example : GueltigAbleitung TestD [] [] (.shr 32 (.lit 12) (.lit 2)) 0 12 := by decide

/-- FORGED proof: a negative value shifted right -- no range at all. -/
example : ¬ GueltigAbleitung TestD [] [] (.shr 32 (.sub (.lit 0) (.lit 1)) (.lit 2)) 0 0 := by decide

/-- FORGED proof: the amount `40` is past the width -- undefined in C. -/
example : ¬ GueltigAbleitung TestD [] [] (.shr 32 (.lit 12) (.lit 40)) 0 0 := by decide

/-! ### CUT-4 probes: variables and carrier accesses -/

/-- Variable `0` in `[3 .. 3]` printed as `(3, 3)`: the context lookup hits. -/
example : GueltigAbleitung TestD [.int 3 3] [] (.var 0) 3 3 := by decide

/-- MISMATCHED print: variable `0` claimed as `(0, 0)` -- the lookup says
    `(3, 3)`, so the claim is provably not valid. -/
example : ¬ GueltigAbleitung TestD [.int 3 3] [] (.var 0) 0 0 := by decide

/-- DANGLING print: variable `5` in a one-entry context -- no lookup, no range. -/
example : ¬ GueltigAbleitung TestD [.int 3 3] [] (.var 5) 3 3 := by decide

/-- MISTYPED print: variable `0` of type `bool` claimed as an int range --
    the lookup says `none` for non-int types. -/
example : ¬ GueltigAbleitung TestD [.bool] [] (.var 0) 0 0 := by decide

/-- The global printed as `(0, 7)`: its declared type, under the held guard. -/
example : GueltigAbleitung TestD [] [Res.held ()] (.glob ()) 0 7 := by decide

/-- FORGED guard: the same global with empty hands -- the guard fails, so the
    table yields no range at all. -/
example : ¬ GueltigAbleitung TestD [] [] (.glob ()) 0 7 := by decide

/-- A variable under arithmetic: `x + 1` with `x : 3 .. 3` is `(4, 4)` --
    reads lift through the closed shapes. -/
example : GueltigAbleitung TestD [.int 3 3] [Res.held ()] (.add (.var 0) (.lit 1)) 4 4 := by decide


end Gabbro.Grammatik
