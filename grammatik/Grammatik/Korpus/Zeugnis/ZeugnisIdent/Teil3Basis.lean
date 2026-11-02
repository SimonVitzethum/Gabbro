module

public import Grammatik.Korpus.Zeugnis.Zeugnis
public import Grammatik.Korpus.Referenz.ReferenzB
public import Grammatik.Korpus.Zeugnis.ZeugnisIdent.Teil2

@[expose] public section

namespace Gabbro.Grammatik

/-- Converse: elaboration implies certificate validity -- an elaborated
    print is exactly what the range table recomputes. Combined with the
    existing `zeugnis_sound`, `elabInt c = some e` yields both the
    `GueltigAbleitung` (here) and the judgment (there). Proved by
    induction over the certificate; every premise is used (sub-equations
    feed the IHs, side hypotheses discharge the table guards). -/
theorem elab_valid {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (c : CertExpr D) {lo hi : Int} {e : Expr D Γ Λ (.int lo hi)}
    (h : elabInt c = some ⟨.int lo hi, e⟩) :
    GueltigAbleitung D Γ Λ c lo hi := by
  induction c generalizing lo hi e with
  | lit n =>
    simp only [elabInt, Option.some.injEq, Sigma.mk.injEq, Ty.int.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, -⟩ := h
    rfl
  | var k =>
    simp only [elabInt] at h
    cases hvar : varOfAll Γ k with
    | none => simp only [hvar, reduceCtorEq] at h
    | some w =>
      obtain ⟨τw, xw⟩ := w
      simp only [hvar, Option.some.injEq, Sigma.mk.injEq] at h
      obtain ⟨hτw, -⟩ := h
      cases hτw
      exact varOfAll_ctxTyp hvar
  | glob g =>
    by_cases hc : gdarf D g Λ
    · have h' : elabInt (D := D) (Γ := Γ) (Λ := Λ) (.glob g) =
          some ⟨D.gtyp g, .glob g hc⟩ := by
        simp only [elabInt, dif_pos hc]
      rw [h'] at h
      have hg : D.gtyp g = .int lo hi := congrArg Sigma.fst (Option.some.inj h)
      show certRange D Γ Λ (.glob g) = some (lo, hi)
      simp only [certRange, intVonTyp, hg, hc, ↓reduceIte]
    · have h' : elabInt (D := D) (Γ := Γ) (Λ := Λ) (.glob g) = none := by
        simp only [elabInt, dif_neg hc]
      rw [h'] at h
      simp only [reduceCtorEq] at h
  | add a b iha ihb =>
    cases ha1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) a with
    | none => simp only [elabInt, ha1, reduceCtorEq] at h
    | some va =>
      obtain ⟨τa, ea⟩ := va
      cases hb1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) b with
      | none => simp only [elabInt, ha1, hb1, reduceCtorEq] at h
      | some vb =>
        obtain ⟨τb, eb⟩ := vb
        cases τa with
        | int l1 h1 =>
          cases τb with
          | int l2 h2 =>
            simp only [elabInt, ha1, hb1, Option.some.injEq, Sigma.mk.injEq,
              Ty.int.injEq] at h
            obtain ⟨⟨rfl, rfl⟩, -⟩ := h
            have ra : certRange D Γ Λ a = some (l1, h1) := iha ha1
            have rb : certRange D Γ Λ b = some (l2, h2) := ihb hb1
            show certRange D Γ Λ (.add a b) = some (l1 + l2, h1 + h2)
            simp only [certRange, ra, rb]
          | bool | opt | sum | why | never | fl | fnptr | ptr | ref | arr | str | prod =>
            simp only [elabInt, ha1, hb1, reduceCtorEq] at h
        | bool | opt | sum | why | never | fl | fnptr | ptr | ref | arr | str | prod =>
          simp only [elabInt, ha1, hb1, reduceCtorEq] at h
  | sub a b iha ihb =>
    cases ha1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) a with
    | none => simp only [elabInt, ha1, reduceCtorEq] at h
    | some va =>
      obtain ⟨τa, ea⟩ := va
      cases hb1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) b with
      | none => simp only [elabInt, ha1, hb1, reduceCtorEq] at h
      | some vb =>
        obtain ⟨τb, eb⟩ := vb
        cases τa with
        | int l1 h1 =>
          cases τb with
          | int l2 h2 =>
            simp only [elabInt, ha1, hb1, Option.some.injEq, Sigma.mk.injEq,
              Ty.int.injEq] at h
            obtain ⟨⟨rfl, rfl⟩, -⟩ := h
            have ra : certRange D Γ Λ a = some (l1, h1) := iha ha1
            have rb : certRange D Γ Λ b = some (l2, h2) := ihb hb1
            show certRange D Γ Λ (.sub a b) = some (l1 - h2, h1 - l2)
            simp only [certRange, ra, rb]
          | bool | opt | sum | why | never | fl | fnptr | ptr | ref | arr | str | prod =>
            simp only [elabInt, ha1, hb1, reduceCtorEq] at h
        | bool | opt | sum | why | never | fl | fnptr | ptr | ref | arr | str | prod =>
          simp only [elabInt, ha1, hb1, reduceCtorEq] at h
  | neg a iha =>
    cases ha1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) a with
    | none => simp only [elabInt, ha1, reduceCtorEq] at h
    | some va =>
      obtain ⟨τa, ea⟩ := va
      cases τa with
      | int l hh =>
        simp only [elabInt, ha1, Option.some.injEq, Sigma.mk.injEq, Ty.int.injEq] at h
        obtain ⟨⟨rfl, rfl⟩, -⟩ := h
        have ra : certRange D Γ Λ a = some (l, hh) := iha ha1
        show certRange D Γ Λ (.neg a) = some (-hh, -l)
        simp only [certRange, ra]
      | bool | opt | sum | why | never | fl | fnptr | ptr | ref | arr | str | prod =>
        simp only [elabInt, ha1, reduceCtorEq] at h
  | mul a b iha ihb =>
    cases ha1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) a with
    | none => simp only [elabInt, ha1, reduceCtorEq] at h
    | some va =>
      obtain ⟨τa, ea⟩ := va
      cases hb1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) b with
      | none => simp only [elabInt, ha1, hb1, reduceCtorEq] at h
      | some vb =>
        obtain ⟨τb, eb⟩ := vb
        cases τa with
        | int l1 h1 =>
          cases τb with
          | int l2 h2 =>
            simp only [elabInt, ha1, hb1, Option.some.injEq, Sigma.mk.injEq,
              Ty.int.injEq] at h
            obtain ⟨⟨rfl, rfl⟩, -⟩ := h
            have ra : certRange D Γ Λ a = some (l1, h1) := iha ha1
            have rb : certRange D Γ Λ b = some (l2, h2) := ihb hb1
            show certRange D Γ Λ (.mul a b) =
              some (imin (imin (l1 * l2) (l1 * h2)) (imin (h1 * l2) (h1 * h2)),
                imax (imax (l1 * l2) (l1 * h2)) (imax (h1 * l2) (h1 * h2)))
            simp only [certRange, ra, rb]
          | bool | opt | sum | why | never | fl | fnptr | ptr | ref | arr | str | prod =>
            simp only [elabInt, ha1, hb1, reduceCtorEq] at h
        | bool | opt | sum | why | never | fl | fnptr | ptr | ref | arr | str | prod =>
          simp only [elabInt, ha1, hb1, reduceCtorEq] at h
  | div a b iha ihb =>
    cases ha1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) a with
    | none => simp only [elabInt, ha1, reduceCtorEq] at h
    | some va =>
      obtain ⟨τa, ea⟩ := va
      cases hb1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) b with
      | none => simp only [elabInt, ha1, hb1, reduceCtorEq] at h
      | some vb =>
        obtain ⟨τb, eb⟩ := vb
        cases τa with
        | int l1 h1 =>
          cases τb with
          | int l2 h2 =>
            simp only [elabInt, ha1, hb1] at h
            by_cases hc : 0 ≤ l1 ∧ 1 ≤ l2
            · simp only [dif_pos hc, Option.some.injEq, Sigma.mk.injEq,
                Ty.int.injEq] at h
              obtain ⟨⟨rfl, rfl⟩, -⟩ := h
              have ra : certRange D Γ Λ a = some (l1, h1) := iha ha1
              have rb : certRange D Γ Λ b = some (l2, h2) := ihb hb1
              show certRange D Γ Λ (.div a b) = some (0, h1)
              simp only [certRange, ra, rb, hc, and_self, ↓reduceIte]
            · simp only [dif_neg hc] at h
              simp only [reduceCtorEq] at h
          | bool | opt | sum | why | never | fl | fnptr | ptr | ref | arr | str | prod =>
            simp only [elabInt, ha1, hb1, reduceCtorEq] at h
        | bool | opt | sum | why | never | fl | fnptr | ptr | ref | arr | str | prod =>
          simp only [elabInt, ha1, hb1, reduceCtorEq] at h
  | rem a b iha ihb =>
    cases ha1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) a with
    | none => simp only [elabInt, ha1, reduceCtorEq] at h
    | some va =>
      obtain ⟨τa, ea⟩ := va
      cases hb1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) b with
      | none => simp only [elabInt, ha1, hb1, reduceCtorEq] at h
      | some vb =>
        obtain ⟨τb, eb⟩ := vb
        cases τa with
        | int l1 h1 =>
          cases τb with
          | int l2 h2 =>
            simp only [elabInt, ha1, hb1] at h
            by_cases hc : 0 ≤ l1 ∧ 1 ≤ l2
            · simp only [dif_pos hc, Option.some.injEq, Sigma.mk.injEq,
                Ty.int.injEq] at h
              obtain ⟨⟨rfl, rfl⟩, -⟩ := h
              have ra : certRange D Γ Λ a = some (l1, h1) := iha ha1
              have rb : certRange D Γ Λ b = some (l2, h2) := ihb hb1
              show certRange D Γ Λ (.rem a b) = some (0, h2 - 1)
              simp only [certRange, ra, rb, hc, and_self, ↓reduceIte]
            · simp only [dif_neg hc] at h
              simp only [reduceCtorEq] at h
          | bool | opt | sum | why | never | fl | fnptr | ptr | ref | arr | str | prod =>
            simp only [elabInt, ha1, hb1, reduceCtorEq] at h
        | bool | opt | sum | why | never | fl | fnptr | ptr | ref | arr | str | prod =>
          simp only [elabInt, ha1, hb1, reduceCtorEq] at h
  | sdiv a b iha ihb =>
    cases ha1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) a with
    | none => simp only [elabInt, ha1, reduceCtorEq] at h
    | some va =>
      obtain ⟨τa, ea⟩ := va
      cases hb1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) b with
      | none => simp only [elabInt, ha1, hb1, reduceCtorEq] at h
      | some vb =>
        obtain ⟨τb, eb⟩ := vb
        cases τa with
        | int l1 h1 =>
          cases τb with
          | int l2 h2 =>
            simp only [elabInt, ha1, hb1] at h
            by_cases hc : 1 ≤ l2 ∨ h2 ≤ -1
            · simp only [dif_pos hc, Option.some.injEq, Sigma.mk.injEq,
                Ty.int.injEq] at h
              obtain ⟨⟨rfl, rfl⟩, -⟩ := h
              have ra : certRange D Γ Λ a = some (l1, h1) := iha ha1
              have rb : certRange D Γ Λ b = some (l2, h2) := ihb hb1
              show certRange D Γ Λ (.sdiv a b) =
                some (-(betragMax l1 h1), betragMax l1 h1)
              simp only [certRange, ra, rb, Int.reduceNeg, hc, ↓reduceIte]
            · simp only [dif_neg hc] at h
              simp only [reduceCtorEq] at h
          | bool | opt | sum | why | never | fl | fnptr | ptr | ref | arr | str | prod =>
            simp only [elabInt, ha1, hb1, reduceCtorEq] at h
        | bool | opt | sum | why | never | fl | fnptr | ptr | ref | arr | str | prod =>
          simp only [elabInt, ha1, hb1, reduceCtorEq] at h
  | srem a b iha ihb =>
    cases ha1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) a with
    | none => simp only [elabInt, ha1, reduceCtorEq] at h
    | some va =>
      obtain ⟨τa, ea⟩ := va
      cases hb1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) b with
      | none => simp only [elabInt, ha1, hb1, reduceCtorEq] at h
      | some vb =>
        obtain ⟨τb, eb⟩ := vb
        cases τa with
        | int l1 h1 =>
          cases τb with
          | int l2 h2 =>
            simp only [elabInt, ha1, hb1] at h
            by_cases hc : 1 ≤ l2 ∨ h2 ≤ -1
            · simp only [dif_pos hc, Option.some.injEq, Sigma.mk.injEq,
                Ty.int.injEq] at h
              obtain ⟨⟨rfl, rfl⟩, -⟩ := h
              have ra : certRange D Γ Λ a = some (l1, h1) := iha ha1
              have rb : certRange D Γ Λ b = some (l2, h2) := ihb hb1
              show certRange D Γ Λ (.srem a b) =
                some (-(betragMax l2 h2 - 1), betragMax l2 h2 - 1)
              simp only [certRange, ra, rb, Int.reduceNeg, hc, ↓reduceIte]
            · simp only [dif_neg hc] at h
              simp only [reduceCtorEq] at h
          | bool | opt | sum | why | never | fl | fnptr | ptr | ref | arr | str | prod =>
            simp only [elabInt, ha1, hb1, reduceCtorEq] at h
        | bool | opt | sum | why | never | fl | fnptr | ptr | ref | arr | str | prod =>
          simp only [elabInt, ha1, hb1, reduceCtorEq] at h
  | band a b iha ihb =>
    cases ha1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) a with
    | none => simp only [elabInt, ha1, reduceCtorEq] at h
    | some va =>
      obtain ⟨τa, ea⟩ := va
      cases hb1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) b with
      | none => simp only [elabInt, ha1, hb1, reduceCtorEq] at h
      | some vb =>
        obtain ⟨τb, eb⟩ := vb
        cases τa with
        | int l1 h1 =>
          cases τb with
          | int l2 h2 =>
            simp only [elabInt, ha1, hb1] at h
            by_cases hc : 0 ≤ l1 ∧ 0 ≤ l2
            · simp only [dif_pos hc, Option.some.injEq, Sigma.mk.injEq,
                Ty.int.injEq] at h
              obtain ⟨⟨rfl, rfl⟩, -⟩ := h
              have ra : certRange D Γ Λ a = some (l1, h1) := iha ha1
              have rb : certRange D Γ Λ b = some (l2, h2) := ihb hb1
              show certRange D Γ Λ (.band a b) = some (0, h1)
              simp only [certRange, ra, rb, hc, and_self, ↓reduceIte]
            · simp only [dif_neg hc] at h
              simp only [reduceCtorEq] at h
          | bool | opt | sum | why | never | fl | fnptr | ptr | ref | arr | str | prod =>
            simp only [elabInt, ha1, hb1, reduceCtorEq] at h
        | bool | opt | sum | why | never | fl | fnptr | ptr | ref | arr | str | prod =>
          simp only [elabInt, ha1, hb1, reduceCtorEq] at h
  | bor w a b iha ihb =>
    cases ha1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) a with
    | none => simp only [elabInt, ha1, reduceCtorEq] at h
    | some va =>
      obtain ⟨τa, ea⟩ := va
      cases hb1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) b with
      | none => simp only [elabInt, ha1, hb1, reduceCtorEq] at h
      | some vb =>
        obtain ⟨τb, eb⟩ := vb
        cases τa with
        | int l1 h1 =>
          cases τb with
          | int l2 h2 =>
            simp only [elabInt, ha1, hb1] at h
            by_cases hc : 0 ≤ l1 ∧ 0 ≤ l2 ∧ h1 < 2 ^ w ∧ h2 < 2 ^ w
            · simp only [dif_pos hc, Option.some.injEq, Sigma.mk.injEq,
                Ty.int.injEq] at h
              obtain ⟨⟨rfl, rfl⟩, -⟩ := h
              have ra : certRange D Γ Λ a = some (l1, h1) := iha ha1
              have rb : certRange D Γ Λ b = some (l2, h2) := ihb hb1
              show certRange D Γ Λ (.bor w a b) = some (0, 2 ^ w - 1)
              simp only [certRange, ra, rb, hc, and_self, ↓reduceIte]
            · simp only [dif_neg hc] at h
              simp only [reduceCtorEq] at h
          | bool | opt | sum | why | never | fl | fnptr | ptr | ref | arr | str | prod =>
            simp only [elabInt, ha1, hb1, reduceCtorEq] at h
        | bool | opt | sum | why | never | fl | fnptr | ptr | ref | arr | str | prod =>
          simp only [elabInt, ha1, hb1, reduceCtorEq] at h
  | bxor w a b iha ihb =>
    cases ha1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) a with
    | none => simp only [elabInt, ha1, reduceCtorEq] at h
    | some va =>
      obtain ⟨τa, ea⟩ := va
      cases hb1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) b with
      | none => simp only [elabInt, ha1, hb1, reduceCtorEq] at h
      | some vb =>
        obtain ⟨τb, eb⟩ := vb
        cases τa with
        | int l1 h1 =>
          cases τb with
          | int l2 h2 =>
            simp only [elabInt, ha1, hb1] at h
            by_cases hc : 0 ≤ l1 ∧ 0 ≤ l2 ∧ h1 < 2 ^ w ∧ h2 < 2 ^ w
            · simp only [dif_pos hc, Option.some.injEq, Sigma.mk.injEq,
                Ty.int.injEq] at h
              obtain ⟨⟨rfl, rfl⟩, -⟩ := h
              have ra : certRange D Γ Λ a = some (l1, h1) := iha ha1
              have rb : certRange D Γ Λ b = some (l2, h2) := ihb hb1
              show certRange D Γ Λ (.bxor w a b) = some (0, 2 ^ w - 1)
              simp only [certRange, ra, rb, hc, and_self, ↓reduceIte]
            · simp only [dif_neg hc] at h
              simp only [reduceCtorEq] at h
          | bool | opt | sum | why | never | fl | fnptr | ptr | ref | arr | str | prod =>
            simp only [elabInt, ha1, hb1, reduceCtorEq] at h
        | bool | opt | sum | why | never | fl | fnptr | ptr | ref | arr | str | prod =>
          simp only [elabInt, ha1, hb1, reduceCtorEq] at h
  | shl w a b iha ihb =>
    cases ha1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) a with
    | none => simp only [elabInt, ha1, reduceCtorEq] at h
    | some va =>
      obtain ⟨τa, ea⟩ := va
      cases hb1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) b with
      | none => simp only [elabInt, ha1, hb1, reduceCtorEq] at h
      | some vb =>
        obtain ⟨τb, eb⟩ := vb
        cases τa with
        | int l1 h1 =>
          cases τb with
          | int l2 h2 =>
            simp only [elabInt, ha1, hb1] at h
            by_cases hc : 0 ≤ l1 ∧ 0 ≤ l2 ∧ h1 < 2 ^ w ∧ h2 < (w : Int)
            · simp only [dif_pos hc, Option.some.injEq, Sigma.mk.injEq,
                Ty.int.injEq] at h
              obtain ⟨⟨rfl, rfl⟩, -⟩ := h
              have ra : certRange D Γ Λ a = some (l1, h1) := iha ha1
              have rb : certRange D Γ Λ b = some (l2, h2) := ihb hb1
              show certRange D Γ Λ (.shl w a b) = some (0, h1 * 2 ^ h2.toNat)
              simp only [certRange, ra, rb, hc, and_self, ↓reduceIte]
            · simp only [dif_neg hc] at h
              simp only [reduceCtorEq] at h
          | bool | opt | sum | why | never | fl | fnptr | ptr | ref | arr | str | prod =>
            simp only [elabInt, ha1, hb1, reduceCtorEq] at h
        | bool | opt | sum | why | never | fl | fnptr | ptr | ref | arr | str | prod =>
          simp only [elabInt, ha1, hb1, reduceCtorEq] at h
  | shr w a b iha ihb =>
    cases ha1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) a with
    | none => simp only [elabInt, ha1, reduceCtorEq] at h
    | some va =>
      obtain ⟨τa, ea⟩ := va
      cases hb1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) b with
      | none => simp only [elabInt, ha1, hb1, reduceCtorEq] at h
      | some vb =>
        obtain ⟨τb, eb⟩ := vb
        cases τa with
        | int l1 h1 =>
          cases τb with
          | int l2 h2 =>
            simp only [elabInt, ha1, hb1] at h
            by_cases hc : 0 ≤ l1 ∧ 0 ≤ l2 ∧ h1 < 2 ^ w ∧ h2 < (w : Int)
            · simp only [dif_pos hc, Option.some.injEq, Sigma.mk.injEq,
                Ty.int.injEq] at h
              obtain ⟨⟨rfl, rfl⟩, -⟩ := h
              have ra : certRange D Γ Λ a = some (l1, h1) := iha ha1
              have rb : certRange D Γ Λ b = some (l2, h2) := ihb hb1
              show certRange D Γ Λ (.shr w a b) = some (0, h1)
              simp only [certRange, ra, rb, hc, and_self, ↓reduceIte]
            · simp only [dif_neg hc] at h
              simp only [reduceCtorEq] at h
          | bool | opt | sum | why | never | fl | fnptr | ptr | ref | arr | str | prod =>
            simp only [elabInt, ha1, hb1, reduceCtorEq] at h
        | bool | opt | sum | why | never | fl | fnptr | ptr | ref | arr | str | prod =>
          simp only [elabInt, ha1, hb1, reduceCtorEq] at h
  | wide lo' hi' a iha =>
    cases ha1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) a with
    | none => simp only [elabInt, ha1, reduceCtorEq] at h
    | some va =>
      obtain ⟨τa, ea⟩ := va
      cases τa with
      | int l hh =>
        simp only [elabInt, ha1] at h
        by_cases hc : lo' ≤ l ∧ hh ≤ hi'
        · simp only [dif_pos hc, Option.some.injEq, Sigma.mk.injEq,
            Ty.int.injEq] at h
          obtain ⟨⟨rfl, rfl⟩, -⟩ := h
          have ra : certRange D Γ Λ a = some (l, hh) := iha ha1
          show certRange D Γ Λ (.wide lo' hi' a) = some (lo', hi')
          simp only [certRange, ra, hc, and_self, ↓reduceIte]
        · simp only [dif_neg hc] at h
          simp only [reduceCtorEq] at h
      | bool | opt | sum | why | never | fl | fnptr | ptr | ref | arr | str | prod =>
        simp only [elabInt, ha1, reduceCtorEq] at h
  | slot t f i ihi =>
    cases hi1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) i with
    | none => simp only [elabInt, hi1, reduceCtorEq] at h
    | some w =>
      obtain ⟨τw, eiw⟩ := w
      cases τw with
      | int l hh =>
        simp only [elabInt, hi1] at h
        by_cases hc : l = 0 ∧ hh = D.count t - 1 ∧ darf D t Λ
        · simp only [dif_pos hc, Option.some.injEq, Sigma.mk.injEq] at h
          obtain ⟨hg, -⟩ := h
          obtain ⟨rfl, rfl, hL⟩ := hc
          have ri : certRange D Γ Λ i = some (0, D.count t - 1) := ihi hi1
          show certRange D Γ Λ (.slot t f i) = some (lo, hi)
          simp only [certRange, ri, intVonTyp, hg, hL, and_self, ↓reduceIte]
        · simp only [dif_neg hc] at h
          simp only [reduceCtorEq] at h
      | bool | opt | sum | why | never | fl | fnptr | ptr | ref | arr | str | prod =>
        simp only [elabInt, hi1, reduceCtorEq] at h


end Gabbro.Grammatik
