module

public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T3

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- The answer protocol records one callee return, or keeps a root's entry
    record. Updating the residue never changes the caller's key. -/
theorem rufAntwortG_passt {z z' : RufFadenG D} {vor σ : World D}
    {a : ErgVal D (vertragVon D z.kopf.f).erg ⊕ Fin (vertragVon D z.kopf.f).gruende}
    (hz : RufFadenPasstG z) (ha : rufAntwortG z vor σ a = some z') : RufFadenPasstG z' := by
  cases hst : z.stapel with
  | nil =>
      simp only [rufAntwortG, hst, Option.some.injEq] at ha
      subst z'
      exact rufFadenPasstG_behalte _ _ _ _ _ _ _ hz
  | cons c st =>
      obtain ⟨r, hr⟩ : ∃ r, antwortRestG z.kopf.f a c.rest = some r := by
        cases hr : antwortRestG z.kopf.f a c.rest with
        | none => simp [rufAntwortG, hst, hr] at ha
        | some r => exact ⟨r, rfl⟩
      cases a with
      | inl v =>
          simp [rufAntwortG, hst, hr] at ha
          subst z'
          exact rufPopG_passt z c st hst _ rfl _ _ v _ σ rfl _ hz
      | inr grund =>
          simp [rufAntwortG, hst, hr] at ha
          subst z'
          exact rufPopGrundG_passt z c st hst _ rfl _ _ grund _ σ rfl _ hz

end Gabbro.Grammatik
