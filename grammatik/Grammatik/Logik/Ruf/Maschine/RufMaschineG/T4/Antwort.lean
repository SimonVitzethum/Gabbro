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
      have h := rufFadenPasstG_behalte z false (D.params z.kopf.f)
        (vertragVon D z.kopf.f).ende z.kopf.rho (.zurueckgekehrt ⟨a, vor⟩) σ.spur hz
      rw [hst] at h
      exact h
  | cons c st =>
      obtain ⟨r, hr⟩ : ∃ r, antwortRestG z.kopf.f a c.rest = some r := by
        cases hr : antwortRestG z.kopf.f a c.rest with
        | none => simp [rufAntwortG, hst, hr] at ha
        | some r => exact ⟨r, rfl⟩
      cases a with
      | inl v =>
          simp [rufAntwortG, hst, hr] at ha
          subst z'
          exact rufPopG_passt z c st hst ⟨c.f, c.rho, c.s0, r⟩ rfl z.kopf.f z.kopf.rho v z.kopf.s0 σ rfl
            σ.spur hz
      | inr grund =>
          simp [rufAntwortG, hst, hr] at ha
          subst z'
          exact rufPopGrundG_passt z c st hst ⟨c.f, c.rho, c.s0, r⟩ rfl z.kopf.f z.kopf.rho grund z.kopf.s0 σ
            rfl σ.spur hz

end Gabbro.Grammatik
