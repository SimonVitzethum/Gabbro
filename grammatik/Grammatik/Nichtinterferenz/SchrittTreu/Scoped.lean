module

public import Grammatik.Nichtinterferenz.SchrittTreu.Teil1

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- The shared answer operation agrees with the ghost-free pop, including
    the previously missing root cleanup case. -/
theorem kPop_rufAntwortG (z z' : RufFadenG D) (vor σ : World D)
    (a : ErgVal D (vertragVon D z.kopf.f).erg ⊕ Fin (vertragVon D z.kopf.f).gruende)
    (h : rufAntwortG z vor σ a = some z') :
    (match a with
      | .inl v => kPop (z.stapel.map RufRahmenG.kern) z.kopf.f z.kopf.rho σ v
      | .inr r => kPopGrund (z.stapel.map RufRahmenG.kern) z.kopf.f z.kopf.rho
          σ.spur σ.speicher r) = some (z'.kern, σ.speicher) := by
  obtain ⟨st, kopf, spur, log⟩ := z
  cases st with
  | nil =>
      simp only [rufAntwortG, Option.some.injEq] at h
      subst z'
      cases a <;> rfl
  | cons c st =>
      obtain ⟨cf, crho, cs0, ⟨l, Γ, Λ, ρ, rest⟩⟩ := c
      cases a <;> cases rest <;>
        simp_all [rufAntwortG, antwortRestG, kPop, kPopGrund, kBinde,
          RufFadenG.kern, RufRahmenG.kern, GRest.kern, GRest.wartend]
      all_goals split at h <;>
        simp_all [RufFadenG.kern, RufRahmenG.kern, GRest.kern, GRest.wartend]

/-- The value head computes exactly the source read followed by the
    canonical release fold. No expression is evaluated in the released world. -/
theorem kr_scopedWert (P : Programm D) (O : Orakel D) (passes : Nat)
    (st : List (KRahmen D)) (f : D.Fn) (rho : Env D (D.params f))
    (spur : List (Ereignis D)) (sp : Speicher D) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (ρ : Env D Γ) (r : GRest D (vertragVon D f) l Γ Λ)
    (e : ErgExpr D Γ Λ (vertragVon D f).erg)
    (R : RueckRessourcen D (vertragVon D f) Λ) (h : r.scopedWert = some (e, R)) :
    kr P O passes st f rho spur sp ρ r =
      let σ := (sp.welt spur).lese Λ e.orte
      kLokal st f rho ρ (.aufraeumen ⟨.inl (evalErg σ e σ ρ), σ.ohneSnapshot⟩
        R.scopes) σ.spur sp := by
  obtain h | ⟨rest, h⟩ | ⟨Λ', rest, k, h⟩ := GRest.scopedWert_faelle h <;> subst r <;> rfl

/-- The reason channel has the same release fold and no source read. -/
theorem kr_scopedGrund (P : Programm D) (O : Orakel D) (passes : Nat)
    (st : List (KRahmen D)) (f : D.Fn) (rho : Env D (D.params f))
    (spur : List (Ereignis D)) (sp : Speicher D) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (ρ : Env D Γ) (r : GRest D (vertragVon D f) l Γ Λ)
    (grund : Fin (vertragVon D f).gruende)
    (R : RueckRessourcen D (vertragVon D f) Λ) (h : r.scopedGrund = some (grund, R)) :
    kr P O passes st f rho spur sp ρ r =
      kLokal st f rho ρ (.aufraeumen ⟨.inr grund, (sp.welt spur).ohneSnapshot⟩
        R.scopes) spur sp := by
  obtain h | ⟨rest, h⟩ | ⟨Λ', rest, k, h⟩ := GRest.scopedGrund_faelle h <;> subst r <;> rfl

end Gabbro.Grammatik
