module

public import Grammatik.Nichtinterferenz.SchrittTreu.Teil1Basis

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
  cases hst : z.stapel with
  | nil =>
      simp only [rufAntwortG, hst, Option.some.injEq] at h
      subst z'
      cases a <;> rfl
  | cons c st =>
      cases hr : antwortRestG z.kopf.f a c.rest with
      | none => simp [rufAntwortG, hst, hr] at h
      | some result =>
          simp [rufAntwortG, hst, hr] at h
          subst z'
          obtain ⟨cf, crho, cs0, ⟨l, Γ, Λ, ρ, rest⟩⟩ := c
          cases a with
          | inl v =>
            cases rest with
            | wartet body k | wartetSonst _ _ body k =>
              simp only [antwortRestG] at hr
              split at hr
              · rename_i he
                cases hr
                simp [kPop, kBinde, RufFadenG.kern, RufRahmenG.kern,
                  GRest.kern, GRest.wartend, he]
              · contradiction
            | _ =>
              simp only [antwortRestG, Option.some.injEq] at hr
              cases hr
              simp [kPop, RufFadenG.kern, RufRahmenG.kern, GRest.kern, GRest.wartend]
          | inr reason =>
            cases rest with
            | wartetSonst n err body k =>
              simp only [antwortRestG] at hr
              split at hr
              · rename_i hn
                cases hr
                simp [kPopGrund, RufFadenG.kern, RufRahmenG.kern, GRest.kern, hn]
              · contradiction
            | _ => cases hr

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
      kScoped (l := l) st f rho ρ (.inl (evalErg σ e σ ρ)) σ R.scopes := by
  obtain h | ⟨rest, h⟩ | ⟨Λ', rest, k, h⟩ := GRest.scopedWert_faelle h
  · subst r
    rfl
  · subst r
    simp only [kr, kEnde, kEndeCons, GEntfaltbar, Stmt.istBlatt,
      Bool.false_eq_true, ↓reduceIte, kRufEnde]
  · subst r
    simp only [kr, kDann, kDannCons, GEntfaltbar, Stmt.istBlatt,
      Bool.false_eq_true, ↓reduceIte, kRufDann]

/-- The reason channel has the same release fold and no source read. -/
theorem kr_scopedGrund (P : Programm D) (O : Orakel D) (passes : Nat)
    (st : List (KRahmen D)) (f : D.Fn) (rho : Env D (D.params f))
    (spur : List (Ereignis D)) (sp : Speicher D) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (ρ : Env D Γ) (r : GRest D (vertragVon D f) l Γ Λ)
    (grund : Fin (vertragVon D f).gruende)
    (R : RueckRessourcen D (vertragVon D f) Λ) (h : r.scopedGrund = some (grund, R)) :
    kr P O passes st f rho spur sp ρ r =
      kScoped (l := l) st f rho ρ (.inr grund) (sp.welt spur) R.scopes := by
  obtain h | ⟨rest, h⟩ | ⟨Λ', rest, k, h⟩ := GRest.scopedGrund_faelle h
  · subst r
    rfl
  · subst r
    simp only [kr, kEnde, kEndeCons, GEntfaltbar, Stmt.istBlatt,
      Bool.false_eq_true, ↓reduceIte, kRufEnde]
  · subst r
    simp only [kr, kDann, kDannCons, GEntfaltbar, Stmt.istBlatt,
      Bool.false_eq_true, ↓reduceIte, kRufDann]

end Gabbro.Grammatik
