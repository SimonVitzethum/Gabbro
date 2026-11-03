module

public import Grammatik.Speichermodell.Maschine.SperreSemA.Teil1

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

/-- A pending cleanup checks exactly the next release invariant. Its
    saved answer and read-world snapshot pass to the next state unchanged. -/
theorem semHA_aufraeumen_freigabe (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (A : AUmwelt D)
    (passes : Nat) (calls : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (a : (ErgVal D V.erg ⊕ Fin V.gruende) × World D)
    (L : D.Lock) (remaining : List D.Lock) (σ : World D) (ρ : Env D Γ) :
    semHA S O U A passes calls (.aufraeumen (l := l) a (L :: remaining)) σ ρ =
      if S.inv L σ.speicher then
        semHA S O U A passes calls (.aufraeumen (l := l) a remaining) (σ.gibt L) ρ
      else .logik .schleife := by
  cases hL : S.inv L σ.speicher <;>
    simp only [semHA, weiterHA, scopesInvH, List.all_cons, hL, Bool.false_and,
      Bool.true_and, Bool.false_eq_true, if_false, if_true, List.foldl_cons]

/-- A failed pending cleanup remains a logic failure, rather than a named
    external stop. Reachable replay must establish its release checks. -/
theorem semHA_aufraeumen_falsch (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (A : AUmwelt D)
    (passes : Nat) (calls : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (a : (ErgVal D V.erg ⊕ Fin V.gruende) × World D)
    (remaining : List D.Lock) (σ : World D) (ρ : Env D Γ)
    (hcheck : scopesInvH S remaining σ = false) :
    semHA S O U A passes calls (.aufraeumen (l := l) a remaining) σ ρ = .logik .schleife := by
  simp only [semHA, weiterHA, hcheck, Bool.false_eq_true, if_false]

/-- A failed cleanup invariant is a logic failure in every source-head shape. -/
theorem semHA_scopedWert_falsch (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (A : AUmwelt D) (passes : Nat)
    (calls : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (r : GRest D V l Γ Λ) (e : ErgExpr D Γ Λ V.erg) (R : RueckRessourcen D V Λ)
    (h : r.scopedWert = some (e, R)) (σ : World D) (ρ : Env D Γ)
    (hcheck : scopesInvH S R.scopes (leseA A σ Λ e.orte) = false) :
    semHA S O U A passes calls r σ ρ = .logik .schleife := by
  obtain h | ⟨rest, h⟩ | ⟨Λ', rest, k, h⟩ := GRest.scopedWert_faelle h <;> subst r
  · simp only [semHA, execEndHA, hcheck, Bool.false_eq_true, if_false, zErgG]
  · rw [semHA_ende_cons]
    simp only [execStmtHA, hcheck, Bool.false_eq_true, if_false]
    exact weiterHA_logik S O U A passes calls _ _
  · rw [semHA_dann_cons]
    simp only [execStmtHA, hcheck, Bool.false_eq_true, if_false]
    exact weiterHA_logik S O U A passes calls _ _

/-- The reason channel checks exactly the same cleanup obligations. -/
theorem semHA_scopedGrund_falsch (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (A : AUmwelt D) (passes : Nat)
    (calls : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (r : GRest D V l Γ Λ) (grund : Fin V.gruende) (R : RueckRessourcen D V Λ)
    (h : r.scopedGrund = some (grund, R)) (σ : World D) (ρ : Env D Γ)
    (hcheck : scopesInvH S R.scopes σ = false) :
    semHA S O U A passes calls r σ ρ = .logik .schleife := by
  obtain h | ⟨rest, h⟩ | ⟨Λ', rest, k, h⟩ := GRest.scopedGrund_faelle h <;> subst r
  · simp only [semHA, execEndHA, hcheck, Bool.false_eq_true, if_false, zErgG]
  · rw [semHA_ende_cons]
    simp only [execStmtHA, hcheck, Bool.false_eq_true, if_false]
    exact weiterHA_logik S O U A passes calls _ _
  · rw [semHA_dann_cons]
    simp only [execStmtHA, hcheck, Bool.false_eq_true, if_false]
    exact weiterHA_logik S O U A passes calls _ _

end Gabbro.Grammatik
