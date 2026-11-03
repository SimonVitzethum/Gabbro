module

public import Grammatik.Nebenlaeufigkeit.Sperren.SperreSem.T4.Teil2

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

/-- A pending cleanup checks exactly the next release invariant. Its
    saved answer and read-world snapshot pass to the next state unchanged. -/
theorem semH_aufraeumen_freigabe (S : SperrInv D) (O : Orakel D) (U : Umwelt D)
    (passes : Nat) (calls : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (a : (ErgVal D V.erg ⊕ Fin V.gruende) × World D)
    (L : D.Lock) (remaining : List D.Lock) (σ : World D) (ρ : Env D Γ) :
    semH S O U passes calls (.aufraeumen (l := l) a (L :: remaining)) σ ρ =
      if S.inv L σ.speicher then
        semH S O U passes calls (.aufraeumen (l := l) a remaining) (σ.gibt L) ρ
      else .logik .schleife := by
  have hmem : (σ.gibt L).speicher = σ.speicher := rfl
  cases hL : S.inv L σ.speicher <;>
    simp only [semH, weiterH, scopesInvH, List.all_cons, hmem, hL, Bool.false_and,
      Bool.true_and, Bool.false_eq_true, ite_false, ite_true, List.foldl_cons]

/-- A failed pending cleanup remains a logic failure, rather than a named
    external stop. Reachable replay must establish its release checks. -/
theorem semH_aufraeumen_falsch (S : SperrInv D) (O : Orakel D) (U : Umwelt D)
    (passes : Nat) (calls : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (a : (ErgVal D V.erg ⊕ Fin V.gruende) × World D)
    (remaining : List D.Lock) (σ : World D) (ρ : Env D Γ)
    (hcheck : scopesInvH S remaining σ = false) :
    semH S O U passes calls (.aufraeumen (l := l) a remaining) σ ρ = .logik .schleife := by
  simp only [semH, weiterH, hcheck, Bool.false_eq_true, ite_false]

/-- A failed cleanup invariant is a logic failure in every source-head shape. -/
theorem semH_scopedWert_falsch (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (passes : Nat)
    (calls : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (r : GRest D V l Γ Λ) (e : ErgExpr D Γ Λ V.erg) (R : RueckRessourcen D V Λ)
    (h : r.scopedWert = some (e, R)) (σ : World D) (ρ : Env D Γ)
    (hcheck : scopesInvH S R.scopes (σ.lese Λ e.orte) = false) :
    semH S O U passes calls r σ ρ = .logik .schleife := by
  obtain h | ⟨rest, h⟩ | ⟨Λ', rest, k, h⟩ := GRest.scopedWert_faelle h <;> subst r
  · simp only [semH, weiterH, execEndH, hcheck, Bool.false_eq_true, ite_false, zErgG]
  · rw [semH_ende_cons]
    simp only [execStmtH, hcheck, Bool.false_eq_true, ite_false]
    exact weiterH_logik S O U passes calls _ _
  · rw [semH_dann_cons]
    simp only [execStmtH, hcheck, Bool.false_eq_true, ite_false]
    exact weiterH_logik S O U passes calls _ _

/-- The reason channel checks exactly the same cleanup obligations. -/
theorem semH_scopedGrund_falsch (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (passes : Nat)
    (calls : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (r : GRest D V l Γ Λ) (grund : Fin V.gruende) (R : RueckRessourcen D V Λ)
    (h : r.scopedGrund = some (grund, R)) (σ : World D) (ρ : Env D Γ)
    (hcheck : scopesInvH S R.scopes σ = false) :
    semH S O U passes calls r σ ρ = .logik .schleife := by
  obtain h | ⟨rest, h⟩ | ⟨Λ', rest, k, h⟩ := GRest.scopedGrund_faelle h <;> subst r
  · simp only [semH, weiterH, execEndH, hcheck, Bool.false_eq_true, ite_false, zErgG]
  · rw [semH_ende_cons]
    simp only [execStmtH, hcheck, Bool.false_eq_true, ite_false]
    exact weiterH_logik S O U passes calls _ _
  · rw [semH_dann_cons]
    simp only [execStmtH, hcheck, Bool.false_eq_true, ite_false]
    exact weiterH_logik S O U passes calls _ _

/-- The scoped value return agrees with the read world before release.
    `gleich` forgets the trace, so the canonical release fold preserves it. -/
theorem semH_scopedWert (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (passes : Nat)
    (calls : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (r : GRest D V l Γ Λ) (e : ErgExpr D Γ Λ V.erg) (R : RueckRessourcen D V Λ)
    (h : r.scopedWert = some (e, R)) (σ : World D) (ρ : Env D Γ)
    (hcheck : scopesInvH S R.scopes (σ.lese Λ e.orte) = true) :
    (semH S O U passes calls r σ ρ).gleich
      (.zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ)) := by
  have hg : SG (R.scopes.foldl World.gibt (σ.lese Λ e.orte)) (σ.lese Λ e.orte) :=
    World.gibt_foldl_speicher _ _
  obtain h | ⟨rest, h⟩ | ⟨Λ', rest, k, h⟩ := GRest.scopedWert_faelle h <;> subst r
  · simp only [semH, weiterH, execEndH, hcheck, ite_true, zErgG, ZErgG.gleich]
    exact ⟨hg, trivial⟩
  · rw [semH_ende_cons]
    simp only [execStmtH, hcheck, ite_true]
    exact ⟨hg, rfl⟩
  · rw [semH_dann_cons]
    simp only [execStmtH, hcheck, ite_true]
    exact ZErgG.gleich_trans (weiterH_zurueck S O U passes calls (.dann rest k) _ _) ⟨hg, rfl⟩

/-- Reason returns use the same memory-preserving cleanup. -/
theorem semH_scopedGrund (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (passes : Nat)
    (calls : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (r : GRest D V l Γ Λ) (grund : Fin V.gruende) (R : RueckRessourcen D V Λ)
    (h : r.scopedGrund = some (grund, R)) (σ : World D) (ρ : Env D Γ)
    (hcheck : scopesInvH S R.scopes σ = true) :
    (semH S O U passes calls r σ ρ).gleich (.why σ grund) := by
  have hg : SG (R.scopes.foldl World.gibt σ) σ := World.gibt_foldl_speicher _ _
  obtain h | ⟨rest, h⟩ | ⟨Λ', rest, k, h⟩ := GRest.scopedGrund_faelle h <;> subst r
  · simp only [semH, weiterH, execEndH, hcheck, ite_true, zErgG, ZErgG.gleich]
    exact ⟨hg, trivial⟩
  · rw [semH_ende_cons]
    simp only [execStmtH, hcheck, ite_true]
    exact ⟨hg, rfl⟩
  · rw [semH_dann_cons]
    simp only [execStmtH, hcheck, ite_true]
    exact ZErgG.gleich_trans (weiterH_grund S O U passes calls (.dann rest k) _ _) ⟨hg, rfl⟩

end Gabbro.Grammatik
