module

public import Grammatik.Nebenlaeufigkeit.Sperren.SperreSem.T4.Teil2

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

/-- The scoped value return agrees with the read world before release.
    `gleich` forgets the trace, so the canonical release fold preserves it. -/
theorem semH_scopedWert (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (passes : Nat)
    (calls : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (r : GRest D V l Γ Λ) (e : ErgExpr D Γ Λ V.erg) (R : RueckRessourcen D V Λ)
    (h : r.scopedWert = some (e, R)) (σ : World D) (ρ : Env D Γ) :
    (semH S O U passes calls r σ ρ).gleich
      (.zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ)) := by
  have hg : SG (R.scopes.foldl World.gibt (σ.lese Λ e.orte)) (σ.lese Λ e.orte) :=
    World.gibt_foldl_speicher _ _
  obtain h | ⟨rest, h⟩ | ⟨Λ', rest, k, h⟩ := GRest.scopedWert_faelle h <;> subst r
  · exact ⟨hg, rfl⟩
  · rw [semH_ende_cons]
    exact ⟨hg, rfl⟩
  · rw [semH_dann_cons]
    exact ZErgG.gleich_trans (weiterH_zurueck S O U passes calls (.dann rest k) _ _) ⟨hg, rfl⟩

/-- Reason returns use the same memory-preserving cleanup. -/
theorem semH_scopedGrund (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (passes : Nat)
    (calls : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (r : GRest D V l Γ Λ) (grund : Fin V.gruende) (R : RueckRessourcen D V Λ)
    (h : r.scopedGrund = some (grund, R)) (σ : World D) (ρ : Env D Γ) :
    (semH S O U passes calls r σ ρ).gleich (.why σ grund) := by
  have hg : SG (R.scopes.foldl World.gibt σ) σ := World.gibt_foldl_speicher _ _
  obtain h | ⟨rest, h⟩ | ⟨Λ', rest, k, h⟩ := GRest.scopedGrund_faelle h <;> subst r
  · exact ⟨hg, rfl⟩
  · rw [semH_ende_cons]
    exact ⟨hg, rfl⟩
  · rw [semH_dann_cons]
    exact ZErgG.gleich_trans (weiterH_grund S O U passes calls (.dann rest k) _ _) ⟨hg, rfl⟩

end Gabbro.Grammatik
