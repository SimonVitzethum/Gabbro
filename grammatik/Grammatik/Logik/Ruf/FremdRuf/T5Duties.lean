/- C08: the history-independent software binding and summary duties.
   These are independent user obligations; neither follows from call-site pres.
   No goal statement is changed by introducing them. -/
module

public import Grammatik.Logik.Ruf.FremdRuf.T5

@[expose] public section

namespace Gabbro.Grammatik

open Zielsatz

variable {D : Deklaration}

/-- The software interface post refines the declared ensures. This is user
    data about the unit, independent of any oracle or recorded history. -/
def PostDeckt (E : Einheit D) : Prop :=
  ∀ a : D.Ax, D.axHerkunft a = some AxOrigin.software →
    ∀ (σ0 : World D) (ρ : Env D (D.aparams a)) (σ1 : World D)
      (v : ErgVal D (D.aerg a)),
      AxNach E.P.axVertrag a σ0 ρ σ1 v → E.Q a σ1 v = true

/-- The proof about the actual software binding: conditional normal posts and
    decoding of every answer. Boundary clauses and provider realization still
    belong to `ForeignPflicht` over the run's boundary history. -/
def ForeignVertrag (E : Einheit D) (O : Orakel D) : Prop :=
  (∀ a : D.Ax, D.axHerkunft a = some AxOrigin.software →
    ∀ (σ0 : World D) (ρ : Env D (D.aparams a)), AxVor E.P.axVertrag a σ0 ρ →
      ∀ v : ErgVal D (D.aerg a),
        einpassenErg O.zeiger (D.aerg a) (O.wirkt a (σ0.fragt (.inl a)) ρ).2 = some v →
        AxNach E.P.axVertrag a σ0 ρ (O.wirkt a (σ0.fragt (.inl a)) ρ).1 v) ∧
  (∀ a : D.Ax, D.axHerkunft a = some AxOrigin.software →
    ∀ (σ : World D) (ρ : Env D (D.aparams a)),
      (axiomAntwortSonst O a σ ρ).2 ≠ none)

/-- Forget the history-dependent boundary and provider obligations. -/
theorem foreignVertrag_of_foreign {E : Einheit D} {O : Orakel D}
    {H : List (BoundaryRecord D)} (hf : ForeignPflicht E O H) : ForeignVertrag E O :=
  ⟨hf.vertrag, hf.dekodiert⟩

/-- The binding proof supplies the full foreign duty on the empty boundary
    history. This suffices to instantiate `CallSitePflicht`, which quantifies
    over every history; no claim about a run's actual boundary records follows. -/
theorem foreignPflicht_nil_of_vertrag {E : Einheit D} {O : Orakel D}
    (hf : ForeignVertrag E O) : ForeignPflicht E O [] where
  vertrag := hf.1
  dekodiert := hf.2
  klauseln := fun n => n.elim0
  anbieter := providerRealisiert_nil O

/-- No software item means no software post-refinement obligation. -/
theorem postDeckt_ohne (E : Einheit D)
    (h : ∀ a : D.Ax, D.axHerkunft a ≠ some AxOrigin.software) : PostDeckt E :=
  fun a hsw => absurd hsw (h a)

/-- No software item means no software binding obligation, for any oracle. -/
theorem foreignVertrag_ohne (E : Einheit D) (O : Orakel D)
    (h : ∀ a : D.Ax, D.axHerkunft a ≠ some AxOrigin.software) : ForeignVertrag E O :=
  ⟨fun a hsw => absurd hsw (h a), fun a hsw => absurd hsw (h a)⟩

end Gabbro.Grammatik
