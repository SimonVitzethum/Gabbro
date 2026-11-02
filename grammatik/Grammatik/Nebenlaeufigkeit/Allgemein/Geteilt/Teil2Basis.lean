module

public import Grammatik.Nebenlaeufigkeit.Allgemein.Geteilt.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Geteilt

/-- Tabellen-Träger als eigene Sorte, daneben `Carrier` (Schnitt C1, Entwurf:
    bindet die heutigen Beweise nicht um). -/
abbrev TabCarrier := Nat

/-- Global-Träger als eigene Sorte, daneben `Carrier` (Schnitt C1, Entwurf:
    bindet die heutigen Beweise nicht um). -/
abbrev GlobCarrier := Nat

/-- Faltung einer Seite: Tabelle nach zusammengelegtem Träger. -/
def carrierVonTab : TabCarrier → Carrier := fun t => t

/-- Faltung einer Seite: Global nach zusammengelegtem Träger. -/
def carrierVonGlob : GlobCarrier → Carrier := fun g => g

/-- Spiegel einer Seite: zusammengelegter Träger nach Tabelle. -/
def tabVonCarrier : Carrier → TabCarrier := fun c => c

/-- Spiegel einer Seite: zusammengelegter Träger nach Global. -/
def globVonCarrier : Carrier → GlobCarrier := fun c => c

/-- Faltung der geteilten Sorte in den zusammengelegten Träger. -/
def carrierVonSplit : TabCarrier ⊕ GlobCarrier → Carrier
  | .inl t => carrierVonTab t
  | .inr g => carrierVonGlob g

/-- Teilung des zusammengelegten Trägers in die geteilte Sorte; die
    Kennzeichnung `istTab` bleibt Behauptung der späteren Verdrahtung und wird
    hier nicht festgelegt. -/
def splitVonCarrier (istTab : Carrier → Bool) (c : Carrier) :
    TabCarrier ⊕ GlobCarrier :=
  if istTab c then .inl (tabVonCarrier c) else .inr (globVonCarrier c)

/-- Rundweg-Gestalt Tabelle: Spiegeln faltet zurück. -/
def tabRundweg (t : TabCarrier) : Prop :=
  tabVonCarrier (carrierVonTab t) = t

/-- Rundweg-Gestalt Global: Spiegeln faltet zurück. -/
def globRundweg (g : GlobCarrier) : Prop :=
  globVonCarrier (carrierVonGlob g) = g

/-- Rundweg-Gestalt Falten nach Teilen: Falten macht Teilen rückgängig. -/
def faltTeileForm (istTab : Carrier → Bool) (c : Carrier) : Prop :=
  carrierVonSplit (splitVonCarrier istTab c) = c

/-- Rundweg-Gestalt Teilen nach Falten, Tabellenseite. -/
def teileFaltFormTab (istTab : Carrier → Bool) (t : TabCarrier) : Prop :=
  splitVonCarrier istTab (carrierVonSplit (Sum.inl t)) = Sum.inl t

/-- Rundweg-Gestalt Teilen nach Falten, Globalseite. -/
def teileFaltFormGlob (istTab : Carrier → Bool) (g : GlobCarrier) : Prop :=
  splitVonCarrier istTab (carrierVonSplit (Sum.inr g)) = Sum.inr g

/-! ## 8. The split round-trips, proved (changes nothing above)

    The §7 shapes are Prop-defs; here they are discharged from the split
    types. `tabRundweg`/`globRundweg` hold for every carrier, `faltTeileForm`
    for every tag function (both branches fold back to `c`), and the two
    `teileFalt` forms hold under the matching tag premise -- the split can
    only return the injected side when the tag names it.

    The three `…Form` defs below mirror the `hinj`/`hdisj` premises that
    `Extraktion.lean` carries at `geteiltTab_trifft`/`geteiltGlob_trifft`/
    `geteiltAus_glob`: code injectivity per half and separation of the
    halves. Injectivity holds for the identity codes of cut C1 and is proved;
    separation does NOT hold in general (both halves fold through the same
    `Nat`) and stays a stated shape for downstream lanes to assume. -/

/-- Table round-trip: mirroring folds back. -/
theorem tabRundweg_holds (t : TabCarrier) : tabRundweg t := by rfl

/-- Global round-trip: mirroring folds back. -/
theorem globRundweg_holds (g : GlobCarrier) : globRundweg g := by rfl

/-- Fold after split is the identity, whatever the tag says: both branches
    fold back to `c`. -/
theorem faltTeile_holds (istTab : Carrier → Bool) (c : Carrier) :
    faltTeileForm istTab c := by
  unfold faltTeileForm splitVonCarrier
  by_cases h : istTab c = true
  · rw [if_pos h]
    rfl
  · rw [if_neg h]
    rfl

/-- Split after fold returns the table injection, provided the tag marks the
    folded code as a table. -/
theorem teileFaltTab_holds (istTab : Carrier → Bool) (t : TabCarrier)
    (h : istTab (carrierVonSplit (Sum.inl t)) = true) :
    teileFaltFormTab istTab t := by
  unfold teileFaltFormTab splitVonCarrier
  rw [if_pos h]
  rfl

/-- Split after fold returns the global injection, provided the tag marks the
    folded code as a global. -/
theorem teileFaltGlob_holds (istTab : Carrier → Bool) (g : GlobCarrier)
    (h : istTab (carrierVonSplit (Sum.inr g)) = false) :
    teileFaltFormGlob istTab g := by
  unfold teileFaltFormGlob splitVonCarrier
  have hne : ¬ istTab (carrierVonSplit (Sum.inr g)) = true := by
    rw [h]
    exact Bool.false_ne_true
  rw [if_neg hne]
  rfl

/-- Table-code injectivity as a shape: the `hinj` premise
    (`geteiltTab_trifft`) over the split table type. -/
def tabInjForm (tabs : List TabCarrier) : Prop :=
  ∀ t₁ ∈ tabs, ∀ t₂ ∈ tabs, carrierVonTab t₁ = carrierVonTab t₂ → t₁ = t₂

/-- Global-code injectivity as a shape: the `hinj` premise
    (`geteiltGlob_trifft`) over the split global type. -/
def globInjForm (globs : List GlobCarrier) : Prop :=
  ∀ g₁ ∈ globs, ∀ g₂ ∈ globs, carrierVonGlob g₁ = carrierVonGlob g₂ → g₁ = g₂

/-- Separation of the carrier halves as a shape: the `hdisj` premise
    (`geteiltAus_glob`) -- no table code meets a global code. Stated, not
    proved: under the identity codes of cut C1 it fails in general. -/
def halvesDisjointForm (tabs : List TabCarrier)
    (globs : List GlobCarrier) : Prop :=
  ∀ t ∈ tabs, ∀ g ∈ globs, carrierVonTab t ≠ carrierVonGlob g

/-- Table codes are injective: the codes ARE the carriers (cut C1). -/
theorem tabInj_all (tabs : List TabCarrier) : tabInjForm tabs := by
  intro t₁ _ t₂ _ h
  exact h

/-- Global codes are injective: the codes ARE the carriers (cut C1). -/
theorem globInj_all (globs : List GlobCarrier) : globInjForm globs := by
  intro g₁ _ g₂ _ h
  exact h

#print axioms Gabbro.Grammatik.Geteilt.tabRundweg_holds
#print axioms Gabbro.Grammatik.Geteilt.globRundweg_holds
#print axioms Gabbro.Grammatik.Geteilt.faltTeile_holds
#print axioms Gabbro.Grammatik.Geteilt.teileFaltTab_holds
#print axioms Gabbro.Grammatik.Geteilt.teileFaltGlob_holds
#print axioms Gabbro.Grammatik.Geteilt.tabInj_all
#print axioms Gabbro.Grammatik.Geteilt.globInj_all

end Gabbro.Grammatik.Geteilt
