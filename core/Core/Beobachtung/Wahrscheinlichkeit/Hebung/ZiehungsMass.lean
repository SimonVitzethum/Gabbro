/-
  File:      Core/Beobachtung/Wahrscheinlichkeit/Hebung/ZiehungsMass.lean
  Subject:   The Kolmogorov product measure on bands and its exact cylinder masses.

  This is the measure side of the lift, proved independently of replay: a draw law is
  pushed from `Fin Q.anz` to `Nat`, an infinite product of these laws is taken over
  the countable index `Nat × Nat` (source id, draw index), and the product is pushed
  forward along currying to `Band = Nat → Nat → Nat`. `Measure.infinitePi_pi` then
  gives the cylinder weight exactly, for every key-`Nodup` path.

  The replay side of `Hebebuendel` is not supplied here; the pinned statement is
  refuted separately in `Gegenbeispiel.lean`.
-/
module

public import Core.Beobachtung.Wahrscheinlichkeit.Hebung
public import Mathlib.Probability.ProductMeasure

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog
open MeasureTheory

/-- The law of one draw, pushed from `Fin Q.anz` to `Nat` by the outcome value. -/
noncomputable def ziehMass (Q : Zufallsquelle) : MeasureTheory.Measure Nat :=
  Q.gesetz.toMeasure.map (fun a : Fin Q.anz => a.val)

instance ziehMass_istWMass (Q : Zufallsquelle) : IsProbabilityMeasure (ziehMass Q) := by
  dsimp [ziehMass]
  infer_instance

/-- The residue class of an outcome has exactly the declared law's mass. -/
theorem ziehMass_rest (Q : Zufallsquelle) (a : Fin Q.anz) :
    ziehMass Q {n : Nat | n % Q.anz = a.val} = Q.gesetz a := by
  unfold ziehMass
  rw [Measure.map_apply (by fun_prop) (by measurability)]
  have hpre : (fun b : Fin Q.anz => b.val) ⁻¹' {n : Nat | n % Q.anz = a.val} =
      ({a} : Set (Fin Q.anz)) := by
    ext b
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro hb
      apply Fin.ext
      rw [Nat.mod_eq_of_lt b.2] at hb
      exact hb
    · intro hb
      rw [hb]
      exact Nat.mod_eq_of_lt a.2
  rw [hpre, PMF.toMeasure_apply_singleton Q.gesetz a (MeasurableSet.singleton a)]

/-- The pair-indexed product space that carries the independent draws. -/
abbrev Paarband : Type := (Nat × Nat) → Nat

/-- Currying: a pair-indexed draw table becomes a band. -/
def bandVonPaare (f : Paarband) : Band := fun id k => f (id, k)

theorem bandVonPaare_messbar : Measurable bandVonPaare := by
  unfold bandVonPaare
  fun_prop

/-- The band measure: independent draws over every source and position, pushed
    through currying. Positions outside the binding's source are present but never
    constrained by a cylinder, so they contribute no mass factor. -/
noncomputable def bandMass (Q : Zufallsquelle) : MeasureTheory.Measure Band :=
  (Measure.infinitePi (fun _ : Nat × Nat => ziehMass Q)).map bandVonPaare

instance bandMass_istWMass (Q : Zufallsquelle) : IsProbabilityMeasure (bandMass Q) := by
  dsimp [bandMass]
  infer_instance

/-- A finite cylinder set is measurable: a finite intersection of coordinate conditions. -/
theorem zylinderMenge_messbar (Q : Zufallsquelle) (pfad : List (Nat × Fin Q.anz)) :
    MeasurableSet {band : Band | ∀ p ∈ pfad, band Q.id p.1 % Q.anz = p.2.val} := by
  induction pfad with
  | nil =>
      have hset : {band : Band | ∀ p ∈ ([] : List (Nat × Fin Q.anz)),
          band Q.id p.1 % Q.anz = p.2.val} = Set.univ := by
        ext band
        constructor
        · intro _
          trivial
        · intro _ p hp
          cases hp
      rw [hset]
      exact MeasurableSet.univ
  | cons p ps ih =>
      have hcoord : MeasurableSet {band : Band | band Q.id p.1 % Q.anz = p.2.val} := by
        measurability
      simpa only [List.mem_cons, forall_eq_or_imp, Set.setOf_and] using hcoord.inter ih

/-- Exact cylinder masses on key-`Nodup` paths. -/
theorem bandMass_zylinder (Q : Zufallsquelle) (Z : Zylinder Q)
    (hnodup : (Z.pfad.map Prod.fst).Nodup) :
    bandMass Q {band : Band | ∀ p ∈ Z.pfad, band Q.id p.1 % Q.anz = p.2.val} =
      ZylinderGewicht Q Z := by
  classical
  let L : List (Nat × Nat) := Z.pfad.map fun p => (Q.id, p.1)
  let s : Finset (Nat × Nat) := L.toFinset
  let t : (Nat × Nat) → Set Nat := fun ij =>
    {n : Nat | ∀ p ∈ Z.pfad, (Q.id, p.1) = ij → n % Q.anz = p.2.val}
  let menge : Set Band := {band : Band | ∀ p ∈ Z.pfad, band Q.id p.1 % Q.anz = p.2.val}
  have ht : ∀ ij, MeasurableSet (t ij) := by
    intro ij
    measurability
  have hpre : bandVonPaare ⁻¹' menge = Set.pi s t := by
    ext f
    simp only [Set.mem_preimage, menge, Set.mem_setOf_eq, Set.mem_pi, t, s]
    constructor
    · intro h ij hij q hq hkey
      rw [← hkey]
      exact h q hq
    · intro h p hp
      have hpij : (Q.id, p.1) ∈ s := by
        exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨p, hp, rfl⟩)
      exact h (Q.id, p.1) hpij p hp rfl
  have hmenge : MeasurableSet menge := by
    change MeasurableSet {band : Band | ∀ p ∈ Z.pfad, band Q.id p.1 % Q.anz = p.2.val}
    exact zylinderMenge_messbar Q Z.pfad
  have hmass : bandMass Q menge =
      Measure.infinitePi (fun _ : Nat × Nat => ziehMass Q) (Set.pi s t) := by
    unfold bandMass
    rw [Measure.map_apply bandVonPaare_messbar hmenge, hpre]
  have hLnodup : L.Nodup := by
    dsimp only [L]
    apply List.Nodup.map_on
    · intro p hp q hq heq
      exact List.inj_on_of_nodup_map hnodup hp hq (congrArg Prod.snd heq)
    · exact List.Nodup.of_map Prod.fst hnodup
  have hg : ∀ p ∈ Z.pfad, ziehMass Q (t (Q.id, p.1)) = Q.gesetz p.2 := by
    intro p hp
    have htgleich : t (Q.id, p.1) = {n : Nat | n % Q.anz = p.2.val} := by
      ext n
      simp only [t, Set.mem_setOf_eq]
      constructor
      · intro h
        exact h p hp rfl
      · intro hn q hq hkey
        have qeqp : q = p := by
          apply List.inj_on_of_nodup_map hnodup hq hp
          exact congrArg Prod.snd hkey
        subst q
        exact hn
    rw [htgleich, ziehMass_rest]
  calc
    bandMass Q {band : Band | ∀ p ∈ Z.pfad, band Q.id p.1 % Q.anz = p.2.val} =
        Measure.infinitePi (fun _ : Nat × Nat => ziehMass Q) (Set.pi s t) := by
      change bandMass Q menge = _
      exact hmass
    _ = ∏ ij ∈ s, ziehMass Q (t ij) := by
      exact Measure.infinitePi_pi (μ := fun _ : Nat × Nat => ziehMass Q)
        (s := s) (t := t) (fun ij _ => ht ij)
    _ = (L.map fun ij => ziehMass Q (t ij)).prod := by
      exact List.prod_toFinset (fun ij => ziehMass Q (t ij)) hLnodup
    _ = (Z.pfad.map fun p => Q.gesetz p.2).prod := by
      dsimp only [L]
      simp only [List.map_map]
      exact congrArg List.prod (List.map_congr_left (fun p hp => by
        simp only [Function.comp_apply]
        exact hg p hp))
    _ = ZylinderGewicht Q Z := by rfl

/-- The measure side of the lift bundle, packaged for reuse. -/
structure MassBuendel (B : Zufallsbindung) where
  mu : MeasureTheory.Measure Band
  istWMass : MeasureTheory.IsProbabilityMeasure mu
  massErhalt : ∀ Z : Zylinder B.quelle, (Z.pfad.map Prod.fst).Nodup →
    mu {band : Band | ∀ p ∈ Z.pfad, band B.quelle.id p.1 % B.quelle.anz = p.2.val} =
      ZylinderGewicht B.quelle Z

/-- The measure side is always satisfiable: the product construction above. -/
noncomputable def massBuendel_erfuellbar (B : Zufallsbindung) : MassBuendel B :=
  ⟨bandMass B.quelle, inferInstance, fun Z h => bandMass_zylinder B.quelle Z h⟩

end Gabbro.Core.Beobachtung
