module

public import Bruecke.Kodierung.Teil2

@[expose] public section

/-!
# Numeric statics in the bridge world

`GRel` complements `WRel` without changing its slot-only meaning. The lookup and the
numeric/aggregate distinction are exactly those of `lowGlobSide`.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg

variable (u : UProg)

/-- The first static named `g`, if it is declared as an integer range.
    Boolean and aggregate statics have no numeric bridge value. -/
def globWert (σ : World (declOf u)) (g : String) : Option Gabbro.Body.Value :=
  match globIdx u.globs g with
  | .error _ => none
  | .ok i =>
    match (globAt u i).ty with
    | .int .. => some (valOf ((declOf u).gtyp i) (σ.globs i))
    | _ => none

/-- Every declared numeric static has its G value in the Body world. -/
def GRel (σ : World (declOf u)) (w : Gabbro.Body.World) : Prop :=
  ∀ g v, globWert u σ g = some v → w (.global g) = v

/-- Encode slots first, then overwrite just the declared numeric statics. -/
def encG (σ : World (declOf u)) (base : Gabbro.Body.World) : Gabbro.Body.World := fun p =>
  match p with
  | .global g => (globWert u σ g).getD (enc u σ base p)
  | p => enc u σ base p

theorem grel_encG (σ : World (declOf u)) (base : Gabbro.Body.World) :
    GRel u σ (encG u σ base) := by
  intro g v h
  simp [encG, h]

theorem wrel_encG (σ : World (declOf u)) (base : Gabbro.Body.World) :
    WRel u σ (encG u σ base) := by
  intro c k fld v h
  exact wrel_enc u σ base c k fld v h

/-- A static read depends on globals alone, not on slots or the trace. -/
theorem globWert_congr {σ σ' : World (declOf u)} (h : σ'.globs = σ.globs) (g : String) :
    globWert u σ' g = globWert u σ g := by
  unfold globWert
  rw [h]

theorem grel_globs {σ σ' : World (declOf u)} {w : Gabbro.Body.World}
    (h : σ'.globs = σ.globs) (hG : GRel u σ w) : GRel u σ' w := by
  intro g v hv
  rw [globWert_congr u h] at hv
  exact hG g v hv

@[simp] theorem lese_globs (σ : World (declOf u)) (Λ) (orte) :
    (σ.lese Λ orte).globs = σ.globs := rfl

/-- The Body static holds the value read by the resolved G static. -/
theorem grel_lies {σ : World (declOf u)} {w : Gabbro.Body.World} (hG : GRel u σ w)
    (g : String) (i : Fin u.globs.length) (hi : globIdx u.globs g = .ok i)
    (lo hi' : Int) (ht : (globAt u i).ty = .int lo hi') :
    w (.global g) = valOf ((declOf u).gtyp i) (σ.globs i) := by
  apply hG
  simp only [globWert, hi, ht]

/-- The range of the first static by name, only for a numeric static. -/
def globShape (g : String) : Option Gabbro.Body.Shape :=
  match globIdx u.globs g with
  | .error _ => none
  | .ok i =>
    match (globAt u i).ty with
    | .int lo hi => some (.intIn lo hi)
    | _ => none

/-- Extend the slot typing with numeric static ranges. -/
def shapeOfUG : Gabbro.Body.Typing := fun p =>
  match p with
  | .global g => globShape u g
  | p => shapeOfU u p

@[simp] theorem shapeOfUG_slot (c : String) (k : Int) (fld : String) :
    shapeOfUG u (.slot c k fld) = shapeOfU u (.slot c k fld) := rfl

/-- The global part of the extended world typing follows from `GRel` alone. -/
theorem wfG_of_grel {σ : World (declOf u)} {w : Gabbro.Body.World} (hG : GRel u σ w) :
    ∀ g sh, shapeOfUG u (.global g) = some sh → (w (.global g)).hasShape sh = true := by
  intro g sh hp
  change globShape u g = some sh at hp
  unfold globShape at hp
  split at hp
  · cases hp
  · rename_i i hi
    cases ht : (globAt u i).ty with
    | int lo hi' =>
      simp only [ht, Option.some.injEq] at hp
      subst sh
      rw [grel_lies u hG g i hi lo hi' ht]
      have hty : (declOf u).gtyp i = .int lo hi' := by
        show (globAt u i).ty.toTy = _
        rw [ht]
        rfl
      have hv : ∀ x : Wert (declOf u) ((declOf u).gtyp i),
          (valOf ((declOf u).gtyp i) x).hasShape (.intIn lo hi') = true := by
        rw [hty]
        intro x
        simp [x.lo_le, x.le_hi]
      exact hv (σ.globs i)
    | bool => simp [ht] at hp
    | wert τ => simp [ht] at hp

/-- Combine the existing slot typing theorem with the independent global relation. -/
theorem wf_of_wrel_grel {σ : World (declOf u)} {w : Gabbro.Body.World}
    (hB : ∀ t : Fin u.tabs.length,
      (tabAt u t).bools = [] ∧ (tabAt u t).opts = [] ∧ (tabAt u t).werte = [])
    (hW : WRel u σ w) (hG : GRel u σ w) : Gabbro.Body.WF (shapeOfUG u) w := by
  intro p sh hp
  cases p with
  | slot c k fld => exact wf_of_wrel u hB hW (.slot c k fld) sh hp
  | field c n => exact wf_of_wrel u hB hW (.field c n) sh hp
  | global g => exact wfG_of_grel u hG g sh hp

/-- Slots and numeric statics are related to the same Body world. -/
def WGRel (σ : World (declOf u)) (w : Gabbro.Body.World) : Prop :=
  WRel u σ w ∧ GRel u σ w

theorem wgrel_enc (σ : World (declOf u)) (base : Gabbro.Body.World) :
    WGRel u σ (encG u σ base) := ⟨wrel_encG u σ base, grel_encG u σ base⟩

theorem wgrel_same {σ σ' : World (declOf u)} {w : Gabbro.Body.World}
    (hs : σ'.slots = σ.slots) (hg : σ'.globs = σ.globs) (h : WGRel u σ w) :
    WGRel u σ' w := ⟨wrel_slots u hs h.1, grel_globs u hg h.2⟩

theorem wgrel_lese {σ : World (declOf u)} {w : Gabbro.Body.World}
    (h : WGRel u σ w) (Λ) (orte) : WGRel u (σ.lese Λ orte) w :=
  wgrel_same u rfl rfl h

theorem wgrel_store {σ : World (declOf u)} {w : Gabbro.Body.World} (h : WGRel u σ w)
    (c : String) (t : Fin u.tabs.length) (ht : tabIdx u.tabs c = .ok t)
    (fld : String) (fh : FieldHit u t) (hf : fieldHit u t fld = .ok fh) (k : Int)
    (x : Wert (declOf u) ((declOf u).typ t fh.idx)) :
    WGRel u (σ.storeSlot t k fh.idx x)
      (Gabbro.Body.store w (.slot c k fld) (valOf ((declOf u).typ t fh.idx) x)) := by
  refine ⟨wrel_store u h.1 c t ht fld fh hf k x, ?_⟩
  intro g v hv
  have hg := grel_globs u (σ' := σ.storeSlot t k fh.idx x) rfl h.2 g v hv
  exact (Gabbro.Body.store_elsewhere _ _ _ _ (by intro e; cases e)).trans hg

theorem wf_of_wgrel {σ : World (declOf u)} {w : Gabbro.Body.World}
    (hB : ∀ t : Fin u.tabs.length,
      (tabAt u t).bools = [] ∧ (tabAt u t).opts = [] ∧ (tabAt u t).werte = [])
    (h : WGRel u σ w) : Gabbro.Body.WF (shapeOfUG u) w :=
  wf_of_wrel_grel u hB h.1 h.2

end Gabbro.Bruecke
