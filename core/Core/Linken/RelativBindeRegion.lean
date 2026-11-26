module

public import Core.Linken.RelativSchritt

@[expose] public section

namespace Gabbro.Core.Linken

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Annahme
open Gabbro.Core.Maschine
open Gabbro.Core.Katalog

/-- Returning a frame is the frame. -/
theorem pure_rahmen_eq (r : Rahmen) : (pure r : Id Rahmen) = r :=
  rfl

/-- Relocating a region binding commutes with the binding: the guard reads the same local slot,
    arrival table, liveness, borrows and platform on both sides, the halt relocates and the success
    record shifts its position. -/
theorem bindeRegion_proj (off : Nat) (r : Rahmen) (hpc : off ≤ r.pc)
    (receiver : Nat) (init : RegionInitializer) (live : Nat → Bool) :
    (frameZurueck off r).bindeRegion receiver init live =
      frameZurueck off (r.bindeRegion receiver init live) := by
  have h1 : (frameZurueck off r).lokale = r.lokale := frameZurueck_lokale _ _
  have h2 : (frameZurueck off r).arrivalRegions = r.arrivalRegions := arrivalRegions_proj _ _
  have h3 : (frameZurueck off r).platform = r.platform := platform_proj _ _
  have h4 : ∀ slot, (frameZurueck off r).borrowsRegion slot = r.borrowsRegion slot :=
    fun slot => borrowsRegion_proj _ _ slot
  simp only [Rahmen.bindeRegion, Id.run]
  have hE : (r.lokale[receiver]?.join.bind (wertAls .ownedRegion)) =
      ((r.lokale[receiver]?.join.bind (wertAls .ownedRegion)) : Option Nat) := rfl
  have hE' : ((frameZurueck off r).lokale[receiver]?.join.bind (wertAls .ownedRegion)) =
      (((frameZurueck off r).lokale[receiver]?.join.bind (wertAls .ownedRegion)) : Option Nat) :=
    rfl
  rw [hE, hE', h1]
  cases e1 : ((r.lokale[receiver]?.join.bind (wertAls .ownedRegion)) : Option Nat) with
  | none =>
    have e1' : ((frameZurueck off r).lokale[receiver]?.join.bind (wertAls .ownedRegion)) =
        none := by
      rw [h1]
      exact e1
    simp only [e1, e1', pure_rahmen_eq, halt_proj]
  | some slot =>
    have e1' : ((frameZurueck off r).lokale[receiver]?.join.bind (wertAls .ownedRegion)) =
        some slot := by
      rw [h1]
      exact e1
    simp only [e1, e1']
    cases e2 : (r.arrivalRegions[(slot : Nat)]?) with
    | none =>
      have e2' : ((frameZurueck off r).arrivalRegions[(slot : Nat)]?) = none := by
        rw [h2]
        exact e2
      simp only [e2, e2', pure_rahmen_eq, halt_proj]
    | some extent =>
      have e2' : ((frameZurueck off r).arrivalRegions[(slot : Nat)]?) = some extent := by
        rw [h2]
        exact e2
      simp only [e2, e2']
      have h4slot : (frameZurueck off r).borrowsRegion (slot : Nat) =
          r.borrowsRegion (slot : Nat) := h4 _
      by_cases hc : !live (slot : Nat) || r.borrowsRegion (slot : Nat)
      · have hc' : !live (slot : Nat) || (frameZurueck off r).borrowsRegion (slot : Nat) := by
          rw [h4slot]
          exact hc
        simp only [if_pos hc, if_pos hc', pure_rahmen_eq, halt_proj]
      · have hc' : ¬(!live (slot : Nat) ||
          (frameZurueck off r).borrowsRegion (slot : Nat)) := by
          rw [h4slot]
          exact hc
        simp only [if_neg hc, if_neg hc']
        cases e3 : (Gabbro.Core.Ast.LowLevel.RegionInitializer.value r.platform.ziel
            slot extent init) with
        | none =>
          have e3' : (Gabbro.Core.Ast.LowLevel.RegionInitializer.value
              (frameZurueck off r).platform.ziel slot extent init) = none := by
            rw [h3]
            exact e3
          simp only [e3, e3', pure_rahmen_eq, halt_proj]
        | some value =>
          have e3' : (Gabbro.Core.Ast.LowLevel.RegionInitializer.value
              (frameZurueck off r).platform.ziel slot extent init) = some value := by
            rw [h3]
            exact e3
          have hpc1 : (r.pc + 1) - off = (r.pc - off) + 1 := by omega
          simp only [e3, e3', frameZurueck, h1, hpc1, pure_rahmen_eq]

end Gabbro.Core.Linken
