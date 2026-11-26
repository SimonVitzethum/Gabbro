/-
  File:      core/Core/Ziel/Korrektheit/Waechter/WaechterAbstrakt.lean
  Subject:   ABSTRACTION from the computable guard analysis to `WaechterHalten`.

  If the static check accepts the code (`waechterPruefeCode`), every generated guard
  holds on every ideal run of the unit, no reachable cut contains an internal
  deadlock or a closed waiting set, and every lock held under a declared hold bound
  stays checker-eligible: `waechterAbstrakt`.

  The run invariant (`invariantAlle` in `WaechterRahmen.lean`) carries the joined
  environments to every frame at every cut and keeps every lock free. The guard
  conjunct follows from `pruefeBedarf_gilt`: a guard demand read at a satisfying
  frame meets the pinned guard row, because the static hull covers the runtime
  value. Deadlock freedom is vacuous: the elaborated system never blocks
  (`blockiert` is constantly false). The holder conjunct is vacuous: locks stay
  free, so its premise never holds.

  `WaechterFragmentVollstaendigAussage` states completeness on the named decidable
  fragment for the prover handover: on `waechterFragmentCode` every held guard
  passes the static check. The remainder outside the fragment is the pinned
  `PrueferRestUnentscheidbarAussage`.
-/
module

public import Core.Ziel.Korrektheit.Waechter.WaechterRahmen
public import Core.Maschine.Start
public import Core.Annahme.Waechter
public import Core.Ast.Semantik.Elaborierung
public import Core.Ast.Semantik.Runtime.Mehrkontext.System
public import Core.Ziel.Korrektheit.Beweise.BegleitZusammensetzung
public import Core.Ziel.Korrektheit.NichtAkzeptierteEinheit

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit.WaechterAnalyse

open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Ast
open Gabbro.Core.Maschine
open Gabbro.Core.Aussenfrage
open Gabbro.Core.Katalog
open Gabbro.Core.Annahme
open Classical

/-- A guard demand at a non-guard instruction is impossible. -/
theorem guard_none_absurd {b : Befehl} {frame : Gabbro.Core.Ast.Semantik.Rahmen} {op : PartielleOperation}
    {args : Operanden op} {C : Prop}
    (hg : b.guard frame = some ⟨op, args⟩) (h0 : b.guard frame = none) : C := by
  rw [h0] at hg
  cases hg

/-- A text value read through a type coercion has the shape the satisfaction
    predicate needs, with the same bytes. -/
theorem wertAls_text_form {capacity : Nat} {d : Dynamisch} {text : TextValue capacity}
    (h : wertAls (.text capacity) d = some text) :
    ∃ (cap' : Nat) (v : TextValue cap'), d = ⟨.text cap', v⟩ ∧ v.bytes = text.bytes := by
  obtain ⟨ty, v⟩ := d
  cases ty with
  | text cap' =>
      simp only [wertAls] at h
      by_cases hfits : v.bytes.size ≤ capacity
      · rw [dif_pos hfits] at h
        have heq : (⟨v.bytes, hfits⟩ : TextValue capacity) = text :=
          Option.some_inj.mp h
        cases heq
        exact ⟨cap', v, rfl, rfl⟩
      · rw [dif_neg hfits] at h
        cases h
  | int lo hi =>
      have hne : ¬((.int lo hi : Ty .value) = .text capacity) := fun heq => by cases heq
      simp only [wertAls, dif_neg hne] at h
      cases h
  | bool =>
      have hne : ¬((.bool : Ty .value) = .text capacity) := fun heq => by cases heq
      simp only [wertAls, dif_neg hne] at h
      cases h
  | array element count =>
      have hne : ¬(((.array element count : Ty .value)) = .text capacity) := fun heq => by cases heq
      simp only [wertAls, dif_neg hne] at h
      cases h
  | productEnd =>
      have hne : ¬((.productEnd : Ty .value) = .text capacity) := fun heq => by cases heq
      simp only [wertAls, dif_neg hne] at h
      cases h
  | product head tail =>
      have hne : ¬(((.product head tail : Ty .value)) = .text capacity) := fun heq => by cases heq
      simp only [wertAls, dif_neg hne] at h
      cases h
  | record name labels layout =>
      have hne : ¬(((.record name labels layout : Ty .value)) = .text capacity) := fun heq => by cases heq
      simp only [wertAls, dif_neg hne] at h
      cases h
  | recordSchema name labels layout =>
      have hne : ¬(((.recordSchema name labels layout : Ty .value)) = .text capacity) := fun heq => by cases heq
      simp only [wertAls, dif_neg hne] at h
      cases h
  | sumEnd =>
      have hne : ¬((.sumEnd : Ty .value) = .text capacity) := fun heq => by cases heq
      simp only [wertAls, dif_neg hne] at h
      cases h
  | sum head tail =>
      have hne : ¬(((.sum head tail : Ty .value)) = .text capacity) := fun heq => by cases heq
      simp only [wertAls, dif_neg hne] at h
      cases h
  | variant name labels hasPayload layout =>
      have hne : ¬(((.variant name labels hasPayload layout : Ty .value)) = .text capacity) := fun heq => by cases heq
      simp only [wertAls, dif_neg hne] at h
      cases h
  | variantSchema name labels hasPayload layout =>
      have hne : ¬(((.variantSchema name labels hasPayload layout : Ty .value)) = .text capacity) := fun heq => by cases heq
      simp only [wertAls, dif_neg hne] at h
      cases h
  | carrierSchema count labels layout exported =>
      have hne : ¬(((.carrierSchema count labels layout exported : Ty .value)) = .text capacity) := fun heq => by cases heq
      simp only [wertAls, dif_neg hne] at h
      cases h
  | effectGroupSchema effects =>
      have hne : ¬(((.effectGroupSchema effects : Ty .value)) = .text capacity) := fun heq => by cases heq
      simp only [wertAls, dif_neg hne] at h
      cases h
  | address space =>
      have hne : ¬(((.address space : Ty .value)) = .text capacity) := fun heq => by cases heq
      simp only [wertAls, dif_neg hne] at h
      cases h
  | ownedRegion =>
      have hne : ¬((.ownedRegion : Ty .value) = .text capacity) := fun heq => by cases heq
      simp only [wertAls, dif_neg hne] at h
      cases h
  | regionView element =>
      have hne : ¬(((.regionView element : Ty .value)) = .text capacity) := fun heq => by cases heq
      simp only [wertAls, dif_neg hne] at h
      cases h
  | ptr space recht referent =>
      have hne : ¬(((.ptr space recht referent : Ty .value)) = .text capacity) := fun heq => by cases heq
      simp only [wertAls, dif_neg hne] at h
      cases h

/-- A division demand read at a satisfying frame meets the guard row: the static
    hull keeps the divisor away from zero, and satisfaction carries it to the
    runtime value. -/
theorem teilenBedarf_gilt (code : List Befehl) (links : Nat)
    (hmem : Befehl.teilen links ∈ code)
    (frame : Gabbro.Core.Ast.Semantik.Rahmen) (h : RahmenErfuellt code frame)
    (hp : pruefeBedarf code (Befehl.teilen links) = true)
    (op : PartielleOperation) (args : Operanden op)
    (hg : (Befehl.teilen links).guard frame = some ⟨op, args⟩) :
    waechterBedarf op args := by
  rw [show (Befehl.teilen links).guard frame = Option.bind (frame.zahl links) (fun a =>
      Option.bind (frame.zahl (links + 1)) (fun b =>
        (pure (⟨.division, (a.zahl.wert.natAbs, b.zahl.wert.natAbs)⟩ : Bedarf)))) from rfl] at hg
  cases ha : frame.zahl links with
  | none =>
      rw [ha, Option.bind_none] at hg
      cases hg
  | some a =>
      cases hb : frame.zahl (links + 1) with
      | none =>
          rw [ha, hb, Option.bind_some, Option.bind_none] at hg
          cases hg
      | some b =>
          rw [ha, hb, Option.bind_some, Option.bind_some] at hg
          cases hg
          simp only [waechterBedarf]
          have hmatch : (match umgebungInt code (links + 1) with
              | some (lo, hi) => decide (1 ≤ lo ∨ hi ≤ -1)
              | none => false) = true := hp
          cases hlook : umgebungInt code (links + 1) with
          | none =>
              have hfalse : (match (none : Option (Int × Int)) with
                  | some (lo, hi) => decide (1 ≤ lo ∨ hi ≤ -1)
                  | none => false) = false := rfl
              rw [hlook] at hmatch
              rw [hfalse] at hmatch
              cases hmatch
          | some vals =>
              obtain ⟨lo, hi⟩ := vals
              have htrue : decide (1 ≤ lo ∨ hi ≤ -1) = true := by
                have hred : (match (some (lo, hi) : Option (Int × Int)) with
                    | some (lo', hi') => decide (1 ≤ lo' ∨ hi' ≤ -1)
                    | none => false) = decide (1 ≤ lo ∨ hi ≤ -1) := rfl
                rw [hlook] at hmatch
                rw [hred] at hmatch
                exact hmatch
              have hdisj : 1 ≤ lo ∨ hi ≤ -1 := by
                simpa only [decide_eq_true_eq] using htrue
              have hb' : (frame.temp (links + 1)).bind alsGanzzahl = some b := hb
              have hsat := h.1 (links + 1) lo hi hlook b hb'
              have hne : b.zahl.wert ≠ 0 := by omega
              exact fun h0 => hne (Int.natAbs_eq_zero.mp h0)

/-- An array-index demand read at a satisfying frame meets the guard row. -/
theorem liesArrayBedarf_gilt (code : List Befehl) (basis : Nat)
    (element : Ty .value) (count : Nat)
    (hmem : Befehl.liesArray basis element count ∈ code)
    (frame : Gabbro.Core.Ast.Semantik.Rahmen) (h : RahmenErfuellt code frame)
    (hp : pruefeBedarf code (Befehl.liesArray basis element count) = true)
    (op : PartielleOperation) (args : Operanden op)
    (hg : (Befehl.liesArray basis element count).guard frame = some ⟨op, args⟩) :
    waechterBedarf op args := by
  rw [show (Befehl.liesArray basis element count).guard frame =
      Option.bind (frame.zahl (basis + 1)) (fun i =>
        (pure (⟨.index, ((if i.zahl.wert < 0 then count else i.zahl.wert.toNat), count)⟩ :
          Bedarf))) from rfl] at hg
  cases hi : frame.zahl (basis + 1) with
  | none =>
      rw [hi, Option.bind_none] at hg
      cases hg
  | some i =>
      rw [hi, Option.bind_some] at hg
      cases hg
      simp only [waechterBedarf]
      have hmatch : (match umgebungInt code (basis + 1) with
          | some (lo, hi) => decide (0 ≤ lo ∧ hi < (count : Int))
          | none => false) = true := hp
      cases hlook : umgebungInt code (basis + 1) with
      | none =>
          have hfalse : (match (none : Option (Int × Int)) with
              | some (lo, hi) => decide (0 ≤ lo ∧ hi < (count : Int))
              | none => false) = false := rfl
          rw [hlook] at hmatch
          rw [hfalse] at hmatch
          cases hmatch
      | some vals =>
          obtain ⟨lo, hiBd⟩ := vals
          have htrue : decide (0 ≤ lo ∧ hiBd < (count : Int)) = true := by
            have hred : (match (some (lo, hiBd) : Option (Int × Int)) with
                | some (lo', hi') => decide (0 ≤ lo' ∧ hi' < (count : Int))
                | none => false) = decide (0 ≤ lo ∧ hiBd < (count : Int)) := rfl
            rw [hlook] at hmatch
            rw [hred] at hmatch
            exact hmatch
          have hcov : 0 ≤ lo ∧ hiBd < (count : Int) := by
            simpa only [decide_eq_true_eq] using htrue
          have hi' : (frame.temp (basis + 1)).bind alsGanzzahl = some i := hi
          have hsat := h.1 (basis + 1) lo hiBd hlook i hi'
          by_cases hneg : i.zahl.wert < 0
          · rw [if_pos hneg]
            omega
          · rw [if_neg hneg]
            have hnn : 0 ≤ i.zahl.wert := by omega
            omega

/-- A text-index demand read at a satisfying frame meets the guard row: the static
    text-length lower bound covers the runtime length. -/
theorem textIndexBedarf_gilt (code : List Befehl) (basis capacity : Nat)
    (hmem : Befehl.textIndex basis capacity ∈ code)
    (frame : Gabbro.Core.Ast.Semantik.Rahmen) (h : RahmenErfuellt code frame)
    (hp : pruefeBedarf code (Befehl.textIndex basis capacity) = true)
    (op : PartielleOperation) (args : Operanden op)
    (hg : (Befehl.textIndex basis capacity).guard frame = some ⟨op, args⟩) :
    waechterBedarf op args := by
  rw [show (Befehl.textIndex basis capacity).guard frame =
      Option.bind ((frame.temp basis).bind (wertAls (.text capacity))) (fun text =>
        Option.bind (frame.zahl (basis + 1)) (fun offset =>
          (pure (⟨.index, ((if offset.zahl.wert < 0 then text.bytes.size
            else offset.zahl.wert.toNat), text.bytes.size)⟩ : Bedarf)))) from rfl] at hg
  cases htext : (frame.temp basis).bind (wertAls (.text capacity)) with
  | none =>
      rw [htext, Option.bind_none] at hg
      cases hg
  | some text =>
      cases hoff : frame.zahl (basis + 1) with
      | none =>
          rw [htext, hoff, Option.bind_some, Option.bind_none] at hg
          cases hg
      | some offset =>
          rw [htext, hoff, Option.bind_some, Option.bind_some] at hg
          cases hg
          simp only [waechterBedarf]
          have hmatch : (match umgebungText code basis, umgebungInt code (basis + 1) with
              | some (laenge, _), some (lo, hi) => decide (0 ≤ lo ∧ hi < (laenge : Int))
              | _, _ => false) = true := hp
          cases hT : umgebungText code basis with
          | none =>
              have hfalse : (match (none : Option (Nat × Nat)), umgebungInt code (basis + 1) with
                  | some (laenge, _), some (lo, hi) => decide (0 ≤ lo ∧ hi < (laenge : Int))
                  | _, _ => false) = false := rfl
              rw [hT] at hmatch
              rw [hfalse] at hmatch
              cases hmatch
          | some tp =>
              obtain ⟨laenge, H⟩ := tp
              cases hI : umgebungInt code (basis + 1) with
              | none =>
                  have hfalse : (match (some (laenge, H) : Option (Nat × Nat)), (none : Option (Int × Int)) with
                      | some (laenge', _), some (lo', hi') =>
                          decide (0 ≤ lo' ∧ hi' < (laenge' : Int))
                      | _, _ => false) = false := rfl
                  rw [hT, hI] at hmatch
                  rw [hfalse] at hmatch
                  cases hmatch
              | some ip =>
                  obtain ⟨lo, hi⟩ := ip
                  have htrue : decide (0 ≤ lo ∧ hi < (laenge : Int)) = true := by
                    have hred : (match (some (laenge, H) : Option (Nat × Nat)),
                        (some (lo, hi) : Option (Int × Int)) with
                        | some (laenge', _), some (lo', hi') =>
                            decide (0 ≤ lo' ∧ hi' < (laenge' : Int))
                        | _, _ => false) = decide (0 ≤ lo ∧ hi < (laenge : Int)) := rfl
                    rw [hT, hI] at hmatch
                    rw [hred] at hmatch
                    exact hmatch
                  have hcov : 0 ≤ lo ∧ hi < (laenge : Int) := by
                    simpa only [decide_eq_true_eq] using htrue
                  have hoff' : (frame.temp (basis + 1)).bind alsGanzzahl = some offset := hoff
                  have hsat := h.1 (basis + 1) lo hi hI offset hoff'
                  cases hd : frame.temp basis with
                  | none =>
                      simp only [hd, Option.bind_none] at htext
                      cases htext
                  | some d =>
                      have hwd : wertAls (.text capacity) d = some text := by
                        simp only [hd, Option.bind_some] at htext
                        exact htext
                      obtain ⟨cap', v, hd_eq, hbytes⟩ := wertAls_text_form hwd
                      have hd' : frame.temp basis = some (⟨.text cap', v⟩ : Dynamisch) := by
                        rw [hd_eq] at hd
                        exact hd
                      have hlen := h.2.1 basis laenge H hT _ hd' cap' v rfl
                      by_cases hneg : offset.zahl.wert < 0
                      · rw [if_pos hneg]
                        omega
                      · rw [if_neg hneg]
                        have hnn : 0 ≤ offset.zahl.wert := by omega
                        rw [← hbytes]
                        omega

/-- A substring demand read at a satisfying frame meets the guard row. -/
theorem substringBedarf_gilt (code : List Befehl) (basis capacity : Nat)
    (hmem : Befehl.substring basis capacity ∈ code)
    (frame : Gabbro.Core.Ast.Semantik.Rahmen) (h : RahmenErfuellt code frame)
    (hp : pruefeBedarf code (Befehl.substring basis capacity) = true)
    (op : PartielleOperation) (args : Operanden op)
    (hg : (Befehl.substring basis capacity).guard frame = some ⟨op, args⟩) :
    waechterBedarf op args := by
  rw [show (Befehl.substring basis capacity).guard frame =
      Option.bind ((frame.temp basis).bind (wertAls (.text capacity))) (fun text =>
        Option.bind (frame.zahl (basis + 1)) (fun first =>
          Option.bind (frame.zahl (basis + 2)) (fun last =>
            (pure (⟨.teilfolge, (first.zahl.wert, last.zahl.wert, text.bytes.size)⟩ :
              Bedarf))))) from rfl] at hg
  cases htext : (frame.temp basis).bind (wertAls (.text capacity)) with
  | none =>
      rw [htext, Option.bind_none] at hg
      cases hg
  | some text =>
      cases hfirst : frame.zahl (basis + 1) with
      | none =>
          rw [htext, hfirst, Option.bind_some, Option.bind_none] at hg
          cases hg
      | some first =>
          cases hlast : frame.zahl (basis + 2) with
          | none =>
              rw [htext, hfirst, hlast, Option.bind_some, Option.bind_some,
                Option.bind_none] at hg
              cases hg
          | some last =>
              rw [htext, hfirst, hlast, Option.bind_some, Option.bind_some,
                Option.bind_some] at hg
              cases hg
              simp only [waechterBedarf]
              have hmatch : (match umgebungText code basis, umgebungInt code (basis + 1),
                  umgebungInt code (basis + 2) with
                  | some (laenge, _), some (loErste, hiErste), some (loLetzte, hiLetzte) =>
                      decide (0 ≤ loErste ∧ hiErste ≤ loLetzte ∧ hiLetzte ≤ (laenge : Int))
                  | _, _, _ => false) = true := hp
              cases hT : umgebungText code basis with
              | none =>
                  have hfalse : (match (none : Option (Nat × Nat)),
                      umgebungInt code (basis + 1), umgebungInt code (basis + 2) with
                      | some (laenge, _), some (loErste, hiErste), some (loLetzte, hiLetzte) =>
                          decide (0 ≤ loErste ∧ hiErste ≤ loLetzte ∧ hiLetzte ≤ (laenge : Int))
                      | _, _, _ => false) = false := rfl
                  rw [hT] at hmatch
                  rw [hfalse] at hmatch
                  cases hmatch
              | some tp =>
                  obtain ⟨laenge, H⟩ := tp
                  cases hE : umgebungInt code (basis + 1) with
                  | none =>
                      have hfalse : (match (some (laenge, H) : Option (Nat × Nat)),
                          (none : Option (Int × Int)), umgebungInt code (basis + 2) with
                          | some (laenge', _), some (loErste', hiErste'),
                              some (loLetzte', hiLetzte') =>
                              decide (0 ≤ loErste' ∧ hiErste' ≤ loLetzte' ∧
                                hiLetzte' ≤ (laenge' : Int))
                          | _, _, _ => false) = false := rfl
                      rw [hT, hE] at hmatch
                      rw [hfalse] at hmatch
                      cases hmatch
                  | some ep =>
                      obtain ⟨loErste, hiErste⟩ := ep
                      cases hL : umgebungInt code (basis + 2) with
                      | none =>
                          have hfalse : (match (some (laenge, H) : Option (Nat × Nat)),
                              (some (loErste, hiErste) : Option (Int × Int)),
                              (none : Option (Int × Int)) with
                              | some (laenge', _), some (loErste', hiErste'),
                                  some (loLetzte', hiLetzte') =>
                                  decide (0 ≤ loErste' ∧ hiErste' ≤ loLetzte' ∧
                                    hiLetzte' ≤ (laenge' : Int))
                              | _, _, _ => false) = false := rfl
                          rw [hT, hE, hL] at hmatch
                          rw [hfalse] at hmatch
                          cases hmatch
                      | some lp =>
                          obtain ⟨loLetzte, hiLetzte⟩ := lp
                          have htrue : decide (0 ≤ loErste ∧ hiErste ≤ loLetzte ∧
                              hiLetzte ≤ (laenge : Int)) = true := by
                            have hred : (match (some (laenge, H) : Option (Nat × Nat)),
                                (some (loErste, hiErste) : Option (Int × Int)),
                                (some (loLetzte, hiLetzte) : Option (Int × Int)) with
                                | some (laenge', _), some (loErste', hiErste'),
                                    some (loLetzte', hiLetzte') =>
                                    decide (0 ≤ loErste' ∧ hiErste' ≤ loLetzte' ∧
                                      hiLetzte' ≤ (laenge' : Int))
                                | _, _, _ => false) =
                                decide (0 ≤ loErste ∧ hiErste ≤ loLetzte ∧
                                  hiLetzte ≤ (laenge : Int)) := rfl
                            rw [hT, hE, hL] at hmatch
                            rw [hred] at hmatch
                            exact hmatch
                          have hcov : 0 ≤ loErste ∧ hiErste ≤ loLetzte ∧
                              hiLetzte ≤ (laenge : Int) := by
                            simpa only [decide_eq_true_eq] using htrue
                          have hfirst' : (frame.temp (basis + 1)).bind alsGanzzahl =
                              some first := hfirst
                          have hsatE := h.1 (basis + 1) loErste hiErste hE first hfirst'
                          have hlast' : (frame.temp (basis + 2)).bind alsGanzzahl =
                              some last := hlast
                          have hsatL := h.1 (basis + 2) loLetzte hiLetzte hL last hlast'
                          cases hd : frame.temp basis with
                          | none =>
                              simp only [hd, Option.bind_none] at htext
                              cases htext
                          | some d =>
                              have hwd : wertAls (.text capacity) d = some text := by
                                simp only [hd, Option.bind_some] at htext
                                exact htext
                              obtain ⟨cap', v, hd_eq, hbytes⟩ := wertAls_text_form hwd
                              have hd' : frame.temp basis =
                                  some (⟨.text cap', v⟩ : Dynamisch) := by
                                rw [hd_eq] at hd
                                exact hd
                              have hlen := h.2.1 basis laenge H hT _ hd' cap' v rfl
                              rw [← hbytes]
                              omega

/-- A guard demand read at a satisfying frame meets the pinned guard row. -/
theorem pruefeBedarf_gilt (code : List Befehl) (b : Befehl) (frame : Gabbro.Core.Ast.Semantik.Rahmen)
    (hmem : b ∈ code) (h : RahmenErfuellt code frame)
    (hp : pruefeBedarf code b = true) (op : PartielleOperation) (args : Operanden op)
    (hg : b.guard frame = some ⟨op, args⟩) :
    waechterBedarf op args := by
  cases b with
  | teilen links => exact teilenBedarf_gilt code links hmem frame h hp op args hg
  | liesArray basis element count =>
      exact liesArrayBedarf_gilt code basis element count hmem frame h hp op args hg
  | textIndex basis capacity =>
      exact textIndexBedarf_gilt code basis capacity hmem frame h hp op args hg
  | substring basis capacity =>
      exact substringBedarf_gilt code basis capacity hmem frame h hp op args hg
  | literal _ _ => exact guard_none_absurd hg rfl
  | binaer _ _ => exact guard_none_absurd hg rfl
  | binden _ _ => exact guard_none_absurd hg rfl
  | wahrheitswert _ _ => exact guard_none_absurd hg rfl
  | lesen _ _ => exact guard_none_absurd hg rfl
  | negativ _ _ => exact guard_none_absurd hg rfl
  | negieren _ => exact guard_none_absurd hg rfl
  | verneinen _ => exact guard_none_absurd hg rfl
  | vergleichen _ _ => exact guard_none_absurd hg rfl
  | springeWenn _ _ _ => exact guard_none_absurd hg rfl
  | zuweisen _ _ _ => exact guard_none_absurd hg rfl
  | zurueck _ _ => exact guard_none_absurd hg rfl
  | springe _ => exact guard_none_absurd hg rfl
  | blockEnde _ => exact guard_none_absurd hg rfl
  | bindeWert _ _ _ => exact guard_none_absurd hg rfl
  | definiere _ _ _ _ _ _ _ _ => exact guard_none_absurd hg rfl
  | rufe _ _ _ => exact guard_none_absurd hg rfl
  | rueckVoid => exact guard_none_absurd hg rfl
  | pruefeMass _ => exact guard_none_absurd hg rfl
  | setzePasszahl _ _ => exact guard_none_absurd hg rfl
  | whileTest _ _ _ => exact guard_none_absurd hg rfl
  | forAnfang _ _ _ _ _ _ => exact guard_none_absurd hg rfl
  | forTest _ _ => exact guard_none_absurd hg rfl
  | forNaechster _ _ => exact guard_none_absurd hg rfl
  | zurueckSprung _ => exact guard_none_absurd hg rfl
  | starte _ => exact guard_none_absurd hg rfl
  | ende => exact guard_none_absurd hg rfl
  | baueArray _ _ _ => exact guard_none_absurd hg rfl
  | baueTupel _ _ => exact guard_none_absurd hg rfl
  | liesTupelfeld _ _ _ => exact guard_none_absurd hg rfl
  | bindeTupel _ _ _ => exact guard_none_absurd hg rfl
  | definiereRecord _ _ _ => exact guard_none_absurd hg rfl
  | baueRecord _ _ _ _ _ => exact guard_none_absurd hg rfl
  | liesRecordFeld _ _ _ _ _ => exact guard_none_absurd hg rfl
  | setzeRecordFeld _ _ _ _ _ _ => exact guard_none_absurd hg rfl
  | definiereVariante _ _ _ => exact guard_none_absurd hg rfl
  | baueVariante _ _ _ _ _ => exact guard_none_absurd hg rfl
  | waehleVariante _ _ _ _ _ => exact guard_none_absurd hg rfl
  | textLiteral _ _ => exact guard_none_absurd hg rfl
  | textConcat _ _ _ => exact guard_none_absurd hg rfl
  | textLength _ _ => exact guard_none_absurd hg rfl
  | definiereTraeger _ _ _ _ => exact guard_none_absurd hg rfl
  | optionIstBesetzt _ _ => exact guard_none_absurd hg rfl
  | definiereEffektgruppe _ => exact guard_none_absurd hg rfl
  | waehleUmgebung _ _ _ => exact guard_none_absurd hg rfl
  | bindeRegion _ _ => exact guard_none_absurd hg rfl
  | zugriff _ => exact guard_none_absurd hg rfl
  | faden _ => exact guard_none_absurd hg rfl
  | aussen _ => exact guard_none_absurd hg rfl
  | maskiere _ _ => exact guard_none_absurd hg rfl
  | prioritaet _ => exact guard_none_absurd hg rfl
  | sendeUnterbrechung _ _ => exact guard_none_absurd hg rfl
  | leiteLeitung _ _ _ => exact guard_none_absurd hg rfl

/-- The abstraction lemma: acceptance of the static analysis gives `WaechterHalten`
    over all ideal runs of the unit. The guard conjunct goes through the frame
    invariant and `pruefeBedarf_gilt`; deadlock freedom is vacuous because the
    elaborated system never blocks; the holder conjunct is vacuous because locks
    stay free. -/
theorem waechterAbstrakt (p : Fragment) (platform : Katalog.Plattform)
    (h : waechterPruefeCode p.code = true) : WaechterHalten (p.einheit platform) := by
  have hfre : p.code.all keinFremdzugriff = true := by
    have h2 := h
    simp only [waechterPruefeCode, Bool.and_eq_true] at h2
    exact h2.1
  have hpruef : ∀ b ∈ p.code, pruefeBedarf p.code b = true := by
    intro b hb
    have h2 := h
    simp only [waechterPruefeCode, Bool.and_eq_true] at h2
    exact List.all_eq_true.mp h2.2 b hb
  refine ⟨?_, ?_, ?_⟩
  · intro ρ hρ t op args hbed
    have hguard : (p.einheit platform).quelltabellen.guard (ρ.zeit.zustand t.val)
        op args := hbed
    obtain ⟨c, b, head, hdemand⟩ := hguard
    have hmem : b ∈ p.code := kopf_mem head
    have hfr := (invariantAlle p platform hfre ρ hρ t.val).1 c
    exact pruefeBedarf_gilt p.code b ((ρ.zeit.zustand t.val).lokal c) hmem hfr
      (hpruef b hmem) op args hdemand
  · intro ρ hρ t
    intro hC
    obtain ⟨C, ⟨c, hcC⟩, hclosed⟩ := hC
    obtain ⟨b, hblock, _⟩ := hclosed c hcC
    exact False.elim hblock
  · intro ρ hρ t l holder hbes
    have hfree := (invariantAlle p platform hfre ρ hρ t.val).2 l
    rw [hfree] at hbes
    cases hbes

/-- COMPLETENESS of the guard analysis on its named decidable fragment: on
    `waechterFragmentCode` every held guard passes the static check. Difficulty:
    schwer. Sketch: on the fragment every guard sits in the linear prefix before
    the first control-flow instruction and every slot it reads is written exactly
    once, before the guard, by a constant write. Induction over the ideal run with
    the frame invariant shows the runtime value at the guard equals the analysed
    constant on every path that reaches the guard with present values: the prefix
    executes in order from the entry cut, the single constant write is the only
    writer, and control cannot skip it. The static hull is then exact at the guard,
    so a held guard implies a passing static check. The fragment shape is exact:
    the witness unit of `NichtAkzeptierteEinheit` lies on the fragment while the
    analysis refuses it. -/
def WaechterFragmentVollstaendigAussage : Prop :=
  ∀ (p : Fragment) (platform : Katalog.Plattform),
    waechterFragmentCode p.code = true → WaechterHalten (p.einheit platform) →
      waechterPruefeCode p.code = true

/-- The fragment statement is about a nonempty set of fragments: the empty unit
    lies on the fragment, its guards hold, and the analysis accepts it. -/
theorem WaechterFragmentVollstaendigAussage.erfuellbar :
    ∃ (p : Fragment) (platform : Katalog.Plattform),
      waechterFragmentCode p.code = true ∧ WaechterHalten (p.einheit platform) ∧
        waechterPruefeCode p.code = true := by
  refine ⟨fragment Ast.Category.unit trivialUnit, Katalog.Plattform.x86_64, ?_, ?_, ?_⟩
  · show waechterFragmentCode (fragment Ast.Category.unit trivialUnit).code = true
    have hcode : (fragment Ast.Category.unit trivialUnit).code =
        [Befehl.starte mainName, Befehl.ende] := rfl
    rw [hcode]
    decide
  · exact (trivialUnit_akzeptiert Katalog.Plattform.x86_64).2.2
  · show waechterPruefeCode (fragment Ast.Category.unit trivialUnit).code = true
    have hcode : (fragment Ast.Category.unit trivialUnit).code =
        [Befehl.starte mainName, Befehl.ende] := rfl
    rw [hcode]
    decide

/-- The fragment statement is load-bearing: the witness unit lies on the fragment
    while the analysis refuses it, so completeness does not hold vacuously. -/
theorem WaechterFragmentVollstaendigAussage.nichtTrivial :
    ∃ (p : Fragment) (platform : Katalog.Plattform),
      waechterFragmentCode p.code = true ∧ waechterPruefeCode p.code = false := by
  refine ⟨fragment Ast.Category.unit textIndexUnit, Katalog.Plattform.x86_64, ?_, ?_⟩
  · show waechterFragmentCode textIndexCode = true
    rw [textIndexUnit_code]
    decide
  · show waechterPruefeCode textIndexCode = false
    rw [textIndexUnit_code]
    decide

end Gabbro.Core.Ziel.Korrektheit.WaechterAnalyse
