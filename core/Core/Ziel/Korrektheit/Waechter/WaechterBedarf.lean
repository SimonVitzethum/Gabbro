/-
  File:      core/Core/Ziel/Korrektheit/Waechter/WaechterBedarf.lean
  Subject:   STATIC DEMAND LEMMAS for the guard analysis: a guard demand read at a
             satisfying frame meets the pinned guard row, because the static hull
             covers the runtime value. One lemma per guard instruction
             (`teilen`, `liesArray`, `textIndex`, `substring`), plus the value-shape
             helper for text reads. These feed `pruefeBedarf_gilt` in
             `WaechterAbstrakt.lean`.
-/
module

public import Core.Ziel.Korrektheit.Waechter.WaechterTransfer
public import Core.Annahme.Waechter

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit.WaechterAnalyse

open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Ast
open Gabbro.Core.Maschine
open Gabbro.Core.Annahme

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

