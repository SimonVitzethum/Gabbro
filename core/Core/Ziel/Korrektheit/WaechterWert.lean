/-
  File:      core/Core/Ziel/Korrektheit/WaechterWert.lean
  Subject:   VALUE LEMMAS for the joined environments: each static instruction writes exactly
             its analysed constant into its temporary, so the joined lookup covers it.

  These feed the master transfer in `WaechterErhalt.lean`, one lemma per static write.
-/
module

public import Core.Ziel.Korrektheit.WaechterSchritt

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit.WaechterAnalyse

open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Ast

/-- The text-concatenation value satisfies every present text lookup. -/
theorem textConcat_hV (code : List Befehl) (frame : Rahmen) (live : Nat → Bool)
    (dst a b : Nat) (hmem : (Befehl.textConcat dst a b) ∈ code)
    (h : RahmenErfuellt code frame) :
    ∀ (d : Dynamisch),
      (((Befehl.textConcat dst a b).auswerten frame live).temp dst) = some d →
      ∀ (cap : Nat) (t : TextValue cap), d = ⟨.text cap, t⟩ → ∀ L H : Nat,
      umgebungText code dst = some (L, H) → L ≤ t.bytes.size ∧ t.bytes.size ≤ H := by
  intro d hd cap t hdt L H hlook
  cases hleft : (frame.temp dst).bind (wertAls (.text a)) with
  | none =>
    simp only [Befehl.auswerten, Rahmen.schreibe, Function.update_self, eq_self_iff_true,
      if_true, hleft, Option.bind_none] at hd
    cases hd
  | some l =>
    simp only [Befehl.auswerten, Rahmen.schreibe, Function.update_self, eq_self_iff_true,
      if_true, hleft, Option.bind_some] at hd
    cases hright : (frame.temp (dst + 1)).bind (wertAls (.text b)) with
    | none =>
      simp only [hright, Option.bind_none] at hd
      cases hd
    | some r =>
      simp only [hright, Option.bind_some] at hd
      cases hd
      cases hdt
      exact textConcat_wertSat code dst a b hmem l r L H hlook

/-- The substring value satisfies every present text lookup. -/
theorem substring_hV (code : List Befehl) (frame : Rahmen) (live : Nat → Bool)
    (dst capacity : Nat) (hmem : (Befehl.substring dst capacity) ∈ code)
    (h : RahmenErfuellt code frame) :
    ∀ (d : Dynamisch),
      (((Befehl.substring dst capacity).auswerten frame live).temp dst) = some d →
      ∀ (cap : Nat) (t : TextValue cap), d = ⟨.text cap, t⟩ → ∀ L H : Nat,
      umgebungText code dst = some (L, H) → L ≤ t.bytes.size ∧ t.bytes.size ≤ H := by
  intro d hd cap t hdt L H hlook
  cases htext : (frame.temp dst).bind (wertAls (.text capacity)) with
  | none =>
    have htn : (((Befehl.substring dst capacity).auswerten frame live).temp dst) =
        frame.temp dst := by
      simp only [Befehl.auswerten, htext, Rahmen.halt, Id.run]
      rfl
    rw [htn, hdt] at hd
    exact h.2.1 dst _ _ hlook _ hd cap t rfl
  | some text =>
    cases hfirst : frame.zahl (dst + 1) with
    | none =>
      have htn : (((Befehl.substring dst capacity).auswerten frame live).temp dst) =
          frame.temp dst := by
        simp only [Befehl.auswerten, htext, hfirst, Rahmen.halt, Id.run]
        rfl
      rw [htn, hdt] at hd
      exact h.2.1 dst _ _ hlook _ hd cap t rfl
    | some first =>
      cases hlast : frame.zahl (dst + 2) with
      | none =>
        have htn : (((Befehl.substring dst capacity).auswerten frame live).temp dst) =
            frame.temp dst := by
          simp only [Befehl.auswerten, htext, hfirst, hlast, Rahmen.halt, Id.run]
          rfl
        rw [htn, hdt] at hd
        exact h.2.1 dst _ _ hlook _ hd cap t rfl
      | some last =>
        by_cases hok : 0 ≤ first.zahl.wert ∧ first.zahl.wert ≤ last.zahl.wert ∧
            last.zahl.wert ≤ (text.bytes.size : Int)
        case pos =>
          have hdpos : (((Befehl.substring dst capacity).auswerten frame live).temp dst) =
              some ⟨.text capacity, text.slice first.zahl.wert.toNat last.zahl.wert.toNat⟩ := by
            simp only [Befehl.auswerten, htext, hfirst, hlast, if_pos hok, Rahmen.halt, Id.run]
            show (Function.update frame.temp dst
              (some ⟨.text capacity, text.slice first.zahl.wert.toNat last.zahl.wert.toNat⟩ :
                Option Dynamisch)) dst = _
            simp only [Function.update_self]
          rw [hdpos] at hd
          cases hd
          cases hdt
          exact substring_wertSat code dst capacity hmem text
            first.zahl.wert.toNat last.zahl.wert.toNat L H hlook
        case neg =>
          have hdneg : (((Befehl.substring dst capacity).auswerten frame live).temp dst) =
              frame.temp dst := by
            simp only [Befehl.auswerten, htext, hfirst, hlast, if_neg hok, Rahmen.halt, Id.run]
            rfl
          rw [hdneg, hdt] at hd
          exact h.2.1 dst _ _ hlook _ hd cap t rfl

/-- The text-length value satisfies every present integer lookup. -/
theorem textLength_hV (code : List Befehl) (frame : Rahmen) (live : Nat → Bool)
    (dst capacity : Nat) (hmem : (Befehl.textLength dst capacity) ∈ code)
    (h : RahmenErfuellt code frame) :
    ∀ g : Ganzzahl,
      (((Befehl.textLength dst capacity).auswerten frame live).temp dst).bind alsGanzzahl =
        some g →
      ∀ L H : Int, umgebungInt code dst = some (L, H) → L ≤ g.zahl.wert ∧ g.zahl.wert ≤ H := by
  intro g hg L H hlook
  simp only [Befehl.auswerten, Rahmen.schreibe, Function.update_self, eq_self_iff_true, if_true] at hg
  cases hbind : (frame.temp dst).bind (wertAls (.text capacity)) with
  | none =>
    simp only [hbind, Option.bind_none, Option.map_none] at hg
    cases hg
  | some t =>
    simp only [hbind, Option.bind_some, Option.map_some] at hg
    have hgv : (⟨(0 : Int), (capacity : Int), TextValue.lengthValue t⟩ : Ganzzahl) = g := by
      simpa [alsGanzzahl] using hg
    subst hgv
    exact textLength_wertSat code dst capacity hmem t L H hlook

/-- The text-index value satisfies every present integer lookup; halts keep the frame. -/
theorem textIndex_hV (code : List Befehl) (frame : Rahmen) (live : Nat → Bool)
    (dst capacity : Nat) (hmem : (Befehl.textIndex dst capacity) ∈ code)
    (h : RahmenErfuellt code frame) :
    ∀ g : Ganzzahl,
      (((Befehl.textIndex dst capacity).auswerten frame live).temp dst).bind alsGanzzahl =
        some g →
      ∀ L H : Int, umgebungInt code dst = some (L, H) → L ≤ g.zahl.wert ∧ g.zahl.wert ≤ H := by
  intro g hg L H hlook
  cases htext : (frame.temp dst).bind (wertAls (.text capacity)) with
  | none =>
    have htemp : ((Befehl.textIndex dst capacity).auswerten frame live).temp = frame.temp := by
      simp only [Befehl.auswerten, htext, Rahmen.halt, Id.run]
      rfl
    rw [htemp] at hg
    exact h.1 dst _ _ hlook g hg
  | some text =>
    cases hzahl : frame.zahl (dst + 1) with
    | none =>
      have htemp : ((Befehl.textIndex dst capacity).auswerten frame live).temp = frame.temp := by
        simp only [Befehl.auswerten, htext, hzahl, Rahmen.halt, Id.run]
        rfl
      rw [htemp] at hg
      exact h.1 dst _ _ hlook g hg
    | some offset =>
      by_cases hneg : offset.zahl.wert < 0
      · have htemp : ((Befehl.textIndex dst capacity).auswerten frame live).temp =
            frame.temp := by
          simp only [Befehl.auswerten, htext, hzahl, if_pos hneg, Rahmen.halt, Id.run]
          rfl
        rw [htemp] at hg
        exact h.1 dst _ _ hlook g hg
      · cases hbyte : text.bytes[offset.zahl.wert.toNat]? with
        | none =>
          have htemp : ((Befehl.textIndex dst capacity).auswerten frame live).temp =
              frame.temp := by
            simp only [Befehl.auswerten, htext, hzahl, if_neg hneg, hbyte, Rahmen.halt, Id.run]
            rfl
          rw [htemp] at hg
          exact h.1 dst _ _ hlook g hg
        | some byte =>
          have htemp : ((Befehl.textIndex dst capacity).auswerten frame live).temp dst =
              some ⟨.int (0 : Int) 255, byteValue byte⟩ := by
            simp only [Befehl.auswerten, htext, hzahl, if_neg hneg, hbyte, Rahmen.halt,
              Id.run]
            show (Function.update frame.temp dst
              (some ⟨.int (0 : Int) 255, byteValue byte⟩ : Option Dynamisch)) dst = _
            simp only [Function.update_self]
          rw [htemp] at hg
          have hgv : (⟨(0 : Int), 255, byteValue byte⟩ : Ganzzahl) = g := by
            simpa [alsGanzzahl] using hg
          subst hgv
          exact textIndex_wertSat code dst capacity hmem byte L H hlook

/-- The array-read value satisfies every present integer lookup; misses write nothing. -/
theorem liesArray_hV (code : List Befehl) (frame : Rahmen) (live : Nat → Bool)
    (basis count : Nat) (lo hi : Int)
    (hmem : (Befehl.liesArray basis (.int lo hi) count) ∈ code)
    (h : RahmenErfuellt code frame) :
    ∀ g : Ganzzahl,
      (((Befehl.liesArray basis (.int lo hi) count).auswerten frame live).temp basis).bind
        alsGanzzahl = some g →
      ∀ L H : Int, umgebungInt code basis = some (L, H) → L ≤ g.zahl.wert ∧ g.zahl.wert ≤ H := by
  intro g hg L H hlook
  cases htemp : frame.temp basis with
  | none =>
    have hnone : (((Befehl.liesArray basis (.int lo hi) count).auswerten frame live).temp
        basis).bind alsGanzzahl = none := by
      simp only [Befehl.auswerten, htemp, Rahmen.schreibe, Function.update_self,
        eq_self_iff_true, if_true, Option.bind_none, bind, Option.bind, pure]
    rw [hnone] at hg
    cases hg
  | some d =>
    cases hwd : (wertAls (.array (.int lo hi) count) d :
        Option (Vector (Wert (.int lo hi)) count)) with
    | none =>
      have hnone : (((Befehl.liesArray basis (.int lo hi) count).auswerten frame live).temp
          basis).bind alsGanzzahl = none := by
        simp only [Befehl.auswerten, htemp, hwd, Rahmen.schreibe, Function.update_self,
          eq_self_iff_true, if_true, Option.bind_some, Option.bind_none, bind, Option.bind, pure]
      rw [hnone] at hg
      cases hg
    | some values =>
      cases hindex : frame.zahl (basis + 1) with
      | none =>
        have hnone : (((Befehl.liesArray basis (.int lo hi) count).auswerten frame live).temp
            basis).bind alsGanzzahl = none := by
          simp only [Befehl.auswerten, htemp, hwd, hindex, Rahmen.schreibe,
            Function.update_self, eq_self_iff_true, if_true, Option.bind_some, Option.bind_none, bind, Option.bind, pure]
        rw [hnone] at hg
        cases hg
      | some index =>
        by_cases hneg : index.zahl.wert < 0
        case pos =>
          have hnone : (((Befehl.liesArray basis (.int lo hi) count).auswerten frame live).temp
              basis).bind alsGanzzahl = none := by
            simp only [Befehl.auswerten, htemp, hwd, hindex, if_pos hneg, Rahmen.schreibe,
              Function.update_self, eq_self_iff_true, if_true, Option.bind_some, Option.bind_none, bind, Option.bind, pure]
          rw [hnone] at hg
          cases hg
        case neg =>
          by_cases hbound : index.zahl.wert.toNat < count
          case pos =>
            simp only [Befehl.auswerten, htemp, hwd, hindex, if_neg hneg, dif_pos hbound,
              Rahmen.schreibe, Function.update_self, eq_self_iff_true, if_true,
              Option.bind_some, alsGanzzahl, bind, Option.bind, pure] at hg
            cases hg
            let v : Vector (Wert (.int lo hi)) count := values
            exact liesArray_wertSat code basis count lo hi hmem
              (v.get ⟨index.zahl.wert.toNat, hbound⟩) L H hlook
          case neg =>
            have hnone : (((Befehl.liesArray basis (.int lo hi) count).auswerten frame live).temp
                basis).bind alsGanzzahl = none := by
              simp only [Befehl.auswerten, htemp, hwd, hindex, if_neg hneg, dif_neg hbound,
                Rahmen.schreibe, Function.update_self, eq_self_iff_true, if_true,
                Option.bind_some, Option.bind_none, bind, Option.bind, pure]
            rw [hnone] at hg
            cases hg

end Gabbro.Core.Ziel.Korrektheit.WaechterAnalyse
