/-
  File:      core/Core/Ziel/Korrektheit/WaechterTransfer.lean
  Subject:   SATISFACTION of the joined environments: every reachable temporary value lies in
             the joined hull, and every static write produces exactly its analysed constant.

  `TempSatInt`/`TempSatText` state that every present integer (respectively text) value in a
  temporary map lies in the joined interval; `RahmenErfuellt` extends this to saved
  continuation temporaries (restored by returns). The hull lemmas show the joined lookup
  covers every static contribution, and the write lemmas show each static instruction
  produces exactly its contribution. Poisoned slots (unknown writes) make the lookup top,
  hence vacuous.
-/
module

public import Core.Ziel.Korrektheit.Waechter.WaechterAnalyse
public import Core.Ast.Semantik.Runtime.Befehl
public import Core.Ast.Semantik.Runtime.Frame
public import Core.Ast.Aggregate.Runtime

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit.WaechterAnalyse

open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Ast
open Gabbro.Core.Aussenfrage

/-- Every present integer value in the temporary map lies in the joined interval. -/
def TempSatInt (code : List Befehl) (temp : Nat → Option Dynamisch) : Prop :=
  ∀ slot lo hi, umgebungInt code slot = some (lo, hi) →
    ∀ g : Ganzzahl, (temp slot).bind alsGanzzahl = some g → lo ≤ g.zahl.wert ∧ g.zahl.wert ≤ hi

/-- Every present text value in the temporary map has its length in the joined interval. -/
def TempSatText (code : List Befehl) (temp : Nat → Option Dynamisch) : Prop :=
  ∀ slot l h, umgebungText code slot = some (l, h) →
    ∀ d : Dynamisch, temp slot = some d →
      ∀ cap (t : TextValue cap), d = ⟨.text cap, t⟩ → l ≤ t.bytes.size ∧ t.bytes.size ≤ h

/-- A frame satisfies the joined environments, including its saved continuations. -/
def RahmenErfuellt (code : List Befehl) (frame : Rahmen) : Prop :=
  TempSatInt code frame.temp ∧ TempSatText code frame.temp ∧
  ∀ k : Fortsetzung, k ∈ frame.fortsetzungen → TempSatInt code k.temp ∧ TempSatText code k.temp

/-- Unfolding the joined integer hull over a cons cell. -/
theorem huelleInt_cons (b : Befehl) (code : List Befehl) (slot : Nat) :
    huelleInt (b :: code) slot = huelleIntAux (huelleInt code slot) (beitragInt b slot) := rfl

/-- Unfolding the joined text hull over a cons cell. -/
theorem huelleText_cons (b : Befehl) (code : List Befehl) (slot : Nat) :
    huelleText (b :: code) slot = huelleTextAux (huelleText code slot) (beitragText b slot) := rfl

/-- Unfolding the joined integer lookup. -/
theorem umgebungInt_eq (code : List Befehl) (slot : Nat) :
    umgebungInt code slot =
      match slotUnbekanntInt code slot with
      | true => none
      | false => huelleInt code slot := rfl

/-- Unfolding the joined text lookup. -/
theorem umgebungText_eq (code : List Befehl) (slot : Nat) :
    umgebungText code slot =
      match slotUnbekanntText code slot with
      | true => none
      | false => huelleText code slot := rfl

/-- Joining no contribution keeps the hull. -/
theorem huelleIntAux_ohne (acc : Option (Int × Int)) :
    huelleIntAux acc none = acc := rfl

/-- Joining an unknown contribution keeps the hull (poison is tracked separately). -/
theorem huelleIntAux_unbekannt (acc : Option (Int × Int)) :
    huelleIntAux acc (some .unbekannt) = acc := rfl

/-- The hull covers one more interval contribution. -/
theorem huelleIntAux_obere (acc : Option (Int × Int)) (lo hi : Int) :
    ∃ L H, huelleIntAux acc (some (.intervall lo hi)) = some (L, H) ∧ L ≤ lo ∧ hi ≤ H := by
  cases acc with
  | none => exact ⟨lo, hi, rfl, Int.le_refl _, Int.le_refl _⟩
  | some pair =>
    obtain ⟨a, b⟩ := pair
    exact ⟨min a lo, max b hi, rfl, by omega, by omega⟩

/-- The joined integer hull covers every static interval contribution in the code. -/
theorem huelleInt_obere (code : List Befehl) (slot : Nat) (lo hi : Int) (b : Befehl)
    (hb : beitragInt b slot = some (.intervall lo hi)) (hmem : b ∈ code) :
    ∃ L H, huelleInt code slot = some (L, H) ∧ L ≤ lo ∧ hi ≤ H := by
  induction code with
  | nil => exact (List.not_mem_nil hmem).elim
  | cons head tail ih =>
    rw [huelleInt_cons]
    rcases List.mem_cons.mp hmem with rfl | hmem
    · rw [hb]
      exact huelleIntAux_obere _ lo hi
    · obtain ⟨L₀, H₀, hHull, hLo, hHi⟩ := ih hmem
      cases hBeitrag : beitragInt head slot with
      | none =>
        rw [huelleIntAux_ohne]
        exact ⟨L₀, H₀, hHull, hLo, hHi⟩
      | some v =>
        cases v with
        | unbekannt =>
          rw [huelleIntAux_unbekannt]
          exact ⟨L₀, H₀, hHull, hLo, hHi⟩
        | intervall lo' hi' =>
          rw [hHull]
          exact ⟨min L₀ lo', max H₀ hi', rfl, by omega, by omega⟩

/-- An unknown integer write in the code poisons the slot. -/
theorem unbekanntInt_mem (code : List Befehl) (slot : Nat) (b : Befehl)
    (hb : beitragInt b slot = some .unbekannt) (hmem : b ∈ code) :
    slotUnbekanntInt code slot = true := by
  simp only [slotUnbekanntInt, List.any_eq_true]
  refine ⟨b, hmem, ?_⟩
  simp only [hb]

/-- An outside question poisons its answer slot for integers: the answer value is unknown. -/
theorem aussenFrage_poisonInt (code : List Befehl) (ziel : Nat)
    (operation : Gabbro.Core.Katalog.AussenOperation) (args : List Nat)
    (hmem : Befehl.aussen (.frage ziel operation args) ∈ code) :
    slotUnbekanntInt code ziel = true := by
  apply unbekanntInt_mem code ziel _ _ hmem
  simp only [beitragInt, schreibtTemp, List.mem_cons_self, if_true]

/-- A consumed outside answer poisons its target slot for integers. -/
theorem aussenVerbrauche_poisonInt (code : List Befehl) (ziel : Nat)
    (hmem : Befehl.aussen (.verbrauche ziel) ∈ code) :
    slotUnbekanntInt code ziel = true := by
  apply unbekanntInt_mem code ziel _ _ hmem
  simp only [beitragInt, schreibtTemp, List.mem_cons_self, if_true]

/-- A poisoned integer slot has a top lookup. -/
theorem umgebungInt_unbekannt (code : List Befehl) (slot : Nat)
    (h : slotUnbekanntInt code slot = true) : umgebungInt code slot = none := by
  simp only [umgebungInt_eq, h]

/-- A static integer contribution is covered by a present lookup. -/
theorem umgebungInt_beitrag (code : List Befehl) (slot : Nat) (b : Befehl) (lo hi : Int)
    (hmem : b ∈ code) (hb : beitragInt b slot = some (.intervall lo hi))
    (L H : Int) (hlook : umgebungInt code slot = some (L, H)) : L ≤ lo ∧ hi ≤ H := by
  cases hpois : slotUnbekanntInt code slot with
  | true =>
    rw [umgebungInt_unbekannt code slot hpois] at hlook
    cases hlook
  | false =>
    obtain ⟨L₀, H₀, hHull, hLo, hHi⟩ := huelleInt_obere code slot lo hi b hb hmem
    have e1 : huelleInt code slot = some (L, H) := by
      rw [umgebungInt_eq, hpois] at hlook
      exact hlook
    rw [e1] at hHull
    have hPair : L = L₀ ∧ H = H₀ := by simpa using hHull
    obtain ⟨rfl, rfl⟩ := hPair
    exact ⟨hLo, hHi⟩

/-- Joining no text contribution keeps the hull. -/
theorem huelleTextAux_ohne (acc : Option (Nat × Nat)) :
    huelleTextAux acc none = acc := rfl

/-- Joining an unknown text contribution keeps the hull. -/
theorem huelleTextAux_unbekannt (acc : Option (Nat × Nat)) :
    huelleTextAux acc (some .unbekannt) = acc := rfl

/-- The text hull covers one more length contribution. -/
theorem huelleTextAux_obere (acc : Option (Nat × Nat)) (lo hi : Nat) :
    ∃ L H, huelleTextAux acc (some (.laenge lo hi)) = some (L, H) ∧ L ≤ lo ∧ hi ≤ H := by
  cases acc with
  | none => exact ⟨lo, hi, rfl, Nat.le_refl _, Nat.le_refl _⟩
  | some pair =>
    obtain ⟨a, b⟩ := pair
    exact ⟨min a lo, max b hi, rfl, by omega, by omega⟩

/-- The joined text hull covers every static length contribution in the code. -/
theorem huelleText_obere (code : List Befehl) (slot lo hi : Nat) (b : Befehl)
    (hb : beitragText b slot = some (.laenge lo hi)) (hmem : b ∈ code) :
    ∃ L H, huelleText code slot = some (L, H) ∧ L ≤ lo ∧ hi ≤ H := by
  induction code with
  | nil => exact (List.not_mem_nil hmem).elim
  | cons head tail ih =>
    rw [huelleText_cons]
    rcases List.mem_cons.mp hmem with rfl | hmem
    · rw [hb]
      exact huelleTextAux_obere _ lo hi
    · obtain ⟨L₀, H₀, hHull, hLo, hHi⟩ := ih hmem
      cases hBeitrag : beitragText head slot with
      | none =>
        rw [huelleTextAux_ohne]
        exact ⟨L₀, H₀, hHull, hLo, hHi⟩
      | some v =>
        cases v with
        | unbekannt =>
          rw [huelleTextAux_unbekannt]
          exact ⟨L₀, H₀, hHull, hLo, hHi⟩
        | laenge lo' hi' =>
          rw [hHull]
          exact ⟨min L₀ lo', max H₀ hi', rfl, by omega, by omega⟩

/-- An unknown text write in the code poisons the slot. -/
theorem unbekanntText_mem (code : List Befehl) (slot : Nat) (b : Befehl)
    (hb : beitragText b slot = some .unbekannt) (hmem : b ∈ code) :
    slotUnbekanntText code slot = true := by
  simp only [slotUnbekanntText, List.any_eq_true]
  refine ⟨b, hmem, ?_⟩
  simp only [hb]

/-- A poisoned text slot has a top lookup. -/
theorem umgebungText_unbekannt (code : List Befehl) (slot : Nat)
    (h : slotUnbekanntText code slot = true) : umgebungText code slot = none := by
  simp only [umgebungText_eq, h]

/-- An outside question poisons its answer slot for text lengths. -/
theorem aussenFrage_poisonText (code : List Befehl) (ziel : Nat)
    (operation : Gabbro.Core.Katalog.AussenOperation) (args : List Nat)
    (hmem : Befehl.aussen (.frage ziel operation args) ∈ code) :
    slotUnbekanntText code ziel = true := by
  apply unbekanntText_mem code ziel _ _ hmem
  simp only [beitragText, schreibtTemp, List.mem_cons_self, if_true]

/-- A consumed outside answer poisons its target slot for text lengths. -/
theorem aussenVerbrauche_poisonText (code : List Befehl) (ziel : Nat)
    (hmem : Befehl.aussen (.verbrauche ziel) ∈ code) :
    slotUnbekanntText code ziel = true := by
  apply unbekanntText_mem code ziel _ _ hmem
  simp only [beitragText, schreibtTemp, List.mem_cons_self, if_true]

/-- A static text contribution is covered by a present lookup. -/
theorem umgebungText_beitrag (code : List Befehl) (slot : Nat) (b : Befehl) (lo hi : Nat)
    (hmem : b ∈ code) (hb : beitragText b slot = some (.laenge lo hi))
    (L H : Nat) (hlook : umgebungText code slot = some (L, H)) : L ≤ lo ∧ hi ≤ H := by
  cases hpois : slotUnbekanntText code slot with
  | true =>
    rw [umgebungText_unbekannt code slot hpois] at hlook
    cases hlook
  | false =>
    obtain ⟨L₀, H₀, hHull, hLo, hHi⟩ := huelleText_obere code slot lo hi b hb hmem
    have e1 : huelleText code slot = some (L, H) := by
      rw [umgebungText_eq, hpois] at hlook
      exact hlook
    rw [e1] at hHull
    have hPair : L = L₀ ∧ H = H₀ := by simpa using hHull
    obtain ⟨rfl, rfl⟩ := hPair
    exact ⟨hLo, hHi⟩

/-- A literal writes exactly its value. -/
theorem literal_temp (frame : Rahmen) (live : Nat → Bool) (dst val slot : Nat) :
    ((Befehl.literal dst val).auswerten frame live).temp slot =
      if slot = dst then some ⟨.int (val : Int) (val : Int), Zahl.literal (val : Int)⟩
        else frame.temp slot := by
  show (frame.schreibe dst _).temp slot = _
  by_cases heq : slot = dst
  · subst heq
    simp only [Rahmen.schreibe, Function.update_self, if_true]
  · simp only [Rahmen.schreibe, Function.update_of_ne heq]
    rw [if_neg heq]

/-- A negated literal writes exactly its value. -/
theorem negativ_temp (frame : Rahmen) (live : Nat → Bool) (dst betrag slot : Nat) :
    ((Befehl.negativ dst betrag).auswerten frame live).temp slot =
      if slot = dst
        then some ⟨.int (-(betrag : Int)) (-(betrag : Int)), Zahl.literal (-(betrag : Int))⟩
        else frame.temp slot := by
  show (frame.schreibe dst _).temp slot = _
  by_cases heq : slot = dst
  · subst heq
    simp only [Rahmen.schreibe, Function.update_self, if_true]
  · simp only [Rahmen.schreibe, Function.update_of_ne heq]
    rw [if_neg heq]

/-- A literal satisfies every present integer lookup at its slot. -/
theorem literal_wertSat (code : List Befehl) (dst val : Nat)
    (hmem : (Befehl.literal dst val) ∈ code) :
    ∀ g : Ganzzahl,
      ((some ⟨.int (val : Int) (val : Int), Zahl.literal (val : Int)⟩ : Option Dynamisch)).bind
        alsGanzzahl = some g →
      ∀ L H : Int, umgebungInt code dst = some (L, H) → L ≤ g.zahl.wert ∧ g.zahl.wert ≤ H := by
  intro g hg L H hlook
  have hg' : alsGanzzahl (⟨.int (val : Int) (val : Int), Zahl.literal (val : Int)⟩ : Dynamisch) =
      some g := hg
  have hgv : (⟨(val : Int), (val : Int), Zahl.literal (val : Int)⟩ : Ganzzahl) = g := by
    simpa [alsGanzzahl] using hg'
  subst hgv
  have hb : beitragInt (Befehl.literal dst val) dst = some (.intervall (val : Int) (val : Int)) := by
    simp only [beitragInt, eq_self_iff_true, if_true]
  exact umgebungInt_beitrag code dst _ _ _ hmem hb L H hlook

/-- A negated literal satisfies every present integer lookup at its slot. -/
theorem negativ_wertSat (code : List Befehl) (dst betrag : Nat)
    (hmem : (Befehl.negativ dst betrag) ∈ code) :
    ∀ g : Ganzzahl,
      ((some ⟨.int (-(betrag : Int)) (-(betrag : Int)),
        Zahl.literal (-(betrag : Int))⟩ : Option Dynamisch)).bind alsGanzzahl = some g →
      ∀ L H : Int, umgebungInt code dst = some (L, H) → L ≤ g.zahl.wert ∧ g.zahl.wert ≤ H := by
  intro g hg L H hlook
  have hg' : alsGanzzahl (⟨.int (-(betrag : Int)) (-(betrag : Int)),
      Zahl.literal (-(betrag : Int))⟩ : Dynamisch) = some g := hg
  have hgv : (⟨(-(betrag : Int)), (-(betrag : Int)),
      Zahl.literal (-(betrag : Int))⟩ : Ganzzahl) = g := by
    simpa [alsGanzzahl] using hg'
  subst hgv
  have hb : beitragInt (Befehl.negativ dst betrag) dst =
      some (.intervall (-(betrag : Int)) (-(betrag : Int))) := by
    simp only [beitragInt, eq_self_iff_true, if_true]
  exact umgebungInt_beitrag code dst _ _ _ hmem hb L H hlook

/-- A text literal satisfies every present text lookup at its slot. -/
theorem textLiteral_wertSat (code : List Befehl) (dst : Nat) (decoded : List Char)
    (hmem : (Befehl.textLiteral dst decoded) ∈ code) (L H : Nat)
    (hlook : umgebungText code dst = some (L, H)) :
    L ≤ (TextValue.literal decoded).bytes.size ∧
      (TextValue.literal decoded).bytes.size ≤ H := by
  have hb : beitragText (Befehl.textLiteral dst decoded) dst =
      some (.laenge (sourceUtf8 decoded).size (sourceUtf8 decoded).size) := by
    simp only [beitragText, eq_self_iff_true, if_true]
  exact umgebungText_beitrag code dst _ _ _ hmem hb L H hlook

/-- A text concatenation satisfies every present text lookup at its slot. -/
theorem textConcat_wertSat (code : List Befehl) (dst a b : Nat)
    (hmem : (Befehl.textConcat dst a b) ∈ code) (l : TextValue a) (r : TextValue b)
    (L H : Nat) (hlook : umgebungText code dst = some (L, H)) :
    L ≤ (l.concat r).bytes.size ∧ (l.concat r).bytes.size ≤ H := by
  have hb : beitragText (Befehl.textConcat dst a b) dst = some (.laenge 0 (a + b)) := by
    simp only [beitragText, eq_self_iff_true, if_true]
  have hcov := umgebungText_beitrag code dst _ _ _ hmem hb L H hlook
  have hsize : (l.concat r).bytes.size = l.bytes.size + r.bytes.size := by
    show (l.bytes ++ r.bytes).size = _
    rw [ByteArray.size_append]
  have h1 : l.bytes.size ≤ a := l.bound
  have h2 : r.bytes.size ≤ b := r.bound
  omega

/-- A substring satisfies every present text lookup at its slot. -/
theorem substring_wertSat (code : List Befehl) (dst capacity : Nat)
    (hmem : (Befehl.substring dst capacity) ∈ code) (t : TextValue capacity)
    (first last : Nat) (L H : Nat) (hlook : umgebungText code dst = some (L, H)) :
    L ≤ (t.slice first last).bytes.size ∧ (t.slice first last).bytes.size ≤ H := by
  have hb : beitragText (Befehl.substring dst capacity) dst = some (.laenge 0 capacity) := by
    simp only [beitragText, eq_self_iff_true, if_true]
  have hcov := umgebungText_beitrag code dst _ _ _ hmem hb L H hlook
  have hsize : (t.slice first last).bytes.size ≤ capacity := by
    show (t.bytes.extract first last).size ≤ capacity
    rw [ByteArray.size_extract]
    have := t.bound
    omega
  have hnonneg : 0 ≤ (t.slice first last).bytes.size := Nat.zero_le _
  omega

/-- A text length satisfies every present integer lookup at its slot. -/
theorem textLength_wertSat (code : List Befehl) (base capacity : Nat)
    (hmem : (Befehl.textLength base capacity) ∈ code) (t : TextValue capacity)
    (L H : Int) (hlook : umgebungInt code base = some (L, H)) :
    L ≤ (TextValue.lengthValue t).wert ∧ (TextValue.lengthValue t).wert ≤ H := by
  have hb : beitragInt (Befehl.textLength base capacity) base =
      some (.intervall 0 capacity) := by
    simp only [beitragInt, eq_self_iff_true, if_true]
  have hcov := umgebungInt_beitrag code base _ _ _ hmem hb L H hlook
  exact ⟨Int.le_trans hcov.1 (TextValue.lengthValue t).unten,
    Int.le_trans (TextValue.lengthValue t).oben hcov.2⟩

/-- A text index writes a byte and satisfies every present integer lookup at its slot. -/
theorem textIndex_wertSat (code : List Befehl) (base capacity : Nat)
    (hmem : (Befehl.textIndex base capacity) ∈ code) (byte : UInt8)
    (L H : Int) (hlook : umgebungInt code base = some (L, H)) :
    L ≤ (byteValue byte).wert ∧ (byteValue byte).wert ≤ H := by
  have hb : beitragInt (Befehl.textIndex base capacity) base = some (.intervall 0 255) := by
    simp only [beitragInt, eq_self_iff_true, if_true]
  have hcov := umgebungInt_beitrag code base _ _ _ hmem hb L H hlook
  exact ⟨Int.le_trans hcov.1 (byteValue byte).unten, Int.le_trans (byteValue byte).oben hcov.2⟩

/-- An array read of statically typed elements satisfies every present integer lookup. -/
theorem liesArray_wertSat (code : List Befehl) (base count : Nat) (lo hi : Int)
    (hmem : (Befehl.liesArray base (.int lo hi) count) ∈ code) (v : Zahl lo hi)
    (L H : Int) (hlook : umgebungInt code base = some (L, H)) :
    L ≤ v.wert ∧ v.wert ≤ H := by
  have hb : beitragInt (Befehl.liesArray base (.int lo hi) count) base =
      some (.intervall lo hi) := by
    simp only [beitragInt, eq_self_iff_true, if_true]
  have hcov := umgebungInt_beitrag code base _ _ _ hmem hb L H hlook
  exact ⟨Int.le_trans hcov.1 v.unten, Int.le_trans v.oben hcov.2⟩

end Gabbro.Core.Ziel.Korrektheit.WaechterAnalyse
