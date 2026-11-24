module

public import Core.Beobachtung.Unentscheidbar.Simulation.Kodierung
public import Mathlib.Computability.PartrecCode

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Text
open Nat.Partrec.Code

/-- A fixed well-spelled local name; the runtime ignores the spelling. -/
def nameX : Identifier := ⟨['x'], by
  refine ⟨'x', [], rfl, ?_, ?_⟩
  · simp only [isNameStart, isLetter]
    exact Or.inl (Or.inl ⟨by decide, by decide⟩)
  · intro a ha
    simp only [List.mem_nil_iff] at ha⟩

/-- The straight-line program for a constant: write the value, move it to the
    head local, and finish. -/
def progZahl (a : Nat) : List Befehl :=
  [.literal 0 a, .binden nameX 0, .ende]

def frameZahl1 (a n : Nat) : Rahmen :=
  let r := startVon n
  let v : Option Dynamisch := some ⟨.int (a : Int) (a : Int), Zahl.literal (a : Int)⟩
  { r with pc := 1, temp := Function.update r.temp 0 v }

def frameZahl2 (a n : Nat) : Rahmen :=
  let r := frameZahl1 a n
  { r with pc := 2, lokale := r.temp 0 :: r.lokale }

def frameZahl3 (a n : Nat) : Rahmen :=
  let r := frameZahl2 a n
  { r with rueckgabe := r.lokale.head?.join, stopp := some .fertig }

theorem schrittZahl0 (a n : Nat) :
    Schritt (progZahl a) (some (startVon n)) = some (frameZahl1 a n) := by
  rfl

theorem schrittZahl1 (a n : Nat) :
    Schritt (progZahl a) (some (frameZahl1 a n)) = some (frameZahl2 a n) := by
  rfl

theorem schrittZahl2 (a n : Nat) :
    Schritt (progZahl a) (some (frameZahl2 a n)) = some (frameZahl3 a n) := by
  rfl

theorem schrittZahl3 (a n : Nat) :
    Schritt (progZahl a) (some (frameZahl3 a n)) = some (frameZahl3 a n) := by
  rfl

theorem frameZahl3_rueckgabe (a n : Nat) : (frameZahl3 a n).rueckgabe =
    some ⟨.int (a : Int) (a : Int), Zahl.literal (a : Int)⟩ := by
  rfl

theorem schrittZahlNone (a : Nat) : Schritt (progZahl a) none = none := by
  rfl

theorem natAusgabeZahl (a : Nat) :
    NatAusgabe (⟨.int (a : Int) (a : Int), Zahl.literal (a : Int)⟩ : Dynamisch) = some a := by
  simp only [NatAusgabe, alsGanzzahl, Zahl.literal]
  rw [if_pos (by omega : (0 : Int) ≤ (a : Int))]
  simp only [Int.toNat_natCast]

theorem iterateZahl0 (a n : Nat) :
    (Schritt (progZahl a))^[0] (some (startVon n)) = some (startVon n) := by
  rfl

theorem iterateZahl1 (a n : Nat) :
    (Schritt (progZahl a))^[1] (some (startVon n)) = some (frameZahl1 a n) := by
  change Schritt (progZahl a) (some (startVon n)) = _
  exact schrittZahl0 a n

theorem iterateZahl2 (a n : Nat) :
    (Schritt (progZahl a))^[2] (some (startVon n)) = some (frameZahl2 a n) := by
  change Schritt (progZahl a) (Schritt (progZahl a) (some (startVon n))) = _
  rw [schrittZahl0, schrittZahl1]

theorem iterateZahl_ge3 (a n t : Nat) :
    (Schritt (progZahl a))^[t] (some (frameZahl3 a n)) = some (frameZahl3 a n) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply]
    rw [schrittZahl3, ih]

theorem iterateZahl3 (a n t : Nat) :
    (Schritt (progZahl a))^[3 + t] (some (startVon n)) = some (frameZahl3 a n) := by
  rw [show 3 + t = t + 3 by omega, Function.iterate_add_apply]
  rw [show (Schritt (progZahl a))^[3] (some (startVon n)) = some (frameZahl3 a n) by
    change Schritt (progZahl a) (Schritt (progZahl a) (Schritt (progZahl a) (some (startVon n)))) = _
    rw [schrittZahl0, schrittZahl1, schrittZahl2]]
  exact iterateZahl_ge3 a n t

theorem haeltMit_progZahl_iff (a n b : Nat) :
    HaeltMit (progZahl a) (startVon n) b ↔ b = a := by
  constructor
  · rintro ⟨r, ⟨k, hk⟩, hout⟩
    rcases k with _ | _ | _ | t
    · rw [iterateZahl0] at hk
      injection hk with hr
      subst r
      cases hout
    · rw [iterateZahl1] at hk
      injection hk with hr
      subst r
      cases hout
    · rw [iterateZahl2] at hk
      injection hk with hr
      subst r
      cases hout
    · have hk' : (Schritt (progZahl a))^[3 + t] (some (startVon n)) = some r := by
        simpa only [show t + 1 + 1 + 1 = 3 + t by omega] using hk
      rw [iterateZahl3] at hk'
      injection hk' with hr
      subst r
      rw [frameZahl3_rueckgabe] at hout
      change NatAusgabe (⟨.int (a : Int) (a : Int), Zahl.literal (a : Int)⟩ : Dynamisch) = some b at hout
      rw [natAusgabeZahl] at hout
      exact Option.some.inj hout.symm
  · intro hb
    subst b
    refine ⟨frameZahl3 a n, ⟨3, ?_⟩, ?_⟩
    · exact show (Schritt (progZahl a))^[3] (some (startVon n)) = some (frameZahl3 a n) by
        change Schritt (progZahl a) (Schritt (progZahl a) (Schritt (progZahl a) (some (startVon n)))) = _
        rw [schrittZahl0, schrittZahl1, schrittZahl2]
    · rw [frameZahl3_rueckgabe a n]
      change NatAusgabe (⟨.int (a : Int) (a : Int), Zahl.literal (a : Int)⟩ : Dynamisch) = some a
      exact natAusgabeZahl a

/-- Successor adds one to the input in place, then finishes as above. -/
def progSucc : List Befehl :=
  [.literal 1 1, .binaer .add 0, .binden nameX 0, .ende]

def frameSucc1 (n : Nat) : Rahmen :=
  let r := startVon n
  let v : Option Dynamisch := some ⟨.int (1 : Int) (1 : Int), Zahl.literal 1⟩
  { r with pc := 1, temp := Function.update r.temp 1 v }

theorem schrittSucc0 (n : Nat) :
    Schritt progSucc (some (startVon n)) = some (frameSucc1 n) := by
  rfl

def frameSucc2 (n : Nat) : Rahmen :=
  let r := frameSucc1 n
  let v : Option Dynamisch := some
    (Ganzzahl.pack ⟨_, _, Arith.auswerten .add (Zahl.literal (n : Int)) (Zahl.literal 1)⟩)
  { r with pc := 2, temp := Function.update r.temp 0 v }

theorem schrittSucc1 (n : Nat) :
    Schritt progSucc (some (frameSucc1 n)) = some (frameSucc2 n) := by
  rfl

theorem natAusgabeSucc (n : Nat) : NatAusgabe
    (Ganzzahl.pack ⟨_, _, Arith.auswerten .add (Zahl.literal (n : Int)) (Zahl.literal 1)⟩) =
      some (n + 1) := by
  simp only [NatAusgabe, alsGanzzahl, Ganzzahl.pack, Arith.auswerten, Zahl.literal]
  rw [show (n : Int) + 1 = ((n + 1 : Nat) : Int) by omega]
  rw [if_pos (by omega : (0 : Int) ≤ ((n + 1 : Nat) : Int))]
  simp only [Int.toNat_natCast]

def frameSucc3 (n : Nat) : Rahmen :=
  let r := frameSucc2 n
  { r with pc := 3, lokale := r.temp 0 :: r.lokale }

def frameSucc4 (n : Nat) : Rahmen :=
  let r := frameSucc3 n
  { r with rueckgabe := r.lokale.head?.join, stopp := some .fertig }

theorem schrittSucc2 (n : Nat) :
    Schritt progSucc (some (frameSucc2 n)) = some (frameSucc3 n) := by
  rfl

theorem schrittSucc3 (n : Nat) :
    Schritt progSucc (some (frameSucc3 n)) = some (frameSucc4 n) := by
  rfl

theorem schrittSucc4 (n : Nat) :
    Schritt progSucc (some (frameSucc4 n)) = some (frameSucc4 n) := by
  rfl

theorem frameSucc4_rueckgabe (n : Nat) : (frameSucc4 n).rueckgabe =
    Ganzzahl.pack ⟨_, _, Arith.auswerten .add (Zahl.literal (n : Int)) (Zahl.literal 1)⟩ := by
  rfl

theorem iterateSucc0 (n : Nat) :
    (Schritt progSucc)^[0] (some (startVon n)) = some (startVon n) := by
  rfl

theorem iterateSucc1 (n : Nat) :
    (Schritt progSucc)^[1] (some (startVon n)) = some (frameSucc1 n) := by
  change Schritt progSucc (some (startVon n)) = _
  exact schrittSucc0 n

theorem iterateSucc2 (n : Nat) :
    (Schritt progSucc)^[2] (some (startVon n)) = some (frameSucc2 n) := by
  change Schritt progSucc (Schritt progSucc (some (startVon n))) = _
  rw [schrittSucc0, schrittSucc1]

theorem iterateSucc3 (n : Nat) :
    (Schritt progSucc)^[3] (some (startVon n)) = some (frameSucc3 n) := by
  change Schritt progSucc (Schritt progSucc (Schritt progSucc (some (startVon n)))) = _
  rw [schrittSucc0, schrittSucc1, schrittSucc2]

theorem iterateSucc_ge4 (n t : Nat) :
    (Schritt progSucc)^[t] (some (frameSucc4 n)) = some (frameSucc4 n) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply]
    rw [schrittSucc4, ih]

theorem iterateSucc4 (n t : Nat) :
    (Schritt progSucc)^[4 + t] (some (startVon n)) = some (frameSucc4 n) := by
  rw [show 4 + t = t + 4 by omega, Function.iterate_add_apply]
  rw [show (Schritt progSucc)^[4] (some (startVon n)) = some (frameSucc4 n) by
    change Schritt progSucc (Schritt progSucc (Schritt progSucc (Schritt progSucc (some (startVon n))))) = _
    rw [schrittSucc0, schrittSucc1, schrittSucc2, schrittSucc3]]
  exact iterateSucc_ge4 n t

theorem haeltMit_progSucc_iff (n b : Nat) :
    HaeltMit progSucc (startVon n) b ↔ b = n + 1 := by
  constructor
  · rintro ⟨r, ⟨k, hk⟩, hout⟩
    rcases k with _ | _ | _ | _ | t
    · rw [iterateSucc0] at hk
      injection hk with hr
      subst r
      cases hout
    · rw [iterateSucc1] at hk
      injection hk with hr
      subst r
      cases hout
    · rw [iterateSucc2] at hk
      injection hk with hr
      subst r
      cases hout
    · rw [iterateSucc3] at hk
      injection hk with hr
      subst r
      cases hout
    · have hk' : (Schritt progSucc)^[4 + t] (some (startVon n)) = some r := by
        simpa only [show t + 1 + 1 + 1 + 1 = 4 + t by omega] using hk
      rw [iterateSucc4] at hk'
      injection hk' with hr
      subst r
      rw [frameSucc4_rueckgabe] at hout
      change NatAusgabe
        (Ganzzahl.pack ⟨_, _, Arith.auswerten .add (Zahl.literal (n : Int)) (Zahl.literal 1)⟩) = some b at hout
      rw [natAusgabeSucc] at hout
      exact Option.some.inj hout.symm
  · intro hb
    subst b
    refine ⟨frameSucc4 n, ⟨4, ?_⟩, ?_⟩
    · change Schritt progSucc (Schritt progSucc (Schritt progSucc (Schritt progSucc (some (startVon n))))) = _
      rw [schrittSucc0, schrittSucc1, schrittSucc2, schrittSucc3]
    · rw [frameSucc4_rueckgabe n]
      change NatAusgabe
        (Ganzzahl.pack ⟨_, _, Arith.auswerten .add (Zahl.literal (n : Int)) (Zahl.literal 1)⟩) = some (n + 1)
      exact natAusgabeSucc n

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation
