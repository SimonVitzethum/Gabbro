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

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation
