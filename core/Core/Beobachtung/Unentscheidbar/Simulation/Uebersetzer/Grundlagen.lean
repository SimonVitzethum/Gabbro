module

public import Core.Beobachtung.Unentscheidbar.Simulation.Programm
public import Mathlib.Logic.Function.Basic

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- A natural number as an exact runtime integer: bounds and value coincide,
    so every arithmetic operation on exact inputs stays exact. -/
def natVal (n : Nat) : Dynamisch :=
  ⟨.int (n : Int) (n : Int), Zahl.literal (n : Int)⟩

theorem natValAusgabe (n : Nat) : NatAusgabe (natVal n) = some n := by
  simp only [NatAusgabe, alsGanzzahl, natVal, Zahl.literal]
  rw [if_pos (by omega : (0 : Int) ≤ (n : Int))]
  simp only [Int.toNat_natCast]

/-- A hit on the updated slot reads the new value. Centralises the orientation
    of the `Function.update` conditional. -/
theorem updateHit (f : Nat → Option Dynamisch) (t : Nat) (v : Option Dynamisch) :
    Function.update f t v t = v :=
  Function.update_self t v f

/-- A miss on any other slot reads the old function. -/
theorem updateMiss (f : Nat → Option Dynamisch) (s t : Nat) (v : Option Dynamisch)
    (h : s ≠ t) : Function.update f t v s = f s :=
  Function.update_of_ne h v f

/-- Copy a temporary slot into another slot. The instruction set has no direct
    move: the value travels through the local scope and the scope is restored,
    so the local scope is unchanged and only the target slot changes. -/
def kopie (ziel quelle : Nat) : List Befehl :=
  [.binden nameX quelle, .lesen ziel 0, .blockEnde 1]

theorem kopieLaenge (ziel quelle : Nat) : (kopie ziel quelle).length = 3 := by
  rfl

/-- The simulation lemma for one translated block, in standalone form: the block
    starts at `pc = 0` with the input as an exact integer in slot `eingabe` and
    falls through to `pc = blk.length`. It ends there with the output in slot
    `ausgabe` exactly when `eval c n = some a`; slots below `frei` other than
    `ausgabe` are preserved, as are the local scope, the return value and the
    stop flag. The block contains no `.ende`: it is relocatable, and later steps
    concatenate blocks and append the final bind. -/
def BlockKorrekt (blk : List Befehl) (c : Nat.Partrec.Code) (ein aus frei : Nat) : Prop :=
  ein < frei ∧
    aus < frei ∧
    ein ≠ aus ∧
    ∀ (n : Nat) (r : Rahmen),
      r.pc = 0 →
      r.temp ein = some (natVal n) →
      (∀ (a : Nat),
          Nat.Partrec.Code.eval c n = Part.some a →
          ∃ (k : Nat) (r' : Rahmen),
            (Schritt blk)^[k] (some r) = some r' ∧
              r'.pc = blk.length ∧
              r'.temp aus = some (natVal a) ∧
              (∀ s, s < frei → s ≠ aus → r'.temp s = r.temp s) ∧
              r'.lokale = r.lokale ∧ r'.rueckgabe = r.rueckgabe ∧ r'.stopp = r.stopp) ∧
      ∀ (k : Nat) (r' : Rahmen),
        (Schritt blk)^[k] (some r) = some r' →
        r'.pc = blk.length →
        ∃ (a : Nat),
          Nat.Partrec.Code.eval c n = Part.some a ∧
            r'.temp aus = some (natVal a) ∧
            (∀ s, s < frei → s ≠ aus → r'.temp s = r.temp s) ∧
            r'.lokale = r.lokale ∧ r'.rueckgabe = r.rueckgabe ∧ r'.stopp = r.stopp

/-- Reading a prefix of a concatenated program sees only the first part. -/
theorem getAnhangLinks (A B : List Befehl) (n : Nat) (h : n < A.length) :
    (A ++ B)[n]? = A[n]? := by
  induction A generalizing n with
  | nil =>
    simp only [List.length_nil] at h
    omega
  | cons _ xs ih =>
    cases n with
    | zero => rfl
    | succ n =>
      show (xs ++ B)[n]? = xs[n]?
      exact ih n (by simp only [List.length_cons] at h ⊢; omega)

/-- One step inside the prefix of a concatenated program ignores the suffix. -/
theorem schrittAnhang (A B : List Befehl) (r : Rahmen) (h : r.pc < A.length) :
    Schritt (A ++ B) (some r) = Schritt A (some r) := by
  show (match (A ++ B)[r.pc]? with
      | none => none | some b => some (b.auswerten r)) =
    (match A[r.pc]? with
      | none => none | some b => some (b.auswerten r))
  rw [getAnhangLinks A B r.pc h]

/-- A run that stays inside the prefix agrees with the standalone run. -/
theorem laufAnhang (A B : List Befehl) (r₀ : Rahmen) (k : Nat)
    (h : ∀ j, j < k → ∃ r, (Schritt A)^[j] (some r₀) = some r ∧ r.pc < A.length) :
    (Schritt (A ++ B))^[k] (some r₀) = (Schritt A)^[k] (some r₀) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hIH : ∀ j, j < k → ∃ r, (Schritt A)^[j] (some r₀) = some r ∧ r.pc < A.length :=
      fun j hj => h j (by omega)
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih hIH]
    obtain ⟨r, hr, hlt⟩ := h k (Nat.lt_succ_self k)
    rw [hr]
    exact schrittAnhang A B r hlt

/-- Reading past the end of a program yields nothing. -/
theorem getLenKein (l : List Befehl) (n : Nat) (h : l.length ≤ n) :
    l[n]? = none := by
  induction l generalizing n with
  | nil => rfl
  | cons _ xs ih =>
    cases n with
    | zero =>
      simp only [List.length_cons] at h
      omega
    | succ n =>
      show xs[n]? = none
      exact ih n (by simp only [List.length_cons] at h ⊢; omega)

/-- A frame past the last instruction has no successor: the run stops. -/
theorem schrittAmEnde (blk : List Befehl) (r : Rahmen) (h : r.pc = blk.length) :
    Schritt blk (some r) = none := by
  have hget : blk[r.pc]? = none := h ▸ getLenKein blk blk.length (Nat.le_refl _)
  show (match blk[r.pc]? with | none => none | some b => some (b.auswerten r)) = none
  rw [hget]

/-- The failed run stays failed. -/
theorem laufKein (blk : List Befehl) (t : Nat) :
    (Schritt blk)^[t] none = none := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have h0 : Schritt blk none = none := rfl
    rw [Function.iterate_succ_apply, h0, ih]

/-- Extending a failed run keeps it failed. -/
theorem laufVerlaengertKein (blk : List Befehl) (r : Rahmen) (j t : Nat)
    (h : (Schritt blk)^[j] (some r) = none) :
    (Schritt blk)^[j + t] (some r) = none := by
  rw [show j + t = t + j by omega, Function.iterate_add_apply, h]
  exact laufKein blk t

/-- A run that has reached the end stays dead: no later step count reaches
    a state again. Past the end the run dies, so a later arrival contradicts
    determinism. Applied twice, this rules out any second arrival time. -/
theorem laufStirbtNach (blk : List Befehl) (r₀ : Rahmen) (k kRef : Nat)
    (r' rRef : Rahmen) (hk : (Schritt blk)^[k] (some r₀) = some r')
    (hpc : r'.pc = blk.length) (hkRef : (Schritt blk)^[kRef] (some r₀) = some rRef)
    (hlt : k < kRef) : False := by
  have hnone : Schritt blk (some r') = none := schrittAmEnde blk r' hpc
  have h1 : (Schritt blk)^[1] (some r') = none := hnone
  have hle : k + 1 ≤ kRef := Nat.succ_le_of_lt hlt
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hle
  have eKt : (Schritt blk)^[(k + 1) + t] (some r₀) =
      (Schritt blk)^[t] ((Schritt blk)^[1] ((Schritt blk)^[k] (some r₀))) := by
    have e1 : (Schritt blk)^[k + 1] (some r₀) =
        (Schritt blk)^[1] ((Schritt blk)^[k] (some r₀)) := by
      rw [show (k + 1 : Nat) = 1 + k from Nat.add_comm k 1, Function.iterate_add_apply]
    have e2 : (Schritt blk)^[(k + 1) + t] (some r₀) =
        (Schritt blk)^[t] ((Schritt blk)^[k + 1] (some r₀)) := by
      rw [show ((k + 1) + t : Nat) = t + (k + 1) from Nat.add_comm (k + 1) t,
        Function.iterate_add_apply]
    rw [e2, e1]
  rw [eKt, hk, h1, laufKein] at hkRef
  cases hkRef

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
