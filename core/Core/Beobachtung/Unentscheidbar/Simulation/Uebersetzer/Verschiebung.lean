module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Grundlagen

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- Shift a frame's program counter by a fixed base. All jumps in the
    translator are relative, so running a block at a shifted base behaves as
    running it at zero and shifting the resulting counters back. -/
def mitPc (p : Nat) (r : Rahmen) : Rahmen :=
  { r with pc := p + r.pc }

/-- The instructions the translator emits. Every one of them touches the
    program counter only by adding a constant, or (for the backward jump) by
    subtracting a constant not larger than the counter. -/
def Verschiebbar (b : Befehl) : Prop :=
  match b with
  | .literal _ _ | .binaer _ _ | .binden _ _ | .wahrheitswert _ _
  | .lesen _ _ | .negativ _ _ | .negieren _ | .verneinen _ | .teilen _
  | .vergleichen _ _ | .springeWenn _ _ _ | .zuweisen _ _ _
  | .springe _ | .blockEnde _ | .zurueckSprung _ | .ende => True
  | _ => False

/-- Evaluation of a translator instruction commutes with a program-counter
    shift. The backward jump needs its distance not to exceed the counter. -/
theorem auswertenMitPc (p : Nat) (b : Befehl) (r : Rahmen)
    (hv : Verschiebbar b)
    (hz : ∀ d, b = .zurueckSprung d → d ≤ r.pc) :
    b.auswerten (mitPc p r) = mitPc p (b.auswerten r) := by
  cases b with
  | literal z v => simp only [Befehl.auswerten, Rahmen.schreibe, Rahmen.zahl, mitPc, Nat.add_assoc]
  | binaer op l => simp only [Befehl.auswerten, Rahmen.schreibe, Rahmen.zahl, mitPc, Nat.add_assoc]
  | binden n q => simp only [Befehl.auswerten, mitPc, Nat.add_assoc]
  | wahrheitswert z v => simp only [Befehl.auswerten, Rahmen.schreibe, Rahmen.zahl, mitPc, Nat.add_assoc]
  | lesen z i => simp only [Befehl.auswerten, Rahmen.schreibe, Rahmen.zahl, mitPc, Nat.add_assoc]
  | negativ z m => simp only [Befehl.auswerten, Rahmen.schreibe, Rahmen.zahl, mitPc, Nat.add_assoc]
  | negieren z => simp only [Befehl.auswerten, Rahmen.schreibe, Rahmen.zahl, mitPc, Nat.add_assoc]
  | verneinen z => simp only [Befehl.auswerten, Rahmen.schreibe, Rahmen.zahl, mitPc, Nat.add_assoc]
  | teilen l => simp only [Befehl.auswerten, Rahmen.schreibe, Rahmen.zahl, mitPc, Nat.add_assoc]
  | vergleichen op l => simp only [Befehl.auswerten, Rahmen.schreibe, Rahmen.zahl, mitPc, Nat.add_assoc]
  | zuweisen q i t => simp only [Befehl.auswerten, mitPc, Nat.add_assoc]
  | springe d => simp only [Befehl.auswerten, mitPc, Nat.add_assoc]
  | blockEnde c => simp only [Befehl.auswerten, mitPc, Nat.add_assoc]
  | ende => simp only [Befehl.auswerten, mitPc]
  | springeWenn q wv d =>
    by_cases hc : (r.temp q).bind alsBoolean = some wv <;>
      simp only [Befehl.auswerten, mitPc, Nat.add_assoc, hc]
  | zurueckSprung d =>
    have hpc : (p + r.pc) - d = p + (r.pc - d) := by
      have hd : d ≤ r.pc := hz d rfl
      omega
    simp only [Befehl.auswerten, mitPc, hpc]
  | _ => cases hv

/-- A program made only of relocatable instructions, whose backward jumps stay
    inside the program. -/
def VerschiebbaresProgramm (blk : List Befehl) : Prop :=
  ∀ j, j < blk.length → ∃ b, blk[j]? = some b ∧ Verschiebbar b ∧
    (∀ d, b = .zurueckSprung d → d ≤ j)

/-- Reading a program at its own prefix offset sees the middle part. -/
theorem getNachPrefix (pre mid : List Befehl) (j : Nat) (hj : j < mid.length) :
    (pre ++ mid)[pre.length + j]? = mid[j]? := by
  induction pre with
  | nil => simp
  | cons x xs ih =>
    simp only [List.length_cons, List.cons_append, List.getElem?_cons_succ]
    rw [show List.length xs + 1 + j = (List.length xs + j) + 1 by omega]
    exact ih

/-- One step of a relocated block inside a concatenation agrees with the step
    of the block at base zero, lifted by the prefix length. -/
theorem schrittMitPcBei (pre mid post : List Befehl) (hv : VerschiebbaresProgramm mid)
    (r : Rahmen) (hlt : r.pc < mid.length) :
    Schritt (pre ++ mid ++ post) (some (mitPc pre.length r)) =
      match Schritt mid (some r) with
      | none => none
      | some r' => some (mitPc pre.length r') := by
  obtain ⟨b, hb, hvb, hzd⟩ := hv r.pc hlt
  have hgetConcat : (pre ++ mid ++ post)[pre.length + r.pc]? = some b := by
    rw [getAnhangLinks (pre ++ mid) post (pre.length + r.pc)]
    · exact (getNachPrefix pre mid r.pc hlt).trans hb
    · simp only [List.length_append]
      omega
  have hzb : ∀ d, b = .zurueckSprung d → d ≤ (mitPc pre.length r).pc := by
    intro d hd
    have hd0 : d ≤ r.pc := hzd d hd
    simp only [mitPc]
    omega
  have hgetConcat' : (pre ++ mid ++ post)[(mitPc pre.length r).pc]? = some b := by
    simpa only [mitPc] using hgetConcat
  have e2 : b.auswerten (mitPc pre.length r) = mitPc pre.length (b.auswerten r) :=
    auswertenMitPc pre.length b r hvb hzd
  simp only [Schritt, hgetConcat', hb]
  rw [e2]

/-- A whole relocation of a run that stays below the block length. -/
theorem laufMitPc (pre mid post : List Befehl) (hv : VerschiebbaresProgramm mid)
    (r : Rahmen) (k : Nat)
    (hbleib : ∀ j, j < k → ∃ rj, (Schritt mid)^[j] (some r) = some rj ∧ rj.pc < mid.length) :
    (Schritt (pre ++ mid ++ post))^[k] (some (mitPc pre.length r)) =
      match (Schritt mid)^[k] (some r) with
      | none => none
      | some r' => some (mitPc pre.length r') := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hIH : ∀ j, j < k → ∃ rj, (Schritt mid)^[j] (some r) = some rj ∧ rj.pc < mid.length :=
      fun j hj => hbleib j (by omega)
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih hIH]
    obtain ⟨rj, hrj, hlt⟩ := hbleib k (Nat.lt_succ_self k)
    rw [hrj]
    exact schrittMitPcBei pre mid post hv rj hlt

/-- A run that survives until step k has a frame at every earlier step. -/
theorem laufHatZwischen (blk : List Befehl) (r : Rahmen) (k j : Nat) (rk : Rahmen)
    (hrk : (Schritt blk)^[k] (some r) = some rk) (hj : j ≤ k) :
    ∃ rj, (Schritt blk)^[j] (some r) = some rj := by
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hj
  have hrk' : (Schritt blk)^[t] ((Schritt blk)^[j] (some r)) = some rk := by
    rw [← Function.iterate_add_apply]
    rw [show t + j = k by omega]
    exact hrk
  cases hstep : (Schritt blk)^[j] (some r) with
  | none => rw [hstep, laufKein] at hrk'; cases hrk'
  | some rj => exact ⟨rj, rfl⟩

/-- Before its first arrival at the program end, a successful run stays
    strictly below the program length. -/
theorem laufBleibtVorEnde (blk : List Befehl) (r : Rahmen) (k : Nat) (rk : Rahmen)
    (hrk : (Schritt blk)^[k] (some r) = some rk) (hpck : rk.pc = blk.length) :
    ∀ j, j < k → ∃ rj, (Schritt blk)^[j] (some r) = some rj ∧ rj.pc < blk.length := by
  intro j hj
  obtain ⟨rj, hrj⟩ := laufHatZwischen blk r k j rk hrk (Nat.le_of_lt hj)
  refine ⟨rj, hrj, ?_⟩
  by_contra hnlt
  have hge : blk.length ≤ rj.pc := Nat.le_of_not_gt hnlt
  have hnone : Schritt blk (some rj) = none := by
    have hget : blk[rj.pc]? = none := getLenKein blk rj.pc hge
    simp only [Schritt, hget]
  have hjsucc : j + 1 ≤ k := Nat.succ_le_of_lt hj
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hjsucc
  have hrk' : (Schritt blk)^[t] ((Schritt blk)^[1] ((Schritt blk)^[j] (some r))) = some rk := by
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply]
    rw [show t + 1 + j = k by omega]
    exact hrk
  have h1 : (Schritt blk)^[1] (some rj) = none := by simpa using hnone
  rw [hrj, h1, laufKein] at hrk'
  cases hrk'

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
