module

public import Core.Beobachtung.Unentscheidbar.Simulation.Bruecke
public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.BleibtImBlock

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

/-- An instruction preserves the return value exactly. Every instruction the
    translator emits except `.ende` has this property. -/
def ErhaeltRueckgabe (b : Befehl) : Prop :=
  ∀ r, (b.auswerten r).rueckgabe = r.rueckgabe

/-- Every relocatable instruction other than `.ende` preserves the return
    value. -/
theorem verschiebbarNichtEndeErhaeltRueckgabe (b : Befehl)
    (hv : Verschiebbar b) (hne : b ≠ .ende) : ErhaeltRueckgabe b := by
  unfold ErhaeltRueckgabe
  intro r
  cases b <;> simp only [Verschiebbar] at hv
  all_goals
    try contradiction
    try rfl
  · exfalso
    exact hne rfl

/-- One step of a program whose every instruction preserves the return value
    preserves it. -/
theorem schrittErhaeltRueckgabe (blk : List Befehl) (r r' : Rahmen)
    (h : Schritt blk (some r) = some r')
    (hall : ∀ b ∈ blk, ErhaeltRueckgabe b) : r'.rueckgabe = r.rueckgabe := by
  unfold Schritt at h
  cases hget : blk[r.pc]? with
  | none => simp only [hget] at h; cases h
  | some b =>
    simp only [hget] at h
    injection h with hr
    subst r'
    have hbmem : b ∈ blk := by
      exact List.mem_of_getElem? hget
    exact hall b hbmem r

/-- A whole run of such a program preserves the return value. -/
theorem laufErhaeltRueckgabe (blk : List Befehl) (r : Rahmen) (k : Nat) (rk : Rahmen)
    (hrk : (Schritt blk)^[k] (some r) = some rk)
    (hall : ∀ b ∈ blk, ErhaeltRueckgabe b) : rk.rueckgabe = r.rueckgabe := by
  induction k generalizing rk with
  | zero =>
    injection hrk with hr
    subst rk
    rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply'] at hrk
    cases hmid : (Schritt blk)^[k] (some r) with
    | none => simp only [hmid, laufKein] at hrk; cases hrk
    | some rm =>
      have hstep : Schritt blk (some rm) = some rk := by simpa only [hmid] using hrk
      exact (ih rm hmid hall).trans (schrittErhaeltRueckgabe blk rm rk hstep hall)

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation
