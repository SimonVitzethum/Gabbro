module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Kette

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- A block never jumps from an instruction inside it to a counter past its end.
    Forward jumps of a translator block land on a later instruction of the same
    block and the fall-through lands exactly on the end. -/
def BleibtImBlock (blk : List Befehl) : Prop :=
  ∀ (r : Rahmen) (b : Befehl), r.pc < blk.length → blk[r.pc]? = some b →
    (b.auswerten r).pc ≤ blk.length

/-- One relocated step agrees with the standalone step for every counter value:
    inside the block by relocation, at or past its end both runs stop. -/
theorem schrittMitPcTotal (pre mid : List Befehl) (hv : VerschiebbaresProgramm mid)
    (r : Rahmen) :
    Schritt (pre ++ mid) (some (mitPc pre.length r)) =
      match Schritt mid (some r) with
      | none => none
      | some r' => some (mitPc pre.length r') := by
  by_cases hlt : r.pc < mid.length
  · simpa only [List.append_nil] using schrittMitPcBei pre mid [] hv r hlt
  · have hpcGe : mid.length ≤ r.pc := Nat.le_of_not_gt hlt
    have hnoneMid : Schritt mid (some r) = none := by
      have hget : mid[r.pc]? = none := getLenKein mid r.pc hpcGe
      show (match mid[r.pc]? with | none => none | some b => some (b.auswerten r)) = none
      rw [hget]
    have hpcCompGe : (pre ++ mid).length ≤ (mitPc pre.length r).pc := by
      simp only [mitPc, List.length_append]
      omega
    have hnoneComp : Schritt (pre ++ mid) (some (mitPc pre.length r)) = none := by
      have hget : (pre ++ mid)[(mitPc pre.length r).pc]? = none := getLenKein _ _ hpcCompGe
      show (match (pre ++ mid)[(mitPc pre.length r).pc]? with
        | none => none | some b => some (b.auswerten (mitPc pre.length r))) = none
      rw [hget]
    rw [hnoneMid, hnoneComp]
    rfl

/-- A whole relocated run agrees with the standalone run without a stay-below
    premise: once the standalone run reaches its end both runs stop. -/
theorem laufMitPcTotal (pre mid : List Befehl) (hv : VerschiebbaresProgramm mid)
    (r : Rahmen) (t : Nat) :
    (Schritt (pre ++ mid))^[t] (some (mitPc pre.length r)) =
      match (Schritt mid)^[t] (some r) with
      | none => none
      | some r' => some (mitPc pre.length r') := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    cases h : (Schritt mid)^[t] (some r) with
    | none =>
      rw [show (Schritt mid)^[Nat.succ t] (some r) = none by
        rw [Function.iterate_succ_apply', h]
        rfl]
      rfl
    | some rj =>
      rw [show (Schritt mid)^[Nat.succ t] (some r) = Schritt mid (some rj) by
        rw [Function.iterate_succ_apply', h]]
      exact schrittMitPcTotal pre mid hv rj

/-- A composite run reaching the overall end from a shifted entry determines a
    standalone run of the middle block reaching its end. -/
theorem rueckMitPc (pre mid : List Befehl) (hv : VerschiebbaresProgramm mid)
    (r0 : Rahmen) (t : Nat) (rEnd : Rahmen)
    (hcomp : (Schritt (pre ++ mid))^[t] (some (mitPc pre.length r0)) = some rEnd)
    (hpcEnd : rEnd.pc = pre.length + mid.length) :
    ∃ rB, (Schritt mid)^[t] (some r0) = some rB ∧ rB.pc = mid.length ∧
      rEnd = mitPc pre.length rB := by
  have ht := laufMitPcTotal pre mid hv r0 t
  rw [hcomp] at ht
  cases hstand : (Schritt mid)^[t] (some r0) with
  | none =>
    simp only [hstand] at ht
    cases ht
  | some rB =>
    have hEq : rEnd = mitPc pre.length rB := Option.some.inj (by simpa only [hstand] using ht)
    refine ⟨rB, hstand, ?_, hEq⟩
    have hp : (mitPc pre.length rB).pc = rEnd.pc := by rw [← hEq]
    simp only [mitPc] at hp
    omega

/-- The unique intermediate arrival of a composite run at the block boundary.
    From a run that reaches the overall end, take the first counter at or beyond
    the first block's length: `BleibtImBlock` rules out an overshoot, so it is
    exactly the boundary, and before it the run is still inside the first block.
    Prefix agreement then turns it into an arrival of the standalone first block.
    Uniqueness follows from `laufStirbtNach` on the first block; blockKette uses
    it to identify any other arrival with this one. -/
theorem randAusEndePrefix (blkA blkB : List Befehl) (hlocal : BleibtImBlock blkA)
    (hlenA : 0 < blkA.length) (hlenB : 0 < blkB.length)
    (r : Rahmen) (k : Nat) (r' : Rahmen) (hrpc : r.pc = 0)
    (hk : (Schritt (blkA ++ blkB))^[k] (some r) = some r')
    (hpcEnd : r'.pc = (blkA ++ blkB).length) :
    ∃ j rA, j ≤ k ∧ (Schritt blkA)^[j] (some r) = some rA ∧ rA.pc = blkA.length := by
  let Q : Nat → Prop := fun s =>
    ∃ rs, s ≤ k ∧ (Schritt (blkA ++ blkB))^[s] (some r) = some rs ∧ blkA.length ≤ rs.pc
  have hQ : ∃ s, Q s := by
    refine ⟨k, r', le_rfl, hk, ?_⟩
    rw [hpcEnd, List.length_append]
    omega
  let j0 := Nat.find hQ
  have hspec := Nat.find_spec hQ
  rcases hspec with ⟨rJ, hj0k, hrunJ, hgeJ⟩
  have hkle : ∀ s, s < j0 → ∀ rs,
      (Schritt (blkA ++ blkB))^[s] (some r) = some rs → rs.pc < blkA.length := by
    intro s hs rs hrs
    have hnotQ : ¬ Q s := Nat.find_min hQ hs
    by_contra hge
    exact hnotQ ⟨rs, by omega, hrs, Nat.le_of_not_gt hge⟩
  have hEqJ : rJ.pc = blkA.length := by
    by_contra hne
    have hgtJ : blkA.length < rJ.pc := Nat.lt_of_le_of_ne hgeJ hne
    cases hj0 with
    | zero =>
      rw [hrunJ, hrpc] at hgtJ
      omega
    | succ j1 =>
      have hj1k : j1 ≤ k := by omega
      obtain ⟨r1, hrun1⟩ := laufHatZwischen (blkA ++ blkB) r k j1 r' hk hj1k
      have hlt1 : r1.pc < blkA.length := hkle j1 (Nat.lt_succ_self j1) r1 hrun1
      have hopt : ∃ b, blkA[r1.pc]? = some b := by
        cases hopt' : blkA[r1.pc]? with
        | none =>
          have hgetC : (blkA ++ blkB)[r1.pc]? = none := by
            rw [getAnhangLinks blkA blkB r1.pc hlt1]
            exact hopt'
          have hnone : Schritt (blkA ++ blkB) (some r1) = none := by
            show (match (blkA ++ blkB)[r1.pc]? with | none => none | some b => some (b.auswerten r1)) = none
            rw [hgetC]
          have hstep : (Schritt (blkA ++ blkB))^[Nat.succ j1] (some r) = none := by
            rw [Function.iterate_succ_apply', hrun1, hnone]
            rfl
          rw [hstep] at hrunJ
          cases hrunJ
        | some b => exact ⟨b, hopt'⟩
      rcases hopt with ⟨b, hb⟩
      have hleB : (b.auswerten r1).pc ≤ blkA.length := hlocal r1 b hlt1 hb
      have hgetC : (blkA ++ blkB)[r1.pc]? = some b := by
        rw [getAnhangLinks blkA blkB r1.pc hlt1]
        exact hb
      have hstep : Schritt (blkA ++ blkB) (some r1) = some (b.auswerten r1) := by
        show (match (blkA ++ blkB)[r1.pc]? with | none => none | some c => some (c.auswerten r1)) =
          some (b.auswerten r1)
        rw [hgetC]
      have hJ : (Schritt (blkA ++ blkB))^[Nat.succ j1] (some r) = some (b.auswerten r1) := by
        rw [Function.iterate_succ_apply', hrun1, hstep]
      rw [hJ] at hrunJ
      have hEqR : rJ = b.auswerten r1 := Option.some.inj hrunJ
      rw [hEqR] at hgtJ
      omega
  have hP : ∀ s, s < j0 → ∃ rs, (Schritt blkA)^[s] (some r) = some rs ∧
      (Schritt (blkA ++ blkB))^[s] (some r) = some rs := by
    intro s
    induction s with
    | zero =>
      intro hs
      exact ⟨r, rfl, rfl⟩
    | succ s ih =>
      intro hs
      have hsj : s < j0 := by omega
      obtain ⟨rs, hrunA, hrunC⟩ := ih hsj
      have hltC : rs.pc < blkA.length := hkle s hsj rs hrunC
      have hgetA : (blkA ++ blkB)[rs.pc]? = blkA[rs.pc]? :=
        getAnhangLinks blkA blkB rs.pc hltC
      have hstep : Schritt (blkA ++ blkB) (some rs) = Schritt blkA (some rs) := by
        show (match (blkA ++ blkB)[rs.pc]? with | none => none | some b => some (b.auswerten rs)) =
          (match blkA[rs.pc]? with | none => none | some b => some (b.auswerten rs))
        rw [hgetA]
      have hnextA : (Schritt blkA)^[Nat.succ s] (some r) = Schritt blkA (some rs) := by
        rw [Function.iterate_succ_apply', hrunA]
      have hnextC : (Schritt (blkA ++ blkB))^[Nat.succ s] (some r) =
          Schritt (blkA ++ blkB) (some rs) := by
        rw [Function.iterate_succ_apply', hrunC]
      obtain ⟨rs', hrunCs'⟩ := laufHatZwischen (blkA ++ blkB) r k (Nat.succ s) r' hk (by omega)
      have hstepSame : Schritt blkA (some rs) = some rs' := by
        rw [← hstep, ← hnextC]
        exact hrunCs'
      exact ⟨rs', hnextA.trans hstepSame, hrunCs'⟩
  have hbleib : ∀ s, s < j0 → ∃ rs, (Schritt blkA)^[s] (some r) = some rs ∧ rs.pc < blkA.length := by
    intro s hs
    obtain ⟨rs, hrunA, hrunC⟩ := hP s hs
    exact ⟨rs, hrunA, hkle s hs rs hrunC⟩
  have hagree : (Schritt (blkA ++ blkB))^[j0] (some r) = (Schritt blkA)^[j0] (some r) :=
    laufAnhang blkA blkB r j0 hbleib
  have hrunA0 : (Schritt blkA)^[j0] (some r) = some rJ := by
    rw [← hagree]
    exact hrunJ
  exact ⟨j0, rJ, hj0k, hrunA0, hEqJ⟩

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
