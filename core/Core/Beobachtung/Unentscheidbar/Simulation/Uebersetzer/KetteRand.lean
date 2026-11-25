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
  · convert schrittMitPcBei pre mid [] hv r hlt using 1 <;> simp only [List.append_nil]
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
    | none => rfl
    | some rj => exact schrittMitPcTotal pre mid hv rj

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
  generalize hst : (Schritt mid)^[t] (some r0) = x at ht
  cases x with
  | none =>
    simp only at ht
    cases ht
  | some rB =>
    have hEq : rEnd = mitPc pre.length rB := Option.some.inj (by simpa only using ht)
    refine ⟨rB, rfl, ?_, hEq⟩
    have hp : (mitPc pre.length rB).pc = rEnd.pc := by rw [← hEq]
    simp only [mitPc] at hp
    omega

/-- The intermediate arrival of a composite run at the block boundary. From a
    run reaching the overall end, take the first counter at or beyond the first
    block's length: `BleibtImBlock` rules out an overshoot, so it is exactly the
    boundary, and before it the run is still inside the first block. Prefix
    agreement then turns it into an arrival of the standalone first block.
    Uniqueness of that arrival follows from `laufStirbtNach`; blockKette uses it
    to identify an arbitrary arrival with this one. -/
theorem randAusEndePrefix (blkA blkB : List Befehl) (hlocal : BleibtImBlock blkA)
    (hlenA : 0 < blkA.length) (hlenB : 0 < blkB.length)
    (r : Rahmen) (k : Nat) (r' : Rahmen) (hrpc : r.pc = 0)
    (hk : (Schritt (blkA ++ blkB))^[k] (some r) = some r')
    (hpcEnd : r'.pc = (blkA ++ blkB).length) :
    ∃ j rA, j ≤ k ∧ (Schritt (blkA ++ blkB))^[j] (some r) = some rA ∧
      (Schritt blkA)^[j] (some r) = some rA ∧ rA.pc = blkA.length := by
  classical
  let Q : Nat → Prop := fun s =>
    ∃ rs, s ≤ k ∧ (Schritt (blkA ++ blkB))^[s] (some r) = some rs ∧ blkA.length ≤ rs.pc
  have hQ : ∃ s, Q s := by
    refine ⟨k, r', le_rfl, hk, ?_⟩
    rw [hpcEnd, List.length_append]
    omega
  rcases Nat.find_spec hQ with ⟨rJ, hjFindK, hrunJ, hgeJ⟩
  have hkle : ∀ s, s < Nat.find hQ → ∀ rs,
      (Schritt (blkA ++ blkB))^[s] (some r) = some rs → rs.pc < blkA.length := by
    intro s hs rs hrs
    have hnotQ : ¬ Q s := Nat.find_min hQ hs
    by_contra hge
    exact hnotQ ⟨rs, by omega, hrs, Nat.le_of_not_gt hge⟩
  have hEqJ : rJ.pc = blkA.length := by
    by_contra hne
    have hgtJ : blkA.length < rJ.pc := Nat.lt_of_le_of_ne hgeJ (fun h => hne h.symm)
    cases hFind : Nat.find hQ with
    | zero =>
      have hrJ : rJ = r := by
        exact Option.some.inj (by simpa only [hFind, Function.iterate_zero_apply] using hrunJ.symm)
      rw [hrJ, hrpc] at hgtJ
      omega
    | succ j1 =>
      have hj1Find : j1 < Nat.find hQ := by rw [hFind]; exact Nat.lt_succ_self j1
      have hj1k : j1 ≤ k := by omega
      obtain ⟨r1, hrun1⟩ := laufHatZwischen (blkA ++ blkB) r k j1 r' hk hj1k
      have hlt1 : r1.pc < blkA.length := hkle j1 hj1Find r1 hrun1
      have hrunJs : (Schritt (blkA ++ blkB))^[Nat.succ j1] (some r) = some rJ := by
        rw [show Nat.succ j1 = Nat.find hQ by omega]
        exact hrunJ
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
          rw [hstep] at hrunJs
          cases hrunJs
        | some b => exact ⟨b, rfl⟩
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
      rw [hJ] at hrunJs
      have hEqR : rJ = b.auswerten r1 := Option.some.inj hrunJs.symm
      rw [hEqR] at hgtJ
      omega
  have hP : ∀ s, s < Nat.find hQ → ∃ rs, (Schritt blkA)^[s] (some r) = some rs ∧
      (Schritt (blkA ++ blkB))^[s] (some r) = some rs := by
    intro s
    induction s with
    | zero =>
      intro hs
      exact ⟨r, rfl, rfl⟩
    | succ s ih =>
      intro hs
      have hsj : s < Nat.find hQ := by omega
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
  have hbleib : ∀ s, s < Nat.find hQ → ∃ rs, (Schritt blkA)^[s] (some r) = some rs ∧
      rs.pc < blkA.length := by
    intro s hs
    obtain ⟨rs, hrunA, hrunC⟩ := hP s hs
    exact ⟨rs, hrunA, hkle s hs rs hrunC⟩
  have hagree : (Schritt (blkA ++ blkB))^[Nat.find hQ] (some r) =
      (Schritt blkA)^[Nat.find hQ] (some r) := laufAnhang blkA blkB r (Nat.find hQ) hbleib
  have hrunA0 : (Schritt blkA)^[Nat.find hQ] (some r) = some rJ := by
    rw [← hagree]
    exact hrunJ
  exact ⟨Nat.find hQ, rJ, hjFindK, hrunJ, hrunA0, hEqJ⟩

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
