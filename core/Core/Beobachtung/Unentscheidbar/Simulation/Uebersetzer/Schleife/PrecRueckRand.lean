module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.PrecRueck

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- A composite run whose prefix has a known reference arrival at the prefix
    end must pass that arrival, and cannot end earlier. Unlike
    `randAusEndePrefix` this needs no global stay-inside fact: the reference
    arrival supplies the boundary directly. -/
theorem randAusEndeMitRef (blkA blkB : List Befehl) (hlenB : 0 < blkB.length)
    (r : Rahmen) (jRef : Nat) (rRef : Rahmen) (hpc : r.pc = 0)
    (hRef : (Schritt blkA)^[jRef] (some r) = some rRef)
    (hpcRef : rRef.pc = blkA.length)
    (k : Nat) (rEnd : Rahmen)
    (hk : (Schritt (blkA ++ blkB))^[k] (some r) = some rEnd)
    (hpcEnd : rEnd.pc = (blkA ++ blkB).length) :
    jRef ≤ k ∧ (Schritt (blkA ++ blkB))^[jRef] (some r) = some rRef := by
  have hbleib := laufBleibtVorEnde blkA r jRef rRef hRef hpcRef
  have hagree := laufAnhang blkA blkB r jRef hbleib
  have hrunRef : (Schritt (blkA ++ blkB))^[jRef] (some r) = some rRef := by
    rw [hagree, hRef]
  by_cases hle : jRef ≤ k
  · exact ⟨hle, hrunRef⟩
  · have hklt : k < jRef := Nat.lt_of_not_ge hle
    have hkeq : (Schritt (blkA ++ blkB))^[k] (some r) = (Schritt blkA)^[k] (some r) :=
      laufAnhang blkA blkB r k (fun j hj => hbleib j (by omega))
    have hrunK : (Schritt blkA)^[k] (some r) = some rEnd := by
      rw [← hkeq]
      exact hk
    obtain ⟨rk, hrk, hpck⟩ := hbleib k hklt
    have hrkEq : rk = rEnd := Option.some.inj (hrk.symm.trans hrunK)
    rw [hrkEq] at hpck
    rw [hpcEnd, List.length_append] at hpck
    omega

/-- A run of `pre ++ mid ++ post` starting at the relocated boundary of a
    relocatable, stay-inside block `mid` and reaching the overall end crosses
    the mid boundary once. The standalone run of `mid` from the unshifted start
    reaches its own end there, and the two boundary states agree up to the
    shift. -/
theorem randAusEndeMitPc (pre mid post : List Befehl) (hv : VerschiebbaresProgramm mid)
    (hlocal : BleibtImBlock mid) (hlenMid : 0 < mid.length) (hlenPost : 0 < post.length)
    (r0 : Rahmen) (hr0pc : r0.pc = 0) (t : Nat) (rEnd : Rahmen)
    (hk : (Schritt (pre ++ mid ++ post))^[t] (some (mitPc pre.length r0)) = some rEnd)
    (hpcEnd : rEnd.pc = pre.length + mid.length + post.length) :
    ∃ j rB rMid, j ≤ t ∧
      (Schritt (pre ++ mid ++ post))^[j] (some (mitPc pre.length r0)) = some rB ∧
      rB.pc = pre.length + mid.length ∧ rB = mitPc pre.length rMid ∧
      (Schritt mid)^[j] (some r0) = some rMid ∧ rMid.pc = mid.length := by
  classical
  let K := pre.length + mid.length
  let Q : Nat → Prop := fun s =>
    ∃ rs, s ≤ t ∧ (Schritt (pre ++ mid ++ post))^[s] (some (mitPc pre.length r0)) = some rs ∧ K ≤ rs.pc
  have hQ : ∃ s, Q s := by
    refine ⟨t, rEnd, le_rfl, hk, ?_⟩
    rw [hpcEnd]
    omega
  let Nat.find hQ := Nat.find hQ
  rcases Nat.find_spec hQ with ⟨rJ, hs0t, hrunJ, hgeJ⟩
  have hkle : ∀ s, s < Nat.find hQ → ∀ rs,
      (Schritt (pre ++ mid ++ post))^[s] (some (mitPc pre.length r0)) = some rs → rs.pc < K := by
    intro s hs rs hrs
    have hnotQ : ¬ Q s := Nat.find_min hQ hs
    by_contra hge
    exact hnotQ ⟨rs, by omega, hrs, Nat.le_of_not_gt hge⟩
  have hP : ∀ s, s < Nat.find hQ → ∃ rm,
      (Schritt mid)^[s] (some r0) = some rm ∧
      (Schritt (pre ++ mid ++ post))^[s] (some (mitPc pre.length r0)) = some (mitPc pre.length rm) ∧
      rm.pc < mid.length := by
    intro s
    induction s with
    | zero =>
        intro hs
        refine ⟨r0, rfl, rfl, ?_⟩
        rw [hr0pc]
        exact hlenMid
    | succ s ih =>
        intro hs
        have hsi : s < Nat.find hQ := by omega
        obtain ⟨rm, hrm, hcomp, hltm⟩ := ih hsi
        obtain ⟨b, hb, hvb, hzd⟩ := hv rm.pc hltm
        have hstepMid : Schritt mid (some rm) = some (b.auswerten rm) := by
          show (match mid[rm.pc]? with | none => none | some c => some (c.auswerten rm)) =
            some (b.auswerten rm)
          rw [hb]
        have hstepComp := schrittMitPcBei pre mid post hv rm hltm
        have hnextComp : (Schritt (pre ++ mid ++ post))^[s + 1]
            (some (mitPc pre.length r0)) = some (mitPc pre.length (b.auswerten rm)) := by
          rw [Function.iterate_succ_apply', hcomp, hstepComp, hstepMid]
        obtain ⟨rs1, hrs1⟩ := laufHatZwischen (pre ++ mid ++ post) (mitPc pre.length r0) t (s + 1) rEnd hk (by omega)
        have hrEq : mitPc pre.length (b.auswerten rm) = rs1 :=
          Option.some.inj (hnextComp.symm.trans hrs1)
        have hrs1K : rs1.pc < K := hkle (s + 1) hs rs1 hrs1
        rw [← hrEq] at hrs1K
        simp only [mitPc] at hrs1K
        have hltNew : (b.auswerten rm).pc < mid.length := by omega
        refine ⟨b.auswerten rm, ?_, hnextComp, hltNew⟩
        rw [Function.iterate_succ_apply', hrm, hstepMid]
  have hEqJ : rJ.pc = K := by
    by_contra hne
    have hgtJ : K < rJ.pc := Nat.lt_of_le_of_ne hgeJ (fun h => hne h.symm)
    cases hs0zero : Nat.find hQ with
    | zero =>
        have hrJ : rJ = mitPc pre.length r0 :=
          Option.some.inj (by simpa only [hs0zero, Function.iterate_zero_apply] using hrunJ.symm)
        rw [hrJ, mitPc, hr0pc, Nat.add_zero] at hgtJ
        dsimp only [K] at hgtJ
        omega
    | succ s1 =>
        have hs1lt : s1 < Nat.find hQ := by rw [hs0zero]; exact Nat.lt_succ_self s1
        obtain ⟨rs, hrs⟩ := laufHatZwischen (pre ++ mid ++ post) (mitPc pre.length r0) t s1 rEnd hk (by omega)
        have hrsK : rs.pc < K := hkle s1 hs1lt rs hrs
        obtain ⟨rm, hrm, hcomp, hltm⟩ := hP s1 hs1lt
        have hrSeq : rs = mitPc pre.length rm := Option.some.inj (hrs.symm.trans hcomp)
        obtain ⟨b, hb, hvb, hzd⟩ := hv rm.pc hltm
        have hstepMid : Schritt mid (some rm) = some (b.auswerten rm) := by
          show (match mid[rm.pc]? with | none => none | some c => some (c.auswerten rm)) =
            some (b.auswerten rm)
          rw [hb]
        have hleB := hlocal rm b hltm hb
        have hrunJs : (Schritt (pre ++ mid ++ post))^[Nat.find hQ] (some (mitPc pre.length r0)) = some rJ := by
          rw [hs0zero]
          exact hrunJ
        have hstepComp := schrittMitPcBei pre mid post hv rm hltm
        have hJstep : (Schritt (pre ++ mid ++ post))^[Nat.succ s1]
            (some (mitPc pre.length r0)) = some (mitPc pre.length (b.auswerten rm)) := by
          rw [Function.iterate_succ_apply', hcomp, hstepComp, hstepMid]
        have hJ : rJ = mitPc pre.length (b.auswerten rm) :=
          Option.some.inj (hJstep.symm.trans hrunJs)
        rw [hJ, mitPc] at hgtJ
        dsimp only [K] at hgtJ hleB
        omega
  have hbleib : ∀ s, s < Nat.find hQ → ∃ rm, (Schritt mid)^[s] (some r0) = some rm ∧ rm.pc < mid.length := by
    intro s hs
    obtain ⟨rm, hrm, hcomp, hltm⟩ := hP s hs
    exact ⟨rm, hrm, hltm⟩
  have hagree := laufMitPc pre mid post hv r0 Nat.find hQ hbleib
  rw [hrunJ] at hagree
  cases hst : (Schritt mid)^[Nat.find hQ] (some r0) with
  | none =>
      have hnone : some rJ = none := by simpa only [hst] using hagree
      cases hnone
  | some rMid =>
      have hrJ : rJ = mitPc pre.length rMid := Option.some.inj (by simpa only [hst] using hagree)
      have hpcMid : rMid.pc = mid.length := by
        have hEqJ' := hEqJ
        rw [hrJ, mitPc] at hEqJ'
        dsimp only [K] at hEqJ'
        omega
      refine ⟨Nat.find hQ, rJ, rMid, hs0t, hrunJ, ?_, hrJ, hst, hpcMid⟩
      · dsimp only [K] at hEqJ
        exact hEqJ

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
