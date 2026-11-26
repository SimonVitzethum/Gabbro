module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.RfindBlock

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- A successful minimisation evaluation identifies the first zero candidate:
    the result is that candidate, it is zero, and every earlier candidate from
    the search start is defined and nonzero. -/
theorem rfindEvalZeigt (cf : Nat.Partrec.Code) (a m y : Nat)
    (h : Nat.Partrec.Code.eval (.rfind' cf) (Nat.pair a m) = Part.some y) :
    m ≤ y ∧
    Nat.Partrec.Code.eval cf (Nat.pair a y) = Part.some 0 ∧
    (∀ z, m ≤ z → z < y → ∃ v,
      Nat.Partrec.Code.eval cf (Nat.pair a z) = Part.some v ∧ v ≠ 0) := by
  let p : Nat → Part Bool := fun n =>
    (fun v => v = 0) <$> Nat.Partrec.Code.eval cf (Nat.pair a (n + m))
  have h' : (Nat.rfind p).map (fun n => n + m) = Part.some y := by
    simpa only [Nat.Partrec.Code.eval, Nat.unpaired, Nat.unpair_pair, p] using h
  have hyMem : y ∈ (Nat.rfind p).map (fun n => n + m) := by
    rw [h']
    simp only [Part.mem_some_iff]
  obtain ⟨i, hi, hiadd⟩ := (Part.mem_map_iff (fun n => n + m)).1 hyMem
  have hiR := (Nat.mem_rfind).1 hi
  have htrue : true ∈ p i := hiR.1
  have hfalse : ∀ {j}, j < i → false ∈ p j := hiR.2
  obtain ⟨v0, hv0, hv0eq⟩ := (Part.mem_map_iff (fun v => v = 0)).1 htrue
  have hv0zero : v0 = 0 := by simpa only using hv0eq
  have hzero : Nat.Partrec.Code.eval cf (Nat.pair a (i + m)) = Part.some 0 :=
    Part.eq_some_iff.2 (by simpa only [hv0zero] using hv0)
  refine ⟨by omega, ?_, ?_⟩
  · simpa only [hiadd] using hzero
  · intro z hmz hzy
    have hjlt : z - m < i := by omega
    obtain ⟨v, hv, hveq⟩ := (Part.mem_map_iff (fun v => v = 0)).1 (hfalse hjlt)
    have hvne : v ≠ 0 := by
      intro he
      have : (v = 0) = true := by rw [he]; rfl
      simpa only [this] using hveq
    have hzadd : (z - m) + m = z := by omega
    refine ⟨v, ?_, hvne⟩
    rw [← hzadd]
    exact Part.eq_some_iff.2 hv

/-- If the value at the start already terminates with zero, the minimisation
    returns the start itself. -/
theorem rfindEvalBeiNull (cf : Nat.Partrec.Code) (a m : Nat)
    (hzero : Nat.Partrec.Code.eval cf (Nat.pair a m) = Part.some 0) :
    Nat.Partrec.Code.eval (.rfind' cf) (Nat.pair a m) = Part.some m := by
  let p : Nat → Part Bool := fun n =>
    (fun v => v = 0) <$> Nat.Partrec.Code.eval cf (Nat.pair a (n + m))
  have hmem0 : 0 ∈ p 0 := by
    have hm : 0 ∈ Nat.Partrec.Code.eval cf (Nat.pair a m) := by
      rw [hzero]
      simp only [Part.mem_some_iff]
    have hm' : 0 ∈ Nat.Partrec.Code.eval cf (Nat.pair a (0 + m)) := by
      simpa only [Nat.zero_add] using hm
    exact (Part.mem_map_iff (fun v => v = 0)).2 ⟨0, hm', rfl⟩
  have hmemR : 0 ∈ Nat.rfind p := Nat.mem_rfind.2 ⟨hmem0, by
    intro j hj
    exact (Nat.not_lt_zero _ hj).elim⟩
  have hR : Nat.rfind p = Part.some 0 := Part.eq_some_iff.2 hmemR
  simp only [Nat.Partrec.Code.eval, Nat.unpaired, Nat.unpair_pair, p]
  rw [hR]
  simp only [Part.map_some, Nat.zero_add]

/-- Skipping a defined nonzero start does not change the minimisation result,
    because the search for the first zero starts one candidate later. -/
theorem rfindEvalWeiter (cf : Nat.Partrec.Code) (a m y : Nat)
    (hdef : ∃ v, Nat.Partrec.Code.eval cf (Nat.pair a m) = Part.some v)
    (hnz : Nat.Partrec.Code.eval cf (Nat.pair a m) ≠ Part.some 0)
    (hnext : Nat.Partrec.Code.eval (.rfind' cf) (Nat.pair a (m + 1)) = Part.some y) :
    Nat.Partrec.Code.eval (.rfind' cf) (Nat.pair a m) = Part.some y := by
  obtain ⟨mle, hzero, hvor⟩ := rfindEvalZeigt cf a (m + 1) y hnext
  let p : Nat → Part Bool := fun n =>
    (fun v => v = 0) <$> Nat.Partrec.Code.eval cf (Nat.pair a (n + m))
  have hmemZ : true ∈ p (y - m) := by
    have hz : 0 ∈ Nat.Partrec.Code.eval cf (Nat.pair a y) := by
      rw [hzero]
      simp only [Part.mem_some_iff]
    have hyadd : (y - m) + m = y := by omega
    have hz' : 0 ∈ Nat.Partrec.Code.eval cf (Nat.pair a ((y - m) + m)) := by
      simpa only [hyadd] using hz
    exact (Part.mem_map_iff (fun v => v = 0)).2 ⟨0, hz', rfl⟩
  have hmemF : ∀ {j}, j < y - m → false ∈ p j := by
    intro j hj
    have hjge : m ≤ j + m := by omega
    have hjlt : j + m < y := by omega
    by_cases hj0 : j = 0
    · subst j
      obtain ⟨v, hv⟩ := hdef
      have hv' : v ∈ Nat.Partrec.Code.eval cf (Nat.pair a (0 + m)) := by
        simpa only [Nat.zero_add] using (show v ∈ Nat.Partrec.Code.eval cf (Nat.pair a m) by
          rw [hv]
          simp only [Part.mem_some_iff])
      have hvne : v ≠ 0 := by
        intro he
        apply hnz
        rw [hv, he]
      have hfalse : (v = 0) = false := by simp only [hvne, down_reduce]
      exact (Part.mem_map_iff (fun v => v = 0)).2 ⟨v, hv', hfalse⟩
    · have hjm : m + 1 ≤ j + m := by omega
      obtain ⟨v, hv, hvne⟩ := hvor (j + m) hjm hjlt
      have hv' : v ∈ Nat.Partrec.Code.eval cf (Nat.pair a (j + m)) := by
        rw [hv]
        simp only [Part.mem_some_iff]
      have hfalse : (v = 0) = false := by simp only [hvne, down_reduce]
      exact (Part.mem_map_iff (fun v => v = 0)).2 ⟨v, hv', hfalse⟩
  have hmemR : (y - m) ∈ Nat.rfind p := Nat.mem_rfind.2 ⟨hmemZ, hmemF⟩
  have hR : Nat.rfind p = Part.some (y - m) := Part.eq_some_iff.2 hmemR
  simp only [Nat.Partrec.Code.eval, Nat.unpaired, Nat.unpair_pair, p]
  rw [hR]
  simp only [Part.map_some]
  congr 1
  omega

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
