module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.SqrtKette

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- Preservation of untouched slots through a full continue-iteration. -/
theorem presWeiter (ein frei s n : Nat) (q : Rahmen) (u : Nat)
    (h0 : u ≠ frei + 0) (h1 : u ≠ frei + 1) (h3 : u ≠ frei + 3)
    (h4 : u ≠ frei + 4) (h5 : u ≠ frei + 5) (h6 : u ≠ frei + 6) :
    (frameA11 q frei s n).temp u = q.temp u := by
  have e1 : (frameA11 q frei s n).temp u = (frameA10 q frei s n).temp u := rfl
  have e2 : (frameA10 q frei s n).temp u = (frameA9w q frei s n).temp u := by
    show Function.update _ (frei + 0) _ u = _
    rw [updateMiss _ _ _ _ h0]
  have e3 : (frameA9w q frei s n).temp u = (frameA8 q frei s n).temp u := rfl
  have e4 : (frameA8 q frei s n).temp u = (frameA7 q frei s n).temp u := by
    show Function.update _ (frei + 5) _ u = _
    rw [updateMiss _ _ _ _ h5]
  have e5 : (frameA7 q frei s n).temp u = (frameA6 q frei s).temp u := by
    show Function.update _ (frei + 6) _ u = _
    rw [updateMiss _ _ _ _ h6]
  have e6 : (frameA6 q frei s).temp u = (frameA5 q frei s).temp u := by
    show Function.update _ (frei + 5) _ u = _
    rw [updateMiss _ _ _ _ h5]
  have e7 : (frameA5 q frei s).temp u = (frameA4 q frei s).temp u := by
    show Function.update _ (frei + 3) _ u = _
    rw [updateMiss _ _ _ _ h3]
  have e8 : (frameA4 q frei s).temp u = (frameA3 q frei s).temp u := by
    show Function.update _ (frei + 4) _ u = _
    rw [updateMiss _ _ _ _ h4]
  have e9 : (frameA3 q frei s).temp u = (frameA2 q frei s).temp u := by
    show Function.update _ (frei + 3) _ u = _
    rw [updateMiss _ _ _ _ h3]
  have e10 : (frameA2 q frei s).temp u = (frameA1 q frei s).temp u := by
    show Function.update _ (frei + 1) _ u = _
    rw [updateMiss _ _ _ _ h1]
  have e11 : (frameA1 q frei s).temp u = q.temp u := by
    show Function.update _ (frei + 1) _ u = _
    rw [updateMiss _ _ _ _ h1]
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]

/-- One full loop iteration: the counter increases by one. -/
theorem laufKoerperWeiter (ein frei s n : Nat) (q : Rahmen) (rest : List Befehl)
    (hqpc : q.pc = 2) (hqe : q.temp ein = some (natVal n))
    (hqs : q.temp (frei + 0) = some (natVal s)) (hq1 : q.temp (frei + 2) = some (natVal 1))
    (hein : ein < frei) (h : (s + 1) * (s + 1) ≤ n) :
    (Schritt (sqrtPrefix ein frei ++ rest))^[23] (some q) =
      some (frameA11 q frei s n) ∧
      (frameA11 q frei s n).pc = 2 ∧
      (frameA11 q frei s n).temp (frei + 0) = some (natVal (s + 1)) ∧
      (frameA11 q frei s n).temp (frei + 2) = some (natVal 1) ∧
      (∀ t, t < frei → (frameA11 q frei s n).temp t = q.temp t) ∧
      (frameA11 q frei s n).lokale = q.lokale ∧
      (frameA11 q frei s n).rueckgabe = q.rueckgabe ∧
      (frameA11 q frei s n).stopp = q.stopp := by
  have hrun := kette11w ein frei s n q rest hqpc hqs hq1 hqe hein h
  refine ⟨hrun, rfl, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · exact updateHit _ _ _
  · rw [presWeiter ein frei s n q (frei + 2) (addNeLinks (by decide : (2 : Nat) ≠ 0))
      (addNeLinks (by decide : (2 : Nat) ≠ 1)) (addNeLinks (by decide : (2 : Nat) ≠ 3))
      (addNeLinks (by decide : (2 : Nat) ≠ 4)) (addNeLinks (by decide : (2 : Nat) ≠ 5))
      (addNeLinks (by decide : (2 : Nat) ≠ 6))]
    exact hq1
  · intro t ht
    rw [presWeiter ein frei s n q t (ltNeAdd ht) (ltNeAdd ht) (ltNeAdd ht)
      (ltNeAdd ht) (ltNeAdd ht) (ltNeAdd ht)]

/-- Preservation of untouched slots through the exiting iteration. -/
theorem presFertig (ein frei s n : Nat) (q : Rahmen) (u : Nat)
    (h1 : u ≠ frei + 1) (h3 : u ≠ frei + 3)
    (h4 : u ≠ frei + 4) (h5 : u ≠ frei + 5) (h6 : u ≠ frei + 6) :
    (frameA9e q frei s n).temp u = (frameA8 q frei s n).temp u := rfl

theorem presFertigKette (ein frei s n : Nat) (q : Rahmen) (u : Nat)
    (h1 : u ≠ frei + 1) (h3 : u ≠ frei + 3)
    (h4 : u ≠ frei + 4) (h5 : u ≠ frei + 5) (h6 : u ≠ frei + 6) :
    (frameA8 q frei s n).temp u = q.temp u := by
  have e4 : (frameA8 q frei s n).temp u = (frameA7 q frei s n).temp u := by
    show Function.update _ (frei + 5) _ u = _
    rw [updateMiss _ _ _ _ h5]
  have e5 : (frameA7 q frei s n).temp u = (frameA6 q frei s).temp u := by
    show Function.update _ (frei + 6) _ u = _
    rw [updateMiss _ _ _ _ h6]
  have e6 : (frameA6 q frei s).temp u = (frameA5 q frei s).temp u := by
    show Function.update _ (frei + 5) _ u = _
    rw [updateMiss _ _ _ _ h5]
  have e7 : (frameA5 q frei s).temp u = (frameA4 q frei s).temp u := by
    show Function.update _ (frei + 3) _ u = _
    rw [updateMiss _ _ _ _ h3]
  have e8 : (frameA4 q frei s).temp u = (frameA3 q frei s).temp u := by
    show Function.update _ (frei + 4) _ u = _
    rw [updateMiss _ _ _ _ h4]
  have e9 : (frameA3 q frei s).temp u = (frameA2 q frei s).temp u := by
    show Function.update _ (frei + 3) _ u = _
    rw [updateMiss _ _ _ _ h3]
  have e10 : (frameA2 q frei s).temp u = (frameA1 q frei s).temp u := by
    show Function.update _ (frei + 1) _ u = _
    rw [updateMiss _ _ _ _ h1]
  have e11 : (frameA1 q frei s).temp u = q.temp u := by
    show Function.update _ (frei + 1) _ u = _
    rw [updateMiss _ _ _ _ h1]
  rw [e4, e5, e6, e7, e8, e9, e10, e11]

/-- The exiting iteration reaches the loop end with the root in place. -/
theorem laufKoerperFertig (ein frei s n : Nat) (q : Rahmen) (rest : List Befehl)
    (hqpc : q.pc = 2) (hqe : q.temp ein = some (natVal n))
    (hqs : q.temp (frei + 0) = some (natVal s)) (hq1 : q.temp (frei + 2) = some (natVal 1))
    (hein : ein < frei) (h : ¬ ((s + 1) * (s + 1) ≤ n)) :
    (Schritt (sqrtPrefix ein frei ++ rest))^[19] (some q) =
      some (frameA9e q frei s n) ∧
      (frameA9e q frei s n).pc = 25 ∧
      (frameA9e q frei s n).temp (frei + 0) = some (natVal s) ∧
      (frameA9e q frei s n).temp (frei + 2) = some (natVal 1) ∧
      (∀ t, t < frei → (frameA9e q frei s n).temp t = q.temp t) ∧
      (frameA9e q frei s n).lokale = q.lokale ∧
      (frameA9e q frei s n).rueckgabe = q.rueckgabe ∧
      (frameA9e q frei s n).stopp = q.stopp := by
  have hrun := kette9e ein frei s n q rest hqpc hqs hq1 hqe hein h
  refine ⟨hrun, rfl, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · rw [presFertig ein frei s n q (frei + 0) (addNeLinks (by decide : (0 : Nat) ≠ 1))
      (addNeLinks (by decide : (0 : Nat) ≠ 3)) (addNeLinks (by decide : (0 : Nat) ≠ 4))
      (addNeLinks (by decide : (0 : Nat) ≠ 5)) (addNeLinks (by decide : (0 : Nat) ≠ 6))]
    rw [presFertigKette ein frei s n q (frei + 0) (addNeLinks (by decide : (0 : Nat) ≠ 1))
      (addNeLinks (by decide : (0 : Nat) ≠ 3)) (addNeLinks (by decide : (0 : Nat) ≠ 4))
      (addNeLinks (by decide : (0 : Nat) ≠ 5)) (addNeLinks (by decide : (0 : Nat) ≠ 6))]
    exact hqs
  · rw [presFertig ein frei s n q (frei + 2) (addNeLinks (by decide : (2 : Nat) ≠ 1))
      (addNeLinks (by decide : (2 : Nat) ≠ 3)) (addNeLinks (by decide : (2 : Nat) ≠ 4))
      (addNeLinks (by decide : (2 : Nat) ≠ 5)) (addNeLinks (by decide : (2 : Nat) ≠ 6))]
    rw [presFertigKette ein frei s n q (frei + 2) (addNeLinks (by decide : (2 : Nat) ≠ 1))
      (addNeLinks (by decide : (2 : Nat) ≠ 3)) (addNeLinks (by decide : (2 : Nat) ≠ 4))
      (addNeLinks (by decide : (2 : Nat) ≠ 5)) (addNeLinks (by decide : (2 : Nat) ≠ 6))]
    exact hq1
  · intro t ht
    rw [presFertig ein frei s n q t (ltNeAdd ht)
      (ltNeAdd ht) (ltNeAdd ht) (ltNeAdd ht) (ltNeAdd ht)]
    rw [presFertigKette ein frei s n q t (ltNeAdd ht)
      (ltNeAdd ht) (ltNeAdd ht) (ltNeAdd ht) (ltNeAdd ht)]

/-- The loop reaches the exit with the integer square root in place. -/
theorem sqrtSchleifeVon (ein frei s n : Nat) (q : Rahmen) (rest : List Befehl)
    (hqpc : q.pc = 2) (hqe : q.temp ein = some (natVal n))
    (hqs : q.temp (frei + 0) = some (natVal s)) (hq1 : q.temp (frei + 2) = some (natVal 1))
    (hein : ein < frei) (hsq : s * s ≤ n) :
    ∃ k q', (Schritt (sqrtPrefix ein frei ++ rest))^[k] (some q) = some q' ∧
      q'.pc = 25 ∧ q'.temp (frei + 0) = some (natVal (Nat.sqrt n)) ∧
      (∀ t, t < frei → q'.temp t = q.temp t) ∧
      q'.lokale = q.lokale ∧ q'.rueckgabe = q.rueckgabe ∧ q'.stopp = q.stopp ∧
      k = 23 * (Nat.sqrt n - s) + 19 := by
  suffices h : ∀ f s q, q.pc = 2 → q.temp ein = some (natVal n) →
      q.temp (frei + 0) = some (natVal s) → q.temp (frei + 2) = some (natVal 1) →
      s + f = Nat.sqrt n → s * s ≤ n →
      ∃ k q', (Schritt (sqrtPrefix ein frei ++ rest))^[k] (some q) = some q' ∧
        q'.pc = 25 ∧ q'.temp (frei + 0) = some (natVal (Nat.sqrt n)) ∧
        (∀ t, t < frei → q'.temp t = q.temp t) ∧
        q'.lokale = q.lokale ∧ q'.rueckgabe = q.rueckgabe ∧ q'.stopp = q.stopp ∧
        k = 23 * f + 19 by
    have hle : s ≤ Nat.sqrt n := Nat.le_sqrt.mpr hsq
    obtain ⟨k, q', hrun, hpc, hsqrt, hpres, hlok, hrueck, hstopp, hk⟩ :=
      h (Nat.sqrt n - s) s q hqpc hqe hqs hq1 (Nat.add_sub_cancel' hle) hsq
    exact ⟨k, q', hrun, hpc, hsqrt, hpres, hlok, hrueck, hstopp, hk⟩
  intro f
  induction f with
  | zero =>
    intro s q hqpc hqe hqs hq1 hs hsq
    have hs0 : s = Nat.sqrt n := by simpa only [Nat.add_zero] using hs
    subst hs0
    obtain ⟨hrun, hpc, hsqrt, hone, hpres, hlok, hrueck, hstopp⟩ :=
      laufKoerperFertig ein frei (Nat.sqrt n) n q rest hqpc hqe hqs hq1 hein
        (exitUeber n)
    exact ⟨19, _, hrun, hpc, hsqrt, hpres, hlok, hrueck, hstopp, rfl⟩
  | succ f ih =>
    intro s q hqpc hqe hqs hq1 hs hsq
    have hlt : s < Nat.sqrt n := by
      have hpos : 0 < f + 1 := Nat.add_one_pos f
      have hstep : s < s + (f + 1) := Nat.lt_add_of_pos_right hpos
      rw [hs] at hstep
      exact hstep
    have hcont := weiterUnter s n hlt
    obtain ⟨hrunW, hpcW, hsqrtW, honeW, hpresW, hlokW, hrueckW, hstoppW⟩ :=
      laufKoerperWeiter ein frei s n q rest hqpc hqe hqs hq1 hein hcont
    -- The counter state after one iteration feeds the induction hypothesis.
    have hqm : (frameA11 q frei s n).temp ein = some (natVal n) := by
      rw [presWeiter ein frei s n q ein (ltNeAdd hein) (ltNeAdd hein) (ltNeAdd hein)
        (ltNeAdd hein) (ltNeAdd hein) (ltNeAdd hein)]
      exact hqe
    have hq1m : (frameA11 q frei s n).temp (frei + 2) = some (natVal 1) := by
      rw [presWeiter ein frei s n q (frei + 2) (addNeLinks (by decide : (2 : Nat) ≠ 0))
        (addNeLinks (by decide : (2 : Nat) ≠ 1)) (addNeLinks (by decide : (2 : Nat) ≠ 3))
        (addNeLinks (by decide : (2 : Nat) ≠ 4)) (addNeLinks (by decide : (2 : Nat) ≠ 5))
        (addNeLinks (by decide : (2 : Nat) ≠ 6))]
      exact hq1
    obtain ⟨k', q', hrun', hpc', hsqrt', hpres', hlok', hrueck', hstopp', hk'⟩ :=
      ih (s + 1) (frameA11 q frei s n) hpcW hqm hsqrtW hq1m
        (by rw [← Nat.add_assoc, Nat.add_comm 1 f]; exact hs) hcont
    have e : (Schritt (sqrtPrefix ein frei ++ rest))^[23 + k'] (some q) =
        (Schritt (sqrtPrefix ein frei ++ rest))^[k']
          ((Schritt (sqrtPrefix ein frei ++ rest))^[23] (some q)) := by
      rw [show (23 + k' : Nat) = k' + 23 from Nat.add_comm 23 k', Function.iterate_add_apply]
    have hrun : (Schritt (sqrtPrefix ein frei ++ rest))^[23 + k'] (some q) =
        some q' := by
      rw [e, hrunW, hrun']
    have hk : 23 + k' = 23 * (f + 1) + 19 := by
      rw [hk', Nat.mul_add, Nat.mul_one, Nat.add_assoc 23 (23 * f) 19,
        Nat.add_comm 23 (23 * f)]
    have hpres : ∀ t, t < frei → q'.temp t = q.temp t := fun t ht =>
      (hpres' t ht).trans (hpresW t ht)
    have hlok : q'.lokale = q.lokale := hlok'.trans hlokW
    have hrueck : q'.rueckgabe = q.rueckgabe := hrueck'.trans hrueckW
    have hstopp : q'.stopp = q.stopp := hstopp'.trans hstoppW
    exact ⟨23 + k', q', hrun, hpc', hsqrt', hpres, hlok, hrueck, hstopp, hk⟩

/-- The search prefix reaches its exit with the integer square root in place. -/
theorem sqrtSchleife (ein frei n : Nat) (r : Rahmen) (rest : List Befehl)
    (hpc : r.pc = 0) (hr : r.temp ein = some (natVal n)) (hein : ein < frei) :
    ∃ k r', (Schritt (sqrtPrefix ein frei ++ rest))^[k] (some r) = some r' ∧
      r'.pc = 25 ∧ r'.temp (frei + 0) = some (natVal (Nat.sqrt n)) ∧
      (∀ t, t < frei → r'.temp t = r.temp t) ∧
      r'.lokale = r.lokale ∧ r'.rueckgabe = r.rueckgabe ∧ r'.stopp = r.stopp ∧
      k = 2 + 23 * Nat.sqrt n + 19 := by
  have hlen : (sqrtPrefix ein frei).length = 25 := sqrtPrefixLaenge _ _
  have g0 : ((sqrtPrefix ein frei ++ rest)[0]?) = some (.literal (frei + 0) 0) := by
    rw [getAnhangLinks _ _ _ (by rw [hlen]; decide)]
    rfl
  have e0 := schrittLiteral _ _ _ _ _ hpc g0
  have hpc1 : ({ r with pc := r.pc + 1, temp := Function.update r.temp (frei + 0) (some (natVal 0)) } : Rahmen).pc = 1 := by
    show r.pc + 1 = 1
    rw [hpc]
  have g1 : ((sqrtPrefix ein frei ++ rest)[1]?) = some (.literal (frei + 2) 1) := by
    rw [getAnhangLinks _ _ _ (by rw [hlen]; decide)]
    rfl
  have e1 := schrittLiteral _ _ _ _ _ hpc1 g1
  have hL0pc : r.pc + 1 + 1 = 2 := by rw [hpc]
  have hr1e : (Function.update (Function.update r.temp (frei + 0) (some (natVal 0)))
      (frei + 2) (some (natVal 1))) ein = some (natVal n) := by
    rw [updateMiss _ _ _ _ (ltNeAdd hein), updateMiss _ _ _ _ (ltNeAdd hein)]
    exact hr
  have hr10 : (Function.update (Function.update r.temp (frei + 0) (some (natVal 0)))
      (frei + 2) (some (natVal 1))) (frei + 0) = some (natVal 0) := by
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (0 : Nat) ≠ 2))]
    exact updateHit _ _ _
  have hr12 : (Function.update (Function.update r.temp (frei + 0) (some (natVal 0)))
      (frei + 2) (some (natVal 1))) (frei + 2) = some (natVal 1) :=
    updateHit _ _ _
  have hpres1 : ∀ t, t < frei → (Function.update (Function.update r.temp (frei + 0)
      (some (natVal 0))) (frei + 2) (some (natVal 1))) t = r.temp t := by
    intro t ht
    rw [updateMiss _ _ _ _ (ltNeAdd ht), updateMiss _ _ _ _ (ltNeAdd ht)]
  obtain ⟨kVon, r', hrunVon, hpcVon, hsqrtVon, hpresVon, hlokVon, hrueckVon,
    hstoppVon, hkVon⟩ :=
    sqrtSchleifeVon ein frei 0 n { r with pc := r.pc + 1 + 1, temp := Function.update (Function.update r.temp (frei + 0) (some (natVal 0))) (frei + 2) (some (natVal 1)) } rest hL0pc hr1e hr10 hr12 hein
      (by simp only [Nat.zero_mul]; exact Nat.zero_le n)
  have e : (Schritt (sqrtPrefix ein frei ++ rest))^[2 + kVon] (some r) =
      (Schritt (sqrtPrefix ein frei ++ rest))^[kVon]
        ((Schritt (sqrtPrefix ein frei ++ rest))^[2] (some r)) := by
    rw [show (2 + kVon : Nat) = kVon + 2 from Nat.add_comm 2 kVon, Function.iterate_add_apply]
  have hrun2 : (Schritt (sqrtPrefix ein frei ++ rest))^[2] (some r) =
      some { r with pc := r.pc + 1 + 1, temp := Function.update (Function.update r.temp (frei + 0) (some (natVal 0))) (frei + 2) (some (natVal 1)) } := by
    have e2 : (Schritt (sqrtPrefix ein frei ++ rest))^[2] (some r) =
        Schritt (sqrtPrefix ein frei ++ rest)
          (Schritt (sqrtPrefix ein frei ++ rest) (some r)) := rfl
    rw [e2, e0, e1]
  have hrun : (Schritt (sqrtPrefix ein frei ++ rest))^[2 + kVon] (some r) =
      some r' := by
    rw [e, hrun2, hrunVon]
  have hk : 2 + kVon = 2 + 23 * Nat.sqrt n + 19 := by
    rw [hkVon, Nat.sub_zero, Nat.add_assoc]
  have hpres : ∀ t, t < frei → r'.temp t = r.temp t := fun t ht =>
    (hpresVon t ht).trans (hpres1 t ht)
  have hlok : r'.lokale = r.lokale := hlokVon.trans rfl
  have hrueck : r'.rueckgabe = r.rueckgabe := hrueckVon.trans rfl
  have hstopp : r'.stopp = r.stopp := hstoppVon.trans rfl
  exact ⟨2 + kVon, r', hrun, hpcVon, hsqrtVon, hpres, hlok, hrueck, hstopp, hk⟩

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
