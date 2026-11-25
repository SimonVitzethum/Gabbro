module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.RightSchritt

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- Preservation of the root slot through the whole selection prefix. -/
theorem presRS (ein aus frei n : Nat) (e : Rahmen) (haus : aus < frei) :
    (frameR12 e ein aus frei n).temp (frei + 0) = e.temp (frei + 0) := by
  show Function.update _ (frei + 1) _ (frei + 0) = _
  rw [updateMiss _ _ _ _ (addNeLinks (by decide : (0 : Nat) ≠ 1))]
  show Function.update _ (frei + 1) _ (frei + 0) = _
  rw [updateMiss _ _ _ _ (addNeLinks (by decide : (0 : Nat) ≠ 1))]
  show Function.update _ aus _ (frei + 0) = _
  rw [updateMiss _ _ _ _ (scratchNeAus (Nat.le_add_right frei 0) haus)]
  show Function.update _ (frei + 1) _ (frei + 0) = _
  rw [updateMiss _ _ _ _ (addNeLinks (by decide : (0 : Nat) ≠ 1))]
  show Function.update _ (frei + 2) _ (frei + 0) = _
  rw [updateMiss _ _ _ _ (addNeLinks (by decide : (0 : Nat) ≠ 2))]
  show Function.update _ (frei + 3) _ (frei + 0) = _
  rw [updateMiss _ _ _ _ (addNeLinks (by decide : (0 : Nat) ≠ 3))]
  show Function.update _ (frei + 1) _ (frei + 0) = _
  rw [updateMiss _ _ _ _ (addNeLinks (by decide : (0 : Nat) ≠ 1))]
  show Function.update _ (frei + 1) _ (frei + 0) = _
  rw [updateMiss _ _ _ _ (addNeLinks (by decide : (0 : Nat) ≠ 1))]
  show Function.update _ (frei + 2) _ (frei + 0) = _
  rw [updateMiss _ _ _ _ (addNeLinks (by decide : (0 : Nat) ≠ 2))]
  show Function.update _ (frei + 1) _ (frei + 0) = _
  rw [updateMiss _ _ _ _ (addNeLinks (by decide : (0 : Nat) ≠ 1))]
  show Function.update _ (frei + 2) _ (frei + 0) = _
  rw [updateMiss _ _ _ _ (addNeLinks (by decide : (0 : Nat) ≠ 2))]
  show Function.update _ (frei + 1) _ (frei + 0) = _
  rw [updateMiss _ _ _ _ (addNeLinks (by decide : (0 : Nat) ≠ 1))]

/-- Preservation of user slots through the whole selection prefix. -/
theorem presRPrefix (ein aus frei n : Nat) (e : Rahmen) (t : Nat)
    (ht : t < frei) (hne : t ≠ aus) :
    (frameR12 e ein aus frei n).temp t = e.temp t := by
  show Function.update _ (frei + 1) _ t = _
  rw [updateMiss _ _ _ _ (ltNeAdd ht)]
  show Function.update _ (frei + 1) _ t = _
  rw [updateMiss _ _ _ _ (ltNeAdd ht)]
  show Function.update _ aus _ t = _
  rw [updateMiss _ _ _ _ hne]
  show Function.update _ (frei + 1) _ t = _
  rw [updateMiss _ _ _ _ (ltNeAdd ht)]
  show Function.update _ (frei + 2) _ t = _
  rw [updateMiss _ _ _ _ (ltNeAdd ht)]
  show Function.update _ (frei + 3) _ t = _
  rw [updateMiss _ _ _ _ (ltNeAdd ht)]
  show Function.update _ (frei + 1) _ t = _
  rw [updateMiss _ _ _ _ (ltNeAdd ht)]
  show Function.update _ (frei + 1) _ t = _
  rw [updateMiss _ _ _ _ (ltNeAdd ht)]
  show Function.update _ (frei + 2) _ t = _
  rw [updateMiss _ _ _ _ (ltNeAdd ht)]
  show Function.update _ (frei + 1) _ t = _
  rw [updateMiss _ _ _ _ (ltNeAdd ht)]
  show Function.update _ (frei + 2) _ t = _
  rw [updateMiss _ _ _ _ (ltNeAdd ht)]
  show Function.update _ (frei + 1) _ t = _
  rw [updateMiss _ _ _ _ (ltNeAdd ht)]

/-- Preservation through the then-branch. -/
theorem presThen (ein aus frei n : Nat) (e : Rahmen) (t : Nat)
    (ht : t < frei) (hne : t ≠ aus) :
    (frameR14t e ein aus frei n).temp t = e.temp t := by
  have e1 : (frameR14t e ein aus frei n).temp t = (frameR12 e ein aus frei n).temp t := by
    show Function.update _ aus _ t = _
    rw [updateMiss _ _ _ _ hne]
  rw [e1, presRPrefix ein aus frei n e t ht hne]

/-- Preservation through the else-branch. -/
theorem presElse (ein aus frei n : Nat) (e : Rahmen) (t : Nat)
    (ht : t < frei) (hne : t ≠ aus) :
    (frameR13e e ein aus frei n).temp t = e.temp t :=
  presRPrefix ein aus frei n e t ht hne

/-- The false comparison jumps straight to the end, leaving `d - s` in place. -/
theorem selJumpRe (ein aus frei n : Nat) (e : Rahmen)
    (hepc : e.pc = 25) (hes : e.temp (frei + 0) = some (natVal (Nat.sqrt n)))
    (heq : e.temp ein = some (natVal n)) (hein : ein < frei) (haus : aus < frei)
    (h : ¬ (n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n)) :
    (Schritt (rightBlk ein aus frei))^[29] (some e) = some (frameR13e e ein aus frei n) := by
  have hpre := selLinkR12 ein aus frei n e hepc hes heq hein haus
  have hwfalse : cmpBoolLeft (Nat.sqrt n) n = false := by
    have e1 : cmpBoolLeft (Nat.sqrt n) n =
        decide (n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n) := by
      simp only [cmpBoolLeft, Compare.eval, decideDlt _ _ (Nat.sqrt_le n)]
    rw [e1]
    exact decide_eq_false h
  have g : (rightBlk ein aus frei)[53]? = some (.springeWenn (frei + 1) false 4) := by rfl
  have e0 : (Schritt (rightBlk ein aus frei))^[1] (some (frameR12 e ein aus frei n)) =
      some (frameR13e e ein aus frei n) :=
    schrittSpringeWennWahr (rightBlk ein aus frei) (frameR12 e ein aus frei n) 53
      (frei + 1) false (cmpBoolLeft (Nat.sqrt n) n) 4 (by rfl) (updateHit _ _ _) hwfalse g
  rw [show (29 : Nat) = 1 + 28 from rfl, Function.iterate_add_apply, hpre]
  exact e0

/-- The true comparison falls through and overwrites the speculative value
    with the root. -/
theorem selThenRun (ein aus frei n : Nat) (e : Rahmen)
    (hepc : e.pc = 25) (hes : e.temp (frei + 0) = some (natVal (Nat.sqrt n)))
    (heq : e.temp ein = some (natVal n)) (hein : ein < frei) (haus : aus < frei)
    (h : n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n) :
    (Schritt (rightBlk ein aus frei))^[32] (some e) = some (frameR14t e ein aus frei n) := by
  have hpre := selLinkR12 ein aus frei n e hepc hes heq hein haus
  have hbool : cmpBoolLeft (Nat.sqrt n) n = true := by
    have e1 : cmpBoolLeft (Nat.sqrt n) n =
        decide (n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n) := by
      simp only [cmpBoolLeft, Compare.eval, decideDlt _ _ (Nat.sqrt_le n)]
    rw [e1]
    exact decide_eq_true h
  have hjne : cmpBoolLeft (Nat.sqrt n) n ≠ false := by rw [hbool]; decide
  have gjump : (rightBlk ein aus frei)[53]? = some (.springeWenn (frei + 1) false 4) := by rfl
  have hj : (Schritt (rightBlk ein aus frei))^[1] (some (frameR12 e ein aus frei n)) =
      some ({ frameR12 e ein aus frei n with pc := 54 }) :=
    schrittSpringeWennFalsch (rightBlk ein aus frei) (frameR12 e ein aus frei n) 53
      (frei + 1) false (cmpBoolLeft (Nat.sqrt n) n) 4 (by rfl) (updateHit _ _ _) hjne gjump
  have g0 : (rightBlk ein aus frei)[54]? = some (.binden nameX (frei + 0)) := by rfl
  have g1 : (rightBlk ein aus frei)[54 + 1]? = some (.lesen aus 0) := by rfl
  have g2 : (rightBlk ein aus frei)[54 + 2]? = some (.blockEnde 1) := by rfl
  have hq : ({ frameR12 e ein aus frei n with pc := 54 } : Rahmen).temp (frei + 0) =
      some (natVal (Nat.sqrt n)) := by
    show (frameR12 e ein aus frei n).temp (frei + 0) = some (natVal (Nat.sqrt n))
    rw [presRS ein aus frei n e haus]
    exact hes
  have hc := laufKopie _ _ 54 aus (frei + 0) _ (by rfl) hq g0 g1 g2
  rw [show (32 : Nat) = 4 + 28 from rfl, Function.iterate_add_apply, hpre]
  rw [show (4 : Nat) = 3 + 1 from rfl, Function.iterate_add_apply, hj]
  exact hc

/-- Then-branch arrival: loop exit composed with the root overwrite. -/
theorem rightArrivalThen (ein aus frei n : Nat) (r : Rahmen)
    (hpc : r.pc = 0) (hr : r.temp ein = some (natVal n))
    (hein : ein < frei) (haus : aus < frei) (hunters : ein ≠ aus)
    (hcond : n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n) :
    ∃ k r', (Schritt (rightBlk ein aus frei))^[k] (some r) = some r' ∧
      r'.pc = 57 ∧ r'.temp aus = some (natVal ((Nat.unpair n).2)) ∧
      (∀ t, t < frei → t ≠ aus → r'.temp t = r.temp t) ∧
      r'.lokale = r.lokale ∧ r'.rueckgabe = r.rueckgabe ∧ r'.stopp = r.stopp := by
  obtain ⟨kL, rE, hrunL, hpcL, hsqrtL, hpresL, hlokL, hrueckL, hstoppL, hkL⟩ :=
    sqrtSchleife ein frei n r (rightSel ein aus frei) hpc hr hein
  have hrunL' : (Schritt (rightBlk ein aus frei))^[kL] (some r) = some rE := hrunL
  have heqE : rE.temp ein = some (natVal n) := by
    rw [hpresL _ hein]
    exact hr
  have hrunT := selThenRun ein aus frei n rE hpcL hsqrtL heqE hein haus hcond
  have hausT : (frameR14t rE ein aus frei n).temp aus =
      some (natVal ((Nat.unpair n).2)) := by
    have hget : (frameR14t rE ein aus frei n).temp aus = some (natVal (Nat.sqrt n)) :=
      updateHit _ _ _
    rw [hget, hunRight n, if_pos hcond]
  have hrun : (Schritt (rightBlk ein aus frei))^[kL + 32] (some r) =
      some (frameR14t rE ein aus frei n) := by
    rw [show kL + 32 = 32 + kL from Nat.add_comm kL 32, Function.iterate_add_apply, hrunL']
    exact hrunT
  have hpc' : (frameR14t rE ein aus frei n).pc = 57 := by
    show (frameR14t rE ein aus frei n).pc = (rightBlk ein aus frei).length
    rw [rightBlkLaenge]
    rfl
  refine ⟨kL + 32, _, hrun, hpc', hausT, ?_, ?_, ?_, ?_⟩
  · intro t ht hne
    rw [presThen ein aus frei n rE t ht hne, hpresL t ht]
  · exact hlokL
  · exact hrueckL
  · exact hstoppL

/-- Else-branch arrival: loop exit composed with the difference selection. -/
theorem rightArrivalElse (ein aus frei n : Nat) (r : Rahmen)
    (hpc : r.pc = 0) (hr : r.temp ein = some (natVal n))
    (hein : ein < frei) (haus : aus < frei) (hunters : ein ≠ aus)
    (hcond : ¬ (n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n)) :
    ∃ k r', (Schritt (rightBlk ein aus frei))^[k] (some r) = some r' ∧
      r'.pc = 57 ∧ r'.temp aus = some (natVal ((Nat.unpair n).2)) ∧
      (∀ t, t < frei → t ≠ aus → r'.temp t = r.temp t) ∧
      r'.lokale = r.lokale ∧ r'.rueckgabe = r.rueckgabe ∧ r'.stopp = r.stopp := by
  obtain ⟨kL, rE, hrunL, hpcL, hsqrtL, hpresL, hlokL, hrueckL, hstoppL, hkL⟩ :=
    sqrtSchleife ein frei n r (rightSel ein aus frei) hpc hr hein
  have hrunL' : (Schritt (rightBlk ein aus frei))^[kL] (some r) = some rE := hrunL
  have heqE : rE.temp ein = some (natVal n) := by
    rw [hpresL _ hein]
    exact hr
  have hrunE := selJumpRe ein aus frei n rE hpcL hsqrtL heqE hein haus hcond
  have hsqrt : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
  have hsle : Nat.sqrt n ≤ n - Nat.sqrt n * Nat.sqrt n := not_lt.mp hcond
  have hausE : (frameR13e rE ein aus frei n).temp aus =
      some (natVal ((Nat.unpair n).2)) := by
    have hget : (frameR13e rE ein aus frei n).temp aus =
        some (diffSubPack n (Nat.sqrt n)) := by
      show (frameR12 rE ein aus frei n).temp aus = some (diffSubPack n (Nat.sqrt n))
      show Function.update _ (frei + 1) _ aus = _
      rw [updateMiss _ _ _ _ (ltNeAdd haus)]
      show (frameR11 rE ein aus frei n).temp aus = some (diffSubPack n (Nat.sqrt n))
      show Function.update _ (frei + 1) _ aus = _
      rw [updateMiss _ _ _ _ (ltNeAdd haus)]
      show (frameR10 rE ein aus frei n).temp aus = some (diffSubPack n (Nat.sqrt n))
      exact updateHit _ _ _
    rw [hget, packDiffSub (Nat.sqrt n) n hsqrt hsle, hunRight n, if_neg hcond]
  have hrun : (Schritt (rightBlk ein aus frei))^[kL + 29] (some r) =
      some (frameR13e rE ein aus frei n) := by
    rw [show kL + 29 = 29 + kL from Nat.add_comm kL 29, Function.iterate_add_apply, hrunL']
    exact hrunE
  have hpc' : (frameR13e rE ein aus frei n).pc = 57 := by
    show (frameR13e rE ein aus frei n).pc = (rightBlk ein aus frei).length
    rw [rightBlkLaenge]
    rfl
  refine ⟨kL + 29, _, hrun, hpc', hausE, ?_, ?_, ?_, ?_⟩
  · intro t ht hne
    rw [presElse ein aus frei n rE t ht hne, hpresL t ht]
  · exact hlokL
  · exact hrueckL
  · exact hstoppL

/-- The right-projection block is correct in the block-lemma sense. -/
theorem blockRight (ein aus frei : Nat) (hein : ein < frei) (haus : aus < frei)
    (hunters : ein ≠ aus) :
    BlockKorrekt (rightBlk ein aus frei) .right ein aus frei := by
  unfold BlockKorrekt
  apply And.intro hein
  apply And.intro haus
  apply And.intro hunters
  intro n r hpc hr
  refine ⟨?_, ?_⟩
  · intro a ha
    have ha0 : a = (Nat.unpair n).2 := by
      have h0 : Part.some ((Nat.unpair n).2) = Part.some a := by
        change Part.some ((Nat.unpair n).2) = Part.some a at ha
        exact ha
      exact (Part.some_injective h0).symm
    subst ha0
    by_cases hcond : n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n
    · obtain ⟨k, r', hrun, hpc', haus', hpres, hlok, hrueck, hstopp⟩ :=
        rightArrivalThen ein aus frei n r hpc hr hein haus hunters hcond
      exact ⟨k, r', hrun, hpc', haus', hpres, hlok, hrueck, hstopp⟩
    · obtain ⟨k, r', hrun, hpc', haus', hpres, hlok, hrueck, hstopp⟩ :=
        rightArrivalElse ein aus frei n r hpc hr hein haus hunters hcond
      exact ⟨k, r', hrun, hpc', haus', hpres, hlok, hrueck, hstopp⟩
  · intro k r' hk hpc'
    by_cases hcond : n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n
    · obtain ⟨kT, rT, hrunT, hpcT, hausT, hpresT, hlokT, hrueckT, hstoppT⟩ :=
        rightArrivalThen ein aus frei n r hpc hr hein haus hunters hcond
      rcases lt_trichotomy k kT with h | h | h
      · exfalso
        exact laufStirbtNach _ _ _ _ _ _ hk hpc' hrunT h
      · subst h
        have heq : r' = rT := Option.some.inj (hk.symm.trans hrunT)
        subst heq
        have heval : Nat.Partrec.Code.eval .right n = Part.some ((Nat.unpair n).2) := rfl
        exact ⟨(Nat.unpair n).2, heval, hausT, hpresT, hlokT, hrueckT, hstoppT⟩
      · exfalso
        exact laufStirbtNach _ _ kT k _ _ hrunT hpcT hk h
    · obtain ⟨kE, rE, hrunE, hpcE, hausE, hpresE, hlokE, hrueckE, hstoppE⟩ :=
        rightArrivalElse ein aus frei n r hpc hr hein haus hunters hcond
      rcases lt_trichotomy k kE with h | h | h
      · exfalso
        exact laufStirbtNach _ _ _ _ _ _ hk hpc' hrunE h
      · subst h
        have heq : r' = rE := Option.some.inj (hk.symm.trans hrunE)
        subst heq
        have heval : Nat.Partrec.Code.eval .right n = Part.some ((Nat.unpair n).2) := rfl
        exact ⟨(Nat.unpair n).2, heval, hausE, hpresE, hlokE, hrueckE, hstoppE⟩
      · exfalso
        exact laufStirbtNach _ _ kE k _ _ hrunE hpcE hk h

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
