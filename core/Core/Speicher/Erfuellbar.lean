/-
  File:      core/Core/Speicher/Erfuellbar.lean
  Subject:   SATISFIABILITY of the premise bundle of `drf_sc` (AGENTS.md §3): a consistent graph with
             only `seq_cst` atomics and no race in which both premises bite -- a plain carrier with
             conflicting accesses and a `seq_cst` carrier (`drf_sc_erfuellbar`). The graph is
             message passing: thread 1 writes the plain `x := 1`, then the `seq_cst` flag
             `y := 1`; thread 2 reads the flag `1`, then reads `x = 1`.
-/
module

public import Core.Speicher.Trennung

@[expose] public section

namespace Gabbro.Core.Speicher

/-- The events: the two initial writes, thread 1 `wx; wy`, thread 2 `ry; rx`. -/
inductive MpEv where
  | ix
  | iy
  | wx
  | wy
  | ry
  | rx
  deriving DecidableEq, Repr

open MpEv

/-- Location `false` is the plain `x`, `true` the `seq_cst` flag `y`. -/
def mpLab : MpEv → Etikett Bool Nat
  | ix => ⟨.schreiben, false, .na, 0, 0⟩
  | iy => ⟨.schreiben, true, .sc, 0, 0⟩
  | wx => ⟨.schreiben, false, .na, 0, 1⟩
  | wy => ⟨.schreiben, true, .sc, 0, 1⟩
  | ry => ⟨.lesen, true, .sc, 1, 0⟩
  | rx => ⟨.lesen, false, .na, 1, 0⟩

@[reducible] def mpPo (a b : MpEv) : Prop :=
  (a = ix ∧ b ≠ ix) ∨ (a = iy ∧ b ≠ ix ∧ b ≠ iy) ∨ (a = wx ∧ b = wy) ∨ (a = ry ∧ b = rx)

@[reducible] def mpRf (a b : MpEv) : Prop := (a = wy ∧ b = ry) ∨ (a = wx ∧ b = rx)

@[reducible] def mpMo (a b : MpEv) : Prop := (a = ix ∧ b = wx) ∨ (a = iy ∧ b = wy)

/-- Happens-before of this graph: program order and thread 1 before thread 2. -/
@[reducible] def mpHb (a b : MpEv) : Prop :=
  mpPo a b ∨ ((a = wx ∨ a = wy) ∧ (b = ry ∨ b = rx))

/-- The extended coherence order of this graph. -/
@[reducible] def mpEco (a b : MpEv) : Prop :=
  (a = ix ∧ (b = wx ∨ b = rx)) ∨ (a = iy ∧ (b = wy ∨ b = ry)) ∨ (a = wx ∧ b = rx) ∨
    (a = wy ∧ b = ry)

def mpRang : MpEv → Nat
  | ix => 0
  | iy => 1
  | wx => 2
  | wy => 3
  | ry => 4
  | rx => 5

def mpGraph : Graph MpEv Bool Nat := ⟨mpLab, mpPo, mpRf, mpMo⟩

theorem mp_wf : mpGraph.Wohlgeformt where
  po_trans := by
    intro a b c
    show mpPo a b → mpPo b c → mpPo a c
    cases a <;> cases b <;> cases c <;> decide
  po_irrefl := by
    intro a
    show ¬ mpPo a a
    cases a <;> decide
  rf_schreibt := by
    rintro w r (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> exact trivial
  rf_liest := by
    rintro w r (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> exact trivial
  rf_ort := by
    rintro w r (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> rfl
  rf_wert := by
    rintro w r (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> rfl
  rf_eindeutig := by
    rintro w w' r (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) (⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
      first | exact h1.symm | exact absurd h2 (by decide)
  mo_schreibt := by
    rintro a b (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> exact ⟨trivial, trivial⟩
  mo_ort := by
    rintro a b (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> rfl
  mo_trans := by
    intro a b c
    show mpMo a b → mpMo b c → mpMo a c
    cases a <;> cases b <;> cases c <;> decide
  mo_irrefl := by
    intro a
    show ¬ mpMo a a
    cases a <;> decide
  mo_total := by
    intro a b ha hb ho hne
    show mpMo a b ∨ mpMo b a
    cases a <;> cases b <;>
      first
        | decide
        | exact False.elim ha
        | exact False.elim hb
        | exact absurd rfl hne
        | (simp only [Graph.ort, mpGraph, mpLab, Bool.false_eq_true, Bool.true_eq_false] at ho; done)

theorem mp_kein_rmw (u : MpEv) : ¬ mpGraph.istRmw u := by
  intro hu
  cases u <;> simp only [Graph.istRmw, mpGraph, mpLab, reduceCtorEq] at hu

theorem mp_hb {a b : MpEv} (h : mpGraph.hb a b) : mpHb a b := by
  have htr : ∀ x y z, mpHb x y → mpHb y z → mpHb x z := by
    intro x y z
    cases x <;> cases y <;> cases z <;> decide
  refine transGen_von_trans htr (transGen_mono (fun x y hxy => ?_) h)
  rcases hxy with hpo | hsw
  · exact Or.inl hpo
  · obtain ⟨z, hz, hzy⟩ := Graph.sw_ohne_rmw mp_kein_rmw hsw
    revert hz hzy
    show (x = z ∨ mpPo x z) → mpRf z y → mpHb x y
    cases x <;> cases z <;> cases y <;> decide

theorem mp_rb_leer {r w : MpEv} (h : mpGraph.rb r w) : False := by
  obtain ⟨w', h1, h2, -⟩ := h
  revert h1 h2
  show mpRf w' r → mpMo w' w → False
  cases w' <;> cases r <;> cases w <;> decide

theorem mp_eco {a b : MpEv} (h : mpGraph.eco a b) : mpEco a b := by
  have htr : ∀ x y z, mpEco x y → mpEco y z → mpEco x z := by
    intro x y z
    cases x <;> cases y <;> cases z <;> decide
  refine transGen_von_trans htr (transGen_mono (fun x y hxy => ?_) h)
  rcases hxy with h | h | h
  · revert h
    show mpRf x y → mpEco x y
    cases x <;> cases y <;> decide
  · revert h
    show mpMo x y → mpEco x y
    cases x <;> cases y <;> decide
  · exact (mp_rb_leer h).elim

theorem mp_hb_rang {a b : MpEv} (h : mpHb a b) : mpRang a < mpRang b := by
  revert h
  cases a <;> cases b <;> decide

theorem mp_konsistent : mpGraph.Konsistent where
  wf := mp_wf
  hb_irrefl := by
    intro a h
    exact Nat.lt_irrefl _ (mp_hb_rang (mp_hb h))
  kohaerent := by
    intro a b h1 h2
    have hp := mp_hb h1
    have he := mp_eco h2
    revert hp he
    cases a <;> cases b <;> decide
  atomar := fun _ u _ _ hu _ => absurd hu (mp_kein_rmw u)
  psc := by
    refine azyklisch_von_rang mpRang (fun a b h => ?_)
    obtain ⟨-, -, h⟩ := h
    rcases h with h | ⟨c, d, h1, -, h3, h4, -⟩ | ⟨h1, -⟩ | h | h
    · exact mp_hb_rang (Or.inl h)
    · exact Nat.lt_trans (mp_hb_rang (Or.inl h1))
        (Nat.lt_trans (mp_hb_rang (mp_hb h3)) (mp_hb_rang (Or.inl h4)))
    · exact mp_hb_rang (mp_hb h1)
    · revert h
      show mpMo a b → mpRang a < mpRang b
      cases a <;> cases b <;> decide
    · exact (mp_rb_leer h).elim
  ohneLB := by
    refine azyklisch_von_rang mpRang ?_
    intro a b
    show mpPo a b ∨ mpRf a b → mpRang a < mpRang b
    cases a <;> cases b <;> decide

theorem mp_nur_sc : mpGraph.NurSC := by
  intro a
  cases a
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The data write happens before the data read: through the `seq_cst` flag. -/
theorem mp_hb_wx_rx : mpGraph.hb wx rx :=
  mpGraph.hb_trans
    (mpGraph.hb_trans (mpGraph.hb_von_po (show mpPo wx wy by decide))
      (mpGraph.hb_von_sw (a := wy) (b := ry)
        ⟨trivial, trivial, trivial, trivial, wy, .selbst trivial,
        show mpRf wy ry by decide⟩))
    (mpGraph.hb_von_po (show mpPo ry rx by decide))

theorem mp_rennfrei : mpGraph.Rennfrei := by
  rintro a b ⟨hne, ho, hw⟩ hna
  cases a <;> cases b <;>
    first
      | exact absurd rfl hne
      | exact Or.inl (mpGraph.hb_von_po (show mpPo _ _ by decide))
      | exact Or.inr (mpGraph.hb_von_po (show mpPo _ _ by decide))
      | exact Or.inl mp_hb_wx_rx
      | exact Or.inr mp_hb_wx_rx
      | (simp only [Graph.ort, mpGraph, mpLab, Bool.false_eq_true, Bool.true_eq_false] at ho; done)
      | (simp only [Graph.na, Graph.modus, mpGraph, mpLab, reduceCtorEq, or_self] at hna; done)
      | (simp only [Graph.schreibt, mpGraph, mpLab, Art.schreibt, or_self] at hw; done)

/-- **Satisfiability of the premises of `drf_sc`**: a consistent graph with only `seq_cst`
    atomics and no race, containing a `seq_cst` access and a conflicting pair on a plain
    carrier. -/
theorem drf_sc_erfuellbar :
    ∃ G : Graph MpEv Bool Nat, G.Konsistent ∧ G.NurSC ∧ G.Rennfrei ∧ (∃ a, G.sc a) ∧
      ∃ a b, G.Konflikt a b ∧ G.na a ∧ G.na b :=
  ⟨mpGraph, mp_konsistent, mp_nur_sc, mp_rennfrei, ⟨wy, rfl⟩,
    wx, rx, ⟨by decide, rfl, Or.inl trivial⟩, rfl, rfl⟩

end Gabbro.Core.Speicher
