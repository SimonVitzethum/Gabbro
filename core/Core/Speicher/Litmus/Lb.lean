/-
  File:      core/Core/Speicher/Litmus/Lb.lean
  Subject:   LOAD BUFFERING (LB) catalogue entry: the two-thread shape
             `rY := y; x := 1 ‖ rX := x; y := 1` in which each read observes the other thread's
             later write (`r1 = r2 = 1`).

  Source: Lahav et al., "Repairing Sequential Consistency in C/C++11" (PLDI 2017), the standard LB
  test, and the RC11 model the paper repairs (Batty et al.; herd catalogue). RC11 strengthens
  no-thin-air to acyclicity of `po ∪ rf`, so `ohneLB` forbids this outcome.

  Modes: FORBIDDEN in every mode (`na`, `rlx`, `ra`, `sc`); the generic theorem takes no mode premise.
  ALLOWED here means the same program shape with a non-LB outcome: both reads observe the initial
  writes, so each read is `rb`-before the other thread's write. A consistent and complete graph
  with that outcome witnesses that the ban is not vacuous.

  Expected: FORBIDDEN (the `1,1` outcome), ALLOWED (the `0,0` outcome). A mismatch with the
  literature would be a model finding; the negation would be proved here and reported, never
  patched over.
-/
module

public import Core.Speicher.Trennung
public import Core.Speicher.Einbettung

@[expose] public section

namespace Gabbro.Core.Speicher

/-- **Load buffering is forbidden in every mode.** Thread 1 reads `r₁` then writes `w₁`; thread 2
    reads `r₂` then writes `w₂`. It is impossible that `r₁` reads from `w₂` and `r₂` reads from `w₁`.
    Feeds: `Graph.lb_verboten` (`ohneLB`). -/
def LbVerbotenAussage : Prop :=
  ¬ ∃ (E Ort Wert : Type) (G : Graph E Ort Wert), G.Konsistent ∧
    ∃ r₁ w₁ r₂ w₂ : E, G.po r₁ w₁ ∧ G.rf w₁ r₂ ∧ G.po r₂ w₂ ∧ G.rf w₂ r₁

theorem lb_verboten_kat : LbVerbotenAussage := by
  rintro ⟨E, Ort, Wert, G, hk, r₁, w₁, r₂, w₂, p₁, f₁, p₂, f₂⟩
  exact Graph.lb_verboten hk p₁ f₁ p₂ f₂

/-! ## The load-buffering graph with the non-LB outcome -/

/-- The six events: the initial writes `iX`, `iY`; thread 1 `rY; wX`; thread 2 `rX; wY`. -/
inductive LbEv where
  | iX | iY | rY | wX | rX | wY
  deriving DecidableEq, Repr

open LbEv

/-- Location `false` is `x`, `true` is `y`. Both reads observe `0`; each thread writes `1` after
    its read. Every access carries the mode `m`. -/
def lbLab (m : Modus) : LbEv → Etikett Bool Nat
  | iX => ⟨.schreiben, false, m, 0, 0⟩
  | iY => ⟨.schreiben, true, m, 0, 0⟩
  | rY => ⟨.lesen, true, m, 0, 0⟩
  | wX => ⟨.schreiben, false, m, 0, 1⟩
  | rX => ⟨.lesen, false, m, 0, 0⟩
  | wY => ⟨.schreiben, true, m, 0, 1⟩

abbrev lbPo (a b : LbEv) : Prop :=
  (a = iX ∧ b ≠ iX) ∨ (a = iY ∧ b ≠ iX ∧ b ≠ iY) ∨
    (a = rY ∧ b = wX) ∨ (a = rX ∧ b = wY)

abbrev lbRf (a b : LbEv) : Prop := (a = iY ∧ b = rY) ∨ (a = iX ∧ b = rX)

abbrev lbMo (a b : LbEv) : Prop := (a = iX ∧ b = wX) ∨ (a = iY ∧ b = wY)

/-- The extended coherence order of this graph, in closed form. -/
abbrev lbEco (a b : LbEv) : Prop :=
  (a = iX ∧ (b = wX ∨ b = rX)) ∨ (a = rX ∧ b = wX) ∨
    (a = iY ∧ (b = wY ∨ b = rY)) ∨ (a = rY ∧ b = wY)

def lbRang : LbEv → Nat
  | iX => 0
  | iY => 1
  | rY => 2
  | wX => 3
  | rX => 4
  | wY => 5

def lbGraph (m : Modus) : Graph LbEv Bool Nat := ⟨lbLab m, lbPo, lbRf, lbMo⟩

theorem lb_wf (m : Modus) : (lbGraph m).Wohlgeformt where
  po_trans := by
    intro a b c
    show lbPo a b → lbPo b c → lbPo a c
    cases a <;> cases b <;> cases c <;> decide
  po_irrefl := by
    intro a
    show ¬ lbPo a a
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
    show lbMo a b → lbMo b c → lbMo a c
    cases a <;> cases b <;> cases c <;> decide
  mo_irrefl := by
    intro a
    show ¬ lbMo a a
    cases a <;> decide
  mo_total := by
    intro a b ha hb ho hne
    show lbMo a b ∨ lbMo b a
    cases a <;> cases b <;>
      first
        | decide
        | exact False.elim ha
        | exact False.elim hb
        | exact absurd rfl hne
        | (simp only [Graph.ort, lbGraph, lbLab, Bool.false_eq_true, Bool.true_eq_false] at ho; done)

theorem lb_kein_rmw (m : Modus) (u : LbEv) : ¬ (lbGraph m).istRmw u := by
  intro hu
  cases u <;> simp only [Graph.istRmw, lbGraph, lbLab, reduceCtorEq] at hu

/-- With `.rlx` no event is strong, so there is no `sw` edge. -/
theorem lb_kein_sw (a b : LbEv) : ¬ (lbGraph .rlx).sw a b := by
  intro h
  rcases h with ⟨_, hs, _, _, _, _⟩
  cases a <;> exact hs

/-- Without `sw`, happens-before is program order. -/
theorem lb_hb {a b : LbEv} (h : (lbGraph .rlx).hb a b) : lbPo a b := by
  have htr : ∀ x y z, lbPo x y → lbPo y z → lbPo x z := by
    intro x y z
    cases x <;> cases y <;> cases z <;> decide
  refine transGen_von_trans htr (transGen_mono (fun x y hxy => ?_) h)
  rcases hxy with hpo | hsw
  · exact hpo
  · exact False.elim (lb_kein_sw x y hsw)

theorem lb_rb {m : Modus} {r w : LbEv} (h : (lbGraph m).rb r w) :
    (r = rY ∧ w = wY) ∨ (r = rX ∧ w = wX) := by
  obtain ⟨w', h1, h2, -⟩ := h
  revert h1 h2
  show lbRf w' r → lbMo w' w → _
  cases w' <;> cases r <;> cases w <;> decide

theorem lb_eco_schritt {m : Modus} {a b : LbEv} (h : (lbGraph m).ecoSchritt a b) : lbEco a b := by
  rcases h with h | h | h
  · revert h
    show lbRf a b → lbEco a b
    cases a <;> cases b <;> decide
  · revert h
    show lbMo a b → lbEco a b
    cases a <;> cases b <;> decide
  · rcases lb_rb h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem lb_eco {m : Modus} {a b : LbEv} (h : (lbGraph m).eco a b) : lbEco a b := by
  have htr : ∀ x y z, lbEco x y → lbEco y z → lbEco x z := by
    intro x y z
    cases x <;> cases y <;> cases z <;> decide
  exact transGen_von_trans htr (transGen_mono (fun _ _ h => lb_eco_schritt h) h)

theorem lb_kein_sc (e : LbEv) : ¬ (lbGraph .rlx).sc e := by
  cases e <;> simp only [Graph.sc, Graph.modus, lbGraph, lbLab, reduceCtorEq] <;> trivial

/-- The relaxed graph with the old-value reads is RC11-consistent. -/
theorem lb_konsistent : (lbGraph .rlx).Konsistent where
  wf := lb_wf .rlx
  hb_irrefl := by
    intro a h
    have hp := lb_hb h
    revert hp
    cases a <;> decide
  kohaerent := by
    intro a b hab he
    have hp := lb_hb hab
    have he' := lb_eco he
    revert hp he'
    cases a <;> cases b <;> decide
  atomar := by
    intro w u _ _ hu
    exact absurd hu (lb_kein_rmw .rlx u)
  psc := by
    intro a h
    obtain ⟨c, hc⟩ := transGen_kopf h
    exact (lb_kein_sc a) hc.1
  ohneLB := by
    refine azyklisch_von_rang lbRang ?_
    intro a b
    show lbPo a b ∨ lbRf a b → lbRang a < lbRang b
    cases a <;> cases b <;> decide
  liest_vorher := by
    intro w u _ hu
    exact absurd hu (lb_kein_rmw .rlx u)

theorem lb_vollstaendig : (lbGraph .rlx).Vollstaendig := by
  intro r hr
  cases r with
  | iX => exact (hr : False).elim
  | iY => exact (hr : False).elim
  | rY => exact ⟨iY, Or.inl ⟨rfl, rfl⟩⟩
  | wX => exact (hr : False).elim
  | rX => exact ⟨iX, Or.inr ⟨rfl, rfl⟩⟩
  | wY => exact (hr : False).elim

/-- **The load-buffering outcome is allowed in the `0,0` form.** Some consistent and complete graph
    has the two program-order read-then-write pairs and both reads `rb`-before the other thread's
    write. Feeds: `lb_konsistent`, `lb_vollstaendig`. -/
def LbErlaubtAussage : Prop :=
  ∃ (E Ort Wert : Type) (G : Graph E Ort Wert),
    G.Konsistent ∧ G.Vollstaendig ∧
      ∃ r₁ w₁ r₂ w₂ : E, G.po r₁ w₁ ∧ G.po r₂ w₂ ∧ G.rb r₂ w₁ ∧ G.rb r₁ w₂

theorem lb_erlaubt_kat : LbErlaubtAussage := by
  refine ⟨LbEv, Bool, Nat, lbGraph .rlx, lb_konsistent, lb_vollstaendig,
    rY, wX, rX, wY, ?_, ?_, ?_, ?_⟩
  · show lbPo rY wX
    decide
  · show lbPo rX wY
    decide
  · exact ⟨iX, Or.inr ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩, by decide⟩
  · exact ⟨iY, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩, by decide⟩

/-- The ban is not vacuous: the same program shape occurs in a consistent graph. -/
theorem lb_verboten_nichtTrivial :
    ∃ (E Ort Wert : Type) (G : Graph E Ort Wert), G.Konsistent ∧
      ∃ r₁ w₁ r₂ w₂ : E, G.po r₁ w₁ ∧ G.po r₂ w₂ := by
  refine ⟨LbEv, Bool, Nat, lbGraph .rlx, lb_konsistent, rY, wX, rX, wY, ?_, ?_⟩
  · show lbPo rY wX
    decide
  · show lbPo rX wY
    decide

/-- **The load-buffering litmus statement.** The general ban and the non-LB allowance. -/
def LbLitmusAussage : Prop := LbVerbotenAussage ∧ LbErlaubtAussage

theorem lb_litmus : LbLitmusAussage := ⟨lb_verboten_kat, lb_erlaubt_kat⟩

end Gabbro.Core.Speicher
