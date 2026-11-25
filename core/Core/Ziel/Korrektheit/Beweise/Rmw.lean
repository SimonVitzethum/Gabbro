/-
  File:      core/Core/Ziel/Korrektheit/Beweise/Rmw.lean
  Subject:   THE PROOF of the pinned `RmwNichtDoppeltAussage`: over the strengthened consistency
             predicate two updates never read the same write. Its proof uses both halves of RC11
             atomicity: `liest_vorher` puts each update `mo`-after the write it reads,
             `Wohlgeformt.mo_total` orders the two updates, and the later one then reads a write
             that the earlier one precedes, contradicting `atomar`.

  The three-event graph below (an initial write `w` and two updates `u₁`, `u₂` reading `w`,
  with `mo` the chain `u₁ < u₂ < w`) satisfies every OLD field -- `atomar` is vacuous because
  no write is `mo`-after the source, `hb` and `psc` are empty, `rf` strictly increases the
  rank -- and violates the new `liest_vorher` field. It stays as the non-triviality witness
  `liest_vorher_nichtTrivial`: the new field is not implied by the old ones.
-/
module

public import Core.Ziel.Korrektheit.Speicher

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core
open Gabbro.Core.Speicher

/-- One initial write `w` of a location and two updates `u₁`, `u₂` that both read `w`. -/
inductive RmwEv where
  | w
  | u1
  | u2
  deriving DecidableEq, Repr

/-- The labels: `w` writes value `1`, each update reads `1` and writes `1`; every access is relaxed. -/
def rmwLab : RmwEv → Etikett Bool Nat
  | RmwEv.w => ⟨.schreiben, true, .rlx, 0, 1⟩
  | RmwEv.u1 => ⟨.rmw, true, .rlx, 1, 1⟩
  | RmwEv.u2 => ⟨.rmw, true, .rlx, 1, 1⟩

/-- No program order at all. -/
@[reducible] def rmwPo (_a _b : RmwEv) : Prop := False

/-- Both updates read the initial write `w`. -/
@[reducible] def rmwRf (a b : RmwEv) : Prop :=
  a = RmwEv.w ∧ (b = RmwEv.u1 ∨ b = RmwEv.u2)

/-- Modification order is the chain `u₁ < u₂ < w`: the source `w` comes LAST, after both updates. -/
@[reducible] def rmwMo (a b : RmwEv) : Prop :=
  (a = RmwEv.u1 ∧ (b = RmwEv.u2 ∨ b = RmwEv.w)) ∨ (a = RmwEv.u2 ∧ b = RmwEv.w)

/-- Every `rf` edge goes from rank `0` to rank `1`; this is the rank for `ohneLB`. -/
def rmwRang : RmwEv → Nat
  | RmwEv.w => 0
  | RmwEv.u1 => 1
  | RmwEv.u2 => 1

def rmwGraph : Graph RmwEv Bool Nat := ⟨rmwLab, rmwPo, rmwRf, rmwMo⟩

/-- The graph is well formed: `mo` is a strict total order on the three writes of the one location,
    `rf` has one source per update and carries the written value. -/
theorem rmwWf : rmwGraph.Wohlgeformt where
  po_trans := by
    intro _ _ _ h
    exact False.elim h
  po_irrefl := by
    intro _ h
    exact False.elim h
  rf_schreibt := by
    rintro _ _ ⟨rfl, _⟩
    exact trivial
  rf_liest := by
    rintro _ _ ⟨rfl, (rfl | rfl)⟩ <;> exact trivial
  rf_ort := by
    rintro _ _ ⟨rfl, (rfl | rfl)⟩ <;> rfl
  rf_wert := by
    rintro _ _ ⟨rfl, (rfl | rfl)⟩ <;> rfl
  rf_eindeutig := by
    intro w w' _ h1 h2
    rcases h1 with ⟨h1, _⟩
    rcases h2 with ⟨h2, _⟩
    rw [h1, h2]
  mo_schreibt := by
    rintro _ _ (⟨rfl, (rfl | rfl)⟩ | ⟨rfl, rfl⟩) <;> exact ⟨trivial, trivial⟩
  mo_ort := by
    rintro _ _ (⟨rfl, (rfl | rfl)⟩ | ⟨rfl, rfl⟩) <;> rfl
  mo_trans := by
    intro a b c
    show rmwMo a b → rmwMo b c → rmwMo a c
    cases a <;> cases b <;> cases c <;> decide
  mo_irrefl := by
    intro a
    show ¬ rmwMo a a
    cases a <;> decide
  mo_total := by
    intro a b _ _ _ hne
    show rmwMo a b ∨ rmwMo b a
    cases a <;> cases b <;> first | decide | exact absurd rfl hne

/-- Every `hb` step is impossible: `po` is empty and every mode is relaxed, so `sw` is empty. -/
theorem rmwHbSchrittFalsch (a b : RmwEv) : ¬ rmwGraph.hbSchritt a b := by
  intro h
  rcases h with hpo | hsw
  · exact False.elim hpo
  · rcases hsw with ⟨_, hstark, _, _, _⟩
    cases a <;> simp only [Graph.modus, rmwGraph, rmwLab, Modus.stark] at hstark <;>
      exact False.elim hstark

/-- Happens-before is empty in this graph. -/
theorem rmwHbFalsch (a b : RmwEv) : ¬ rmwGraph.hb a b := by
  intro h
  induction h with
  | single hs => exact rmwHbSchrittFalsch _ _ hs
  | tail _ _ ih => exact ih

/-- The `psc` relation is empty: no access is `seq_cst`. -/
theorem rmwPscFalsch (a b : RmwEv) : ¬ rmwGraph.psc a b := by
  intro h
  obtain ⟨hsc, _⟩ := h
  cases a <;> simp only [Graph.sc, Graph.modus, rmwGraph, rmwLab, reduceCtorEq] at hsc <;>
    exact False.elim hsc

/-- The empty relation is acyclic. -/
theorem azyklischLeer : Azyklisch (fun _ _ : RmwEv => False) := by
  intro a h
  cases h with
  | single hf => exact False.elim hf
  | tail _ hf => exact False.elim hf

/-- No write is `mo`-after the source `w`: `atomar` is therefore vacuous in this graph. This is exactly the
    half of RC11 atomicity that `Konsistent.atomar` does not state. -/
theorem rmwMoKeinVonW (b : RmwEv) : ¬ rmwMo RmwEv.w b := by
  rintro (⟨h, _⟩ | ⟨h, _⟩) <;> cases h

/-- **ATOMICITY OF READ-MODIFY-WRITE over every consistent graph**: two distinct updates never
    read the same write. Feeds: the `liest_vorher` and `atomar` fields of `Konsistent`,
    `Wohlgeformt.mo_total`. Proof sketch: both updates are `mo`-after the write they read; `mo`
    orders the updates; the later one reads a write that the earlier one precedes, contradicting
    `atomar`. -/
theorem rmw_nicht_doppelt : RmwNichtDoppeltAussage := by
  intro E Ort Wert G hk w u₁ u₂ h1 h2 hrmw1 hrmw2
  have sch : ∀ a, G.istRmw a → G.schreibt a := by
    intro a h
    unfold Graph.schreibt Graph.istRmw at *
    rw [h]
    exact trivial
  have o1 := hk.wf.rf_ort w u₁ h1
  have o2 := hk.wf.rf_ort w u₂ h2
  have ho : G.ort u₁ = G.ort u₂ := o1.symm.trans o2
  have m1 := hk.liest_vorher w u₁ h1 hrmw1
  have m2 := hk.liest_vorher w u₂ h2 hrmw2
  by_cases e : u₁ = u₂
  · exact e
  · rcases hk.wf.mo_total u₁ u₂ (sch u₁ hrmw1) (sch u₂ hrmw2) ho e with h | h
    · exact absurd h (hk.atomar w u₂ u₁ h2 hrmw2 m1)
    · exact absurd h (hk.atomar w u₁ u₂ h1 hrmw1 m2)

/-- **The new field is non-trivial**: the counterexample graph satisfies every old field
    (well-formedness, irreflexive `hb`, coherence, `atomar`, acyclic `psc` and `po ∪ rf`) and
    violates `liest_vorher`: both updates read `w`, but `w` is `mo`-last. -/
theorem liest_vorher_nichtTrivial :
    rmwGraph.Wohlgeformt ∧ (∀ a, ¬ rmwGraph.hb a a) ∧
      (∀ a b, rmwGraph.hb a b → ¬ rmwGraph.eco b a) ∧
      (∀ w u w', rmwGraph.rf w u → rmwGraph.istRmw u → rmwGraph.mo w w' → ¬ rmwGraph.mo w' u) ∧
      Azyklisch rmwGraph.psc ∧ Azyklisch rmwGraph.porf ∧
      ∃ w u, rmwGraph.rf w u ∧ rmwGraph.istRmw u ∧ ¬ rmwGraph.mo w u := by
  refine ⟨rmwWf, fun a h => rmwHbFalsch a a h, fun a b h _ => absurd h (rmwHbFalsch a b),
    ?_, ?_, ?_, RmwEv.w, RmwEv.u1, ⟨rfl, Or.inl rfl⟩, rfl, rmwMoKeinVonW RmwEv.u1⟩
  · intro w _ w' hrf _ hmo _
    rcases hrf with ⟨rfl, _⟩
    exact False.elim (rmwMoKeinVonW w' hmo)
  · exact azyklisch_mono (fun a b h => False.elim (rmwPscFalsch a b h)) azyklischLeer
  · refine azyklisch_von_rang rmwRang ?_
    intro a b h
    rcases h with hpo | hrf
    · exact False.elim hpo
    · rcases hrf with ⟨rfl, (rfl | rfl)⟩ <;> decide

end Gabbro.Core.Ziel.Korrektheit
