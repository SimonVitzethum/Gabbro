/-
  File:      core/Core/Ziel/Korrektheit/Beweise/Rmw.lean
  Subject:   The pinned `RmwNichtDoppeltAussage` is FALSE over the consistency predicate as it stands.
             Its proof sketch in `Core/Ziel/Korrektheit/Speicher.lean` invokes the `atomar` field of
             `Konsistent`, `liest_mo_max` and `Wohlgeformt.mo_total`; none of them puts the write an update
             reads BEFORE that update in `mo`. `atomar` only forbids a write strictly between the source and
             the update. The three-event graph built below has both updates mo-before their common source,
             discharges every field of `Konsistent` and gives two distinct updates reading one write.

  Feeding statements and what they do / do not give:
    * `Core/Speicher/Konsistent.lean`, `Konsistent.atomar`:
        `rf w u → istRmw u → mo w w' → ¬ mo w' u`. Vacuous when `mo u w`, which the field does not exclude.
    * `Core/Speicher/Relationen.lean`, `Wohlgeformt.mo_total`: orders the two updates, but only relative to
        each other, never relative to the source they read.
    * `Core/Speicher/Kohaerenz.lean`, `liest_mo_max` and `hb_mo`: need `hb` from a write to the reader. In the
        graph below `hb` is empty (no `po`, every mode relaxed), so both are inert.
    * `Core/Speicher/Relationen.lean`, `hb_von_po`, `eco_von_rf`, `eco_von_mo`, `eco_von_rb` and the
      `azyklisch_von_rang` / `azyklisch_mono` helpers of `Core/Speicher/Basis.lean` discharge the remaining
      fields.

  Proof sketch of the refutation: take `E = RmwEv` with a plain write `w` and two updates `u₁`, `u₂` reading
  `w`, `po` empty, every access relaxed, and `mo` the chain `u₁ < u₂ < w`. Then `mo w x` holds for no `x`, so
  `atomar` is vacuous; `hb` and `psc` are empty; `rf` strictly increases the rank `w ↦ 0, uᵢ ↦ 1`, so
  `ohneLB` holds. Instantiating the pinned statement at this graph at `w, u₁, u₂` forces `u₁ = u₂`, which is
  false by construction. The missing consistency premise is `rf w u → istRmw u → mo w u` (RC11's
  `irreflexiv (rf ; mo)` half of RMW atomicity); with it, the mo-later update contradicts `atomar`.
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

/-- The counterexample graph is RC11-consistent as the model defines it: the `atomar` field is vacuous
    because the source is `mo`-maximal, `hb` and `psc` are empty, and `rf` strictly increases `rmwRang`. -/
theorem rmwKonsistent : rmwGraph.Konsistent where
  wf := rmwWf
  hb_irrefl := fun a h => rmwHbFalsch a a h
  kohaerent := by
    intro a b h _
    exact False.elim (rmwHbFalsch a b h)
  atomar := by
    intro w _ w' hrf _ hmo _
    rcases hrf with ⟨rfl, _⟩
    exact False.elim (rmwMoKeinVonW w' hmo)
  psc := azyklisch_mono (fun a b h => False.elim (rmwPscFalsch a b h)) azyklischLeer
  ohneLB := by
    refine azyklisch_von_rang rmwRang ?_
    intro a b h
    rcases h with hpo | hrf
    · exact False.elim hpo
    · rcases hrf with ⟨rfl, (rfl | rfl)⟩ <;> decide

/-- `RmwNichtDoppeltAussage` is false: two distinct updates read the same write in a consistent graph.
    The missing premise is `rf w u → istRmw u → mo w u` (equivalently `irreflexiv (rf ; mo)`), the first
    half of RC11's atomicity axiom; the pinned statement's proof sketch silently assumes it. -/
theorem rmwNichtDoppelt_falsch : ¬ RmwNichtDoppeltAussage := by
  intro h
  have heq := h RmwEv Bool Nat rmwGraph rmwKonsistent RmwEv.w RmwEv.u1 RmwEv.u2
    ⟨rfl, Or.inl rfl⟩ ⟨rfl, Or.inr rfl⟩ rfl rfl
  cases heq

end Gabbro.Core.Ziel.Korrektheit
