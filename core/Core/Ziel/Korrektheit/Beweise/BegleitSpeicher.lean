/-
  File:      core/Core/Ziel/Korrektheit/Beweise/BegleitSpeicher.lean
  Subject:   COMPANION LEMMAS for the pinned statements of `Core/Ziel/Korrektheit/Speicher.lean`
              (memory layer, M3): for every `…Aussage` an `X.erfuellbar` (the premises hold jointly)
              and an `X.nichtTrivial` (the statement is sharp: a weaker form fails, or a refused
              object violates it). No statement is changed; every proof reuses an existing witness
              (`graphmaschine_erfuellbar`, `mp_konsistent`, `sb_sc_inkonsistent`, `kohaerenz_katalog`,
              `liest_vorher_nichtTrivial`, `ir_konsistent`, `ir_kein_sc`, `iriw_ra_erlaubt`,
              `iriw_sc_verboten`, `leer_konsistent`) or the proved main theorem.
-/
module

public import Core.Ziel.Korrektheit.Speicher
public import Core.Speicher.Graphmaschine
public import Core.Speicher.GraphmaschineErfuellbar
public import Core.Speicher.Trennung
public import Core.Ziel.Korrektheit.Beweise.Graphmaschine
public import Core.Ziel.Korrektheit.Beweise.Kohaerenz
public import Core.Ziel.Korrektheit.Beweise.Rmw
public import Core.Ziel.Korrektheit.Beweise.Iriw

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core
open Gabbro.Core.Speicher
open IriwEv

/-- The premises of the graph-machine equivalence hold jointly: the message-passing graph is
    produced by a run and is consistent, complete and thread-ordered. Feeds:
    `graphmaschine_erfuellbar`, `mp_konsistent`, `mp_vollstaendig`, `mp_faden_po`. -/
theorem GraphmaschineAequivalentAussage.erfuellbar :
    ∃ (E F Ort Wert : Type) (_ : Finite E) (G : Speicher.Graph E Ort Wert) (th : E → F),
      Speicher.Zustand.Erzeugt G th ∧
      (G.Konsistent ∧ G.Vollstaendig ∧
        ∀ a b, th a = th b → a ≠ b → G.po a b ∨ G.po b a) :=
  ⟨MpEv, Nat, Bool, Nat, inferInstance, mpGraph, mpFaden, graphmaschine_erfuellbar,
    mp_konsistent, mp_vollstaendig, mp_faden_po⟩

/-- The equivalence is sharp: the store-buffering graph with `seq_cst` is refused by the model
    and produced by no run. Feeds: `sb_sc_inkonsistent`, `Einbettung.symm`,
    `Zustand.erreichbar_gut`. Proof sketch: a run producing it would transport consistency back
    along the inverse bijective embedding. -/
theorem GraphmaschineAequivalentAussage.nichtTrivial :
    ∃ (E F Ort Wert : Type) (G : Speicher.Graph E Ort Wert) (th : E → F),
      ¬ Speicher.Zustand.Erzeugt G th := by
  refine ⟨SbEv, Nat, Bool, Nat, sbGraph .sc, fun _ => 0, ?_⟩
  rintro ⟨Z, hZ, e, hbij, _, heinb⟩
  have hgut := Speicher.Zustand.erreichbar_gut hZ
  have hsymm := heinb.symm hbij
  exact sb_sc_inkonsistent (hsymm.konsistent hgut.1)

/-- The premises of the coherence catalogue hold jointly: the message-passing graph is
    consistent, hence satisfies all four axioms. Feeds: `mp_konsistent`, `kohaerenz_katalog`. -/
theorem KohaerenzKatalogAussage.erfuellbar :
    ∃ (E Ort Wert : Type) (G : Speicher.Graph E Ort Wert), G.Konsistent ∧
      (∀ w₁ w₂ : E, G.po w₁ w₂ → G.schreibt w₁ → G.schreibt w₂ → G.ort w₁ = G.ort w₂ →
        ¬ G.mo w₂ w₁)
      ∧ (∀ w w' r : E, G.po w r → G.rf w' r → G.schreibt w → G.ort w = G.ort r → w ≠ w' →
        ¬ G.mo w' w)
      ∧ (∀ r w w' : E, G.po r w → G.rf w' r → G.schreibt w → G.ort w = G.ort r → w ≠ w' →
        ¬ G.mo w w')
      ∧ (∀ r₁ r₂ w₁ w₂ : E, G.po r₁ r₂ → G.rf w₂ r₁ → G.rf w₁ r₂ → ¬ G.mo w₁ w₂) :=
  ⟨MpEv, Bool, Nat, mpGraph, mp_konsistent,
    kohaerenz_katalog MpEv Bool Nat mpGraph mp_konsistent⟩

/-- The consistency premise is load-bearing: some graph is inconsistent. Feeds:
    `sb_sc_inkonsistent`. -/
theorem KohaerenzKatalogAussage.nichtTrivial :
    ∃ (E Ort Wert : Type) (G : Speicher.Graph E Ort Wert), ¬ G.Konsistent :=
  ⟨SbEv, Bool, Nat, sbGraph .sc, sb_sc_inkonsistent⟩

/-- The premises of read-modify-write atomicity hold jointly: some graph is consistent. Feeds:
    `mp_konsistent`. -/
theorem RmwNichtDoppeltAussage.erfuellbar :
    ∃ (E Ort Wert : Type) (G : Speicher.Graph E Ort Wert), G.Konsistent :=
  ⟨MpEv, Bool, Nat, mpGraph, mp_konsistent⟩

/-- The new atomicity field is not implied by the old ones: the three-event graph satisfies
    every old field and violates `liest_vorher`. Feeds: `liest_vorher_nichtTrivial`. -/
theorem RmwNichtDoppeltAussage.nichtTrivial :
    ∃ (w u : RmwEv), rmwGraph.rf w u ∧ rmwGraph.istRmw u ∧ ¬ rmwGraph.mo w u := by
  obtain ⟨-, -, -, -, -, -, w, u, hrf, hrmw, hmo⟩ := liest_vorher_nichtTrivial
  exact ⟨w, u, hrf, hrmw, hmo⟩

/-- The premises of the `seq_cst` IRIW ban hold jointly: the empty graph is consistent and
    vacuously all-`seq_cst`. Feeds: `Zustand.leer_konsistent`, `Zustand.leer_elim`. -/
theorem IriwScVerbotenAussage.erfuellbar :
    ∃ (E Ort Wert : Type) (G : Speicher.Graph E Ort Wert),
      G.Konsistent ∧ ∀ a, G.sc a :=
  ⟨_, _, _, _, Zustand.leer_konsistent, fun a => (Zustand.leer_elim a).elim⟩

/-- The ban is sharp: the same disagreeing-readers shape occurs in a consistent graph below
    `seq_cst`. Feeds: `ir_konsistent`, `ir_kein_sc`. Proof sketch: the release/acquire IRIW
    graph with its six shape edges and one non-`seq_cst` event. -/
theorem IriwScVerbotenAussage.nichtTrivial :
    ∃ (E Ort Wert : Type) (G : Speicher.Graph E Ort Wert) (wx wy r1x r1y r2y r2x : E),
      G.Konsistent ∧ G.rf wx r1x ∧ G.po r1x r1y ∧ G.rb r1y wy ∧
        G.rf wy r2y ∧ G.po r2y r2x ∧ G.rb r2x wx ∧ (∃ a, ¬ G.sc a) := by
  refine ⟨IriwEv, Bool, Nat, irGraph .ra, irWX, irWY, irR1X, irR1Y, irR2Y, irR2X,
    ir_konsistent, ?_, ?_, ?_, ?_, ?_, ?_, irWX, ir_kein_sc _⟩
  · show irRf irWX irR1X
    decide
  · show irPo irR1X irR1Y
    decide
  · exact ⟨irIY, Or.inr (Or.inl ⟨rfl, rfl⟩), Or.inr ⟨rfl, rfl⟩, by decide⟩
  · show irRf irWY irR2Y
    decide
  · show irPo irR2Y irR2X
    decide
  · exact ⟨irIX, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)), Or.inl ⟨rfl, rfl⟩, by decide⟩

/-- The allowed IRIW shape is witnessed: the release/acquire graph. Feeds:
    `iriw_ra_erlaubt`. -/
theorem IriwRaErlaubtAussage.erfuellbar : IriwRaErlaubtAussage :=
  iriw_ra_erlaubt

/-- The allowance is sharp: with `seq_cst` the same shape is impossible. Feeds:
    `iriw_sc_verboten`. -/
theorem IriwRaErlaubtAussage.nichtTrivial : IriwScVerbotenAussage :=
  iriw_sc_verboten

end Gabbro.Core.Ziel.Korrektheit
