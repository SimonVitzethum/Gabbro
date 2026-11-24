/-
  File:      core/Core/Ziel/Korrektheit/Speicher.lean
  Subject:   CORRECTNESS OF THE MEMORY LAYER (M3): the graph machine against the axiomatic model, and the
             catalogue of coherence and litmus results, as pinned propositions.

  What is proved today (`Core/Speicher`): every reachable state of the graph machine is consistent and complete
  (`erreichbar_gut`), its append order is an execution order (`erreichbar_ordnung`), every finite consistent
  complete graph with per-thread program order is produced by a run (`erzeugt`), DRF-SC (`drf_sc`), and the shapes
  store buffering with `seq_cst`, message passing, load buffering and CoRR are excluded (`Litmus.lean`), store
  buffering below `seq_cst` is allowed (`sb_ohne_sc_erlaubt`).

  What the statements below add:
  * `GraphmaschineAequivalentAussage` states the correctness and completeness of the machine as ONE equivalence,
    so that neither half can be weakened silently (an implication would hold for a machine that never moves).
    The forward half needs the transport of consistency along the bijective embedding of `Erzeugt`, which is not
    in the tree yet.
  * the coherence axioms and the atomicity of read-modify-write as separate statements over EVERY consistent
    graph, and the two independent-reads-of-independent-writes results (forbidden for `seq_cst`, allowed below).
  Every statement is a universally quantified property of graphs, never a fixture; the allowed outcomes carry a
  consistent graph as the existential witness, which is what makes the forbidden outcomes non-vacuous.
-/
module

public import Core.Speicher.Graphmaschine
public import Core.Speicher.GraphmaschineVollstaendig
public import Core.Speicher.DRFSC
public import Core.Speicher.Litmus
public import Core.Speicher.Trennung

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core

/-- THE GRAPH MACHINE IS CORRECT AND COMPLETE AGAINST THE AXIOMATIC MODEL, as one equivalence: a finite graph is
produced by a run of the machine (up to renaming of events) exactly when it is RC11-consistent, complete, and its
events of one thread are ordered by program order. Feeds: `Zustand.erreichbar_gut`, `erreichbar_faden`,
`Zustand.erzeugt`, `Graph.Einbettung.konsistent`, `Graph.Einbettung.vollstaendig`. Proof sketch: `←` is
`erzeugt`; `→` transports consistency and completeness along the bijective embedding of `Erzeugt` (needs the
inverse embedding lemma `Einbettung.symm`) and reads program order from `erreichbar_faden`. Non-triviality:
`graphmaschine_erfuellbar` (the message-passing graph is produced) and `sb_sc_inkonsistent` (a graph the model
refuses is not produced). Open: the inverse-embedding lemma (Prover). -/
def GraphmaschineAequivalentAussage : Prop :=
  ∀ (E F Ort Wert : Type) [Finite E] (G : Speicher.Graph E Ort Wert) (th : E → F),
    Speicher.Zustand.Erzeugt G th ↔
      (G.Konsistent ∧ G.Vollstaendig ∧ ∀ a b, th a = th b → a ≠ b → G.po a b ∨ G.po b a)

/-- THE FOUR COHERENCE AXIOMS over every consistent graph: a write cannot precede, in modification order, the
write its own thread already read (CoRW) or wrote (CoWW, CoWR), and a later read never reads an older write
(CoRR, `corr_verboten`). Feeds: `Konsistent.kohaerent`, `Graph.hb_von_po`, `Graph.eco_von_rb`, `corr_verboten`.
Proof sketch: each is `hk.kohaerent` applied to a `po`-ordered pair whose `eco` backward edge the assumption
provides. -/
def KohaerenzKatalogAussage : Prop :=
  ∀ (E Ort Wert : Type) (G : Speicher.Graph E Ort Wert), G.Konsistent →
    (∀ w₁ w₂ : E, G.po w₁ w₂ → G.schreibt w₁ → G.schreibt w₂ → G.ort w₁ = G.ort w₂ → ¬ G.mo w₂ w₁)
  ∧ (∀ w w' r : E, G.po w r → G.rf w' r → G.schreibt w → G.ort w = G.ort r → w ≠ w' → ¬ G.mo w' w)
  ∧ (∀ r w w' : E, G.po r w → G.rf w' r → G.schreibt w → G.ort w = G.ort r → w ≠ w' → ¬ G.mo w w')
  ∧ (∀ r₁ r₂ w₁ w₂ : E, G.po r₁ r₂ → G.rf w₂ r₁ → G.rf w₁ r₂ → ¬ G.mo w₁ w₂)

/-- ATOMICITY OF READ-MODIFY-WRITE over every consistent graph: two distinct updates never read the same write.
Feeds: the `atomar` field of `Konsistent`, `liest_mo_max`, `mo_total`. Proof sketch: the two updates are `mo`
ordered; the later one reads a write that the earlier one precedes, contradicting `atomar`. -/
def RmwNichtDoppeltAussage : Prop :=
  ∀ (E Ort Wert : Type) (G : Speicher.Graph E Ort Wert), G.Konsistent →
    ∀ w u₁ u₂ : E, G.rf w u₁ → G.rf w u₂ → G.istRmw u₁ → G.istRmw u₂ → u₁ = u₂

/-- INDEPENDENT READS OF INDEPENDENT WRITES are forbidden when every access is `seq_cst`: two readers cannot
disagree on the order of two independent writes. Feeds: `drf_sc` (an all-`seq_cst` graph is race free, hence
sequentially consistent), `scSchritt`, `Graph.rb`. Proof sketch: the two disagreeing readers close a cycle
`wx rf r1x po r1y rb wy rf r2y po r2x rb wx` of `scSchritt`, which `SCKonsistent` forbids. -/
def IriwScVerbotenAussage : Prop :=
  ∀ (E Ort Wert : Type) (G : Speicher.Graph E Ort Wert), G.Konsistent → (∀ a, G.sc a) →
    ∀ wx wy r1x r1y r2y r2x : E,
      G.rf wx r1x → G.po r1x r1y → G.rb r1y wy → G.rf wy r2y → G.po r2y r2x → G.rb r2x wx → False

/-- THE SAME SHAPE IS ALLOWED BELOW `seq_cst`: some consistent graph has two readers that disagree on the order of
two independent writes (release/acquire does not order independent writes). This is the existential half that
makes `IriwScVerbotenAussage` non-vacuous: the forbidden outcome is forbidden by the strength of the mode, not
because the shape is impossible. Open: the concrete graph (Prover). -/
def IriwRaErlaubtAussage : Prop :=
  ∃ (E Ort Wert : Type) (G : Speicher.Graph E Ort Wert), G.Konsistent ∧
    ∃ wx wy r1x r1y r2y r2x : E,
      G.rf wx r1x ∧ G.po r1x r1y ∧ G.rb r1y wy ∧ G.rf wy r2y ∧ G.po r2y r2x ∧ G.rb r2x wx

end Gabbro.Core.Ziel.Korrektheit
