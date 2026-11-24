/-
  File:      core/Core/Ziel/Korrektheit/Beweise/Kohaerenz.lean
  Subject:   THE FOUR COHERENCE AXIOMS of the pinned catalogue statement, proved over every consistent graph.

  All four conjuncts are consequences of the one coherence rule `Konsistent.kohaerent` (`hb ; eco?` is
  irreflexive) together with well-formedness (`mo` is a strict total order per location, `rf` a source of a
  read):
  * CoWW is `Graph.hb_mo`, which already puts the earlier write before the later one in `mo`;
  * CoWR is `Graph.liest_mo_max`, which says the source of a read is newest among the writes `hb`-before it;
  * CoRW composes `G.mo w w'` and `G.rf w' r` into `G.eco w r` and closes the cycle with `G.hb r w`;
  * CoRR is the existing `Graph.corr_verboten`.
  No fixture is involved: the theorem quantifies over all event types and all consistent graphs.
-/
module

public import Core.Ziel.Korrektheit.Speicher
public import Core.Speicher.Kohaerenz
public import Core.Speicher.Litmus

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core

/-- THE FOUR COHERENCE AXIOMS (CoWW, CoWR, CoRW, CoRR) hold over every consistent graph, as pinned by
    `KohaerenzKatalogAussage`. Feeds: `Konsistent.kohaerent`, `Konsistent.wf.mo_trans`,
    `Konsistent.wf.mo_irrefl`, `Graph.hb_von_po`, `Graph.eco_von_mo`, `Graph.eco_von_rf`, `Graph.hb_mo`,
    `Graph.liest_mo_max` and `Graph.corr_verboten`. Proof sketch: for CoWW, `hb_mo` gives the forward `mo`
    edge, so the backward edge would close a loop; for CoWR, `liest_mo_max` gives the forward edge unless the
    read's source is the earlier write itself, which the distinctness premise excludes; for CoRW, `mo ; rf`
    is an `eco` path back into the `hb`-earlier write, contradicting `kohaerent`; for CoRR, apply
    `corr_verboten` directly. -/
theorem kohaerenz_katalog : KohaerenzKatalogAussage := by
  intro E Ort Wert G hk
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w₁ w₂ hpo hs₁ hs₂ ho hmo
    have hvor : G.mo w₁ w₂ := Speicher.Graph.hb_mo hk hs₁ hs₂ ho (G.hb_von_po hpo)
    exact hk.wf.mo_irrefl w₁ (hk.wf.mo_trans w₁ w₂ w₁ hvor hmo)
  · intro w w' r hpo hrf hs ho hne hmo
    have hneu : w = w' ∨ G.mo w w' :=
      Speicher.Graph.liest_mo_max hk hrf hs ho (G.hb_von_po hpo)
    have hvor : G.mo w w' := hneu.resolve_left hne
    exact hk.wf.mo_irrefl w' (hk.wf.mo_trans w' w w' hmo hvor)
  · intro r w w' hpo hrf hs ho hne hmo
    exact hk.kohaerent r w (G.hb_von_po hpo)
      (Relation.TransGen.trans (G.eco_von_mo hmo) (G.eco_von_rf hrf))
  · intro r₁ r₂ w₁ w₂ hpo hrf₁ hrf₂ hmo
    exact Speicher.Graph.corr_verboten hk hpo hrf₁ hrf₂ hmo

end Gabbro.Core.Ziel.Korrektheit
