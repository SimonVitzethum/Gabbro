/-
  File:      core/Core/Speicher.lean
  Subject:   The memory model (PERFECT-MODEL §3.4/§3.5, step M3): RC11 without fences, `po ∪ rf`
             acyclic, truly SC `seq_cst`, DRF-SC, the operational graph machine (sound and complete),
             embeddings, coherence consequences and the sink lemma.
-/
module

public import Core.Speicher.Basis
public import Core.Speicher.Relationen
public import Core.Speicher.Konsistent
public import Core.Speicher.DRFSC
public import Core.Speicher.SCOrdnung
public import Core.Speicher.Litmus.Grund
public import Core.Speicher.Praefix
public import Core.Speicher.Trennung
public import Core.Speicher.Litmus.Sb
public import Core.Speicher.Litmus.Rmw
public import Core.Speicher.Litmus.Rs
public import Core.Speicher.Litmus.Katalog
public import Core.Speicher.Erfuellbar
public import Core.Speicher.Einbettung
public import Core.Speicher.Graphmaschine
public import Core.Speicher.GraphmaschineVollstaendig
public import Core.Speicher.GraphmaschineErfuellbar
public import Core.Speicher.Kohaerenz
public import Core.Speicher.Senke
public import Core.Speicher.MoLetzte
public import Core.Speicher.Anhaengen
public import Core.Speicher.Viele
