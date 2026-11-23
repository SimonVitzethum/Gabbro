/-
  File:      Grammatik/Speichermodell/RC11.lean
  Subject:   The axiomatic memory model W (PERFECT-MODEL §3.4/§3.5, step S5): RC11 without fences,
             with `po ∪ rf` acyclic, truly sequentially consistent `seq_cst` and the DRF-SC theorem.
-/
module

public import Grammatik.Speichermodell.RC11.Basis
public import Grammatik.Speichermodell.RC11.Relationen
public import Grammatik.Speichermodell.RC11.Konsistent
public import Grammatik.Speichermodell.RC11.DRFSC
public import Grammatik.Speichermodell.RC11.SCOrdnung
public import Grammatik.Speichermodell.RC11.Litmus
public import Grammatik.Speichermodell.RC11.Praefix
public import Grammatik.Speichermodell.RC11.Trennung
public import Grammatik.Speichermodell.RC11.Erfuellbar
