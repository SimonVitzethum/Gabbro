/-
  File:      Grammatik/ZielOrtSem.lean
  Subject:   THE SEQUENTIAL SIDE OF `ziel_ort` -- agreement on a footprint,
             locality of the sequential semantics, and the frame semantics
             `semZ` that keeps the logic outcome (for the caller duty).

  `ziel_ort` (`ZielOrtBeweis.lean`) replays each frame of the concurrent
  machine G by the SEQUENTIAL semantics of its body, started at the frame's
  entry world. Between the frame's own steps other threads move memory,
  but only OUTSIDE the frame's footprint (the rely, `ZielOrt.lean`); so the
  sequential world and the machine world AGREE ON THE FOOTPRINT
  (`GleichAuf`), not everywhere. This file provides:

  1. `GleichAuf S σ W`: agreement of two worlds on the carriers `S`, and
     the locality of expressions (`eval`, `evalArgs`, `evalErg` depend on
     their carriers only), of writes (a write of the same value at the
     same place keeps agreement) and of every leaf the fragment admits
     (`blatt_lokal`).
  2. `semZ`: the frame semantics of a residue, like `semK`
     (`RufUmkehrRufG.lean`) but keeping the logic outcome `logik e`, which
     the caller duty of `KoerperGut` (no failed `requires` at a call) is
     about; `ZErg.gleich` (equality up to the trace); and the residue step
     lemmas for every rule of the fragment.
  3. `GRest.okZ`: the residues `ziel_ort` follows (in the fragment `kOk`,
     reading only inside a given footprint).
-/
module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtSem.Teil1
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtSem.Teil2
