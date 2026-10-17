/-
  File:      Grammatik/ZielOrtBeweis.lean
  Subject:   `ziel_ort` -- contracts hold at their place on every machine of
             the repaired concurrent call machine G, from the user's
             sequential obligations, the hardware assumption and decidable
             program facts.

  The proof is a REPLAY. Every frame of every thread carries a sequential
  run of its function's body, started at the frame's entry world:

  * the sequential world `σ` of the head frame agrees with the machine
    world on the frame's footprint (`GleichAuf (fussOrte P f) σ W`): the
    frame's own steps are sequential steps at `σ` (leaf locality, the
    residue step lemmas of `ZielOrtSem.lean`), and steps of OTHER threads
    never touch the footprint (the rely: every footprint carrier is guarded
    by a signature lock the frame holds for its whole life
    (`rufG_haelt_signatur`), exclusive across threads (`exklusivG`), or
    written by no function);
  * the calls the frame made are RECORDED with the machine's answers
    (`Eintrag`), each answer at a fresh trace position of the sequential
    world, so the record is a function of the call key and defines a
    contract-respecting handler (`rufAus`); the sequential run of the body
    with ANY handler that repeats the record reaches the frame's current
    residue (`KopfOk`), a suspended frame the pending call (`WarteOk`);
  * at a return, `KoerperGut` (the body triple) gives `ensures` in the
    sequential world, hence in the machine's (agreement on the footprint,
    which contains the `ensures` carriers); at a call, `KoerperGut`'s gated
    conjunct (no failed `requires`) gives the callee's `requires` in the
    sequential world, hence in the machine's (the callee's contract carriers
    are in the caller's footprint).
-/

import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis.T1
import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis.T2
import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis.T3
