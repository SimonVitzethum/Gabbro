/-
  File:      Grammatik/ZielOrt.lean
  Subject:   THE GOAL OVER THE CONCURRENT CALL MACHINE G -- the premise
             classes, the lock facts on the REPAIRED G, and the re-check
             of the earlier finding.

  The goal: a user proves only their own logic (one Hoare triple per
  function, `KoerperGut`) plus named hardware assumptions (`GutO`); memory
  safety, data-race freedom and "contracts hold at their place in concurrent
  runs" (`VertragAmOrtG`) are carried by the language, with every further
  premise a decidable fact the checker computes (`programmImFragment`,
  `fussOrtB`) or a fact about the start configuration (`StartGut`,
  `StartExklusiv`).

  History. This file first REFUTED the goal over G (2026-09-13): the bare
  `gibt` step of G released a lock while a frame of the thread still named
  it, and a reachable machine violated `ensures lies`. G has since been
  repaired (`RufMaschineG.lean`: no bare `nimmt`/`gibt`, start threads hold
  their signature locks, `HeldGenau` on every step that reads or writes),
  and `rufG_haelt_statisch` (`RufHaeltG.lean`) makes "static holdings ⊆
  held locks" an invariant of every run.

  What this file proves.

  1. The conclusion `VertragAmOrtG` (§1), the user obligation `KoerperGut`
     (§2: the body triple requires -> ensures over the sequential semantics
     with ANY contract-respecting handler, plus the caller duty: every call
     the body makes meets the callee's `requires`), and the decidable
     program facts (§3) with their soundness (`fussOrtB_ok`,
     `schreiberHaeltB_ok`). The footprint `fussOrte` of a function now
     includes the contract carriers of the functions it calls directly: a
     caller reasons with its callees' contracts, so those carriers must be
     protected for the caller's whole frame too.
  2. The lock facts on the repaired G (§4): a step releases only a lock the
     head names (`offen_schrittG`), lock exclusivity from an exclusive start
     (`exklusivG`), and the one-step rely (`schritt_traeger`, `relyG`): a
     step of a thread leaves a carrier alone if it does not hold one of the
     carrier's guards or its head function may not write the carrier.
  3. The re-check of the finding (§5): the pivot of the old run (a frame of
     `lies` naming the lock while its thread does not hold it) is
     unreachable (`ziel_ort_gegenbeispiel_verschwindet`); and the start fact
     is needed: with every thread starting in `einzahlen` (holding the lock
     by signature) the start machine is not exclusive and a reachable
     machine of the repaired G still violates `ensures lies` (`geg_lauf`,
     `ziel_ort_gegenbeispiel`, `ziel_ort_form_falsch`).
  4. The conclusion is not vacuous (§6, `vertragAmOrtG_refP_zeuge`).

  The theorem `ziel_ort` itself is in `ZielOrtBeweis.lean`.
-/

import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrt.T1
import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrt.T2
import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrt.T3
