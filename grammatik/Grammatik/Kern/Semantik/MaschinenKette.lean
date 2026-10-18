/-
  File:      Grammatik/MaschinenKette.lean
  Subject:   **THE CHAIN FROM THE WHOLE RUN** -- iterating the one-step chain
             construction over entire lock-only PC runs.

  `kette_aus_maschinenlauf_schritt` (in `Maschine.lean`, read-only here) extends a
  tracking chain along ONE memory-preserving machine step of a member thread,
  but its conclusion drops the facts the NEXT iteration needs: the member
  thread (`f ∈ J.faeden`) and the code the link guard reads (`J.code`). An
  opaque `J'` cannot recover them, so pure reuse cannot iterate. The adapted
  step below (`kette_aus_lauf_schritt`) rebuilds the SAME construction with the
  SAME read-only inputs, threading exactly those two facts plus the guarded
  link through; the delta is marked at each changed line.

  Covered class (exactly): single-thread lock-only `PCReach` runs with
  non-writing code and a fitting entry --

    * lock-only (`hlock`): no `PCAtom.leaf` atom anywhere in `prog`, so every
      `PCSchritt` of the run is a `take` / `rel` step and the memory-preservation
      premises (`hslots` / `hglobs`) close by `rfl`;
    * single-thread (`hsingle_prog`, `hsingle_run`): every other thread has an
      empty program (counter routing: a step by `g ≠ f` would need an atom from
      `prog g = []`), and the final run mentions only `f`, so each prefix does;
    * non-writing code (`hnw_code`): `code f` writes no table carrier, so the
      guarded `SerialLink` of one level discharges to the unconditional link
      the next step consumes;
    * fitting entry (`hEintritt`, `hSchuld`, `hInvSicht`): the seed chain over
      the start machine carries `f` as its member thread.

  Read-only inputs, never modified: `pcSchritt_gen` / `pcReach_gen` (counter
  routing: `PCReach` derivations project to `GenErreichbar`), `GenStart`,
  `Speicher.welt`, `genEigen`, `gen_konsistent`, `gen_gut_obs`,
  `gen_ausschluss`, `genWelten_letzte`, `gen_eigen_getElem`, `Gesittet`,
  `BeschraenkteVerschraenkung`, `konsistent_nil`.

  Remainder (booked, not hidden): `blatt` steps -- a writing leaf moves memory,
  so `hslots` / `hglobs` need the `execStmt` frame correspondence; multi-thread
  runs -- discharging `hsingle` needs the `Einfaedig` projection
  (`pc_discharge_einfaedig`) plus the declaration side (`pc_discharge_unshared`),
  as `gen_gesittet` books them; non-vacuous `SerialLink` witnesses at `zugriff`
  events for writing steps; globals and multi-carrier conflicts (as before).
-/


import Grammatik.Kern.Semantik.MaschinenKette.T1
import Grammatik.Kern.Semantik.MaschinenKette.T2
import Grammatik.Kern.Semantik.MaschinenKette.T3
import Grammatik.Kern.Semantik.MaschinenKette.T4
import Grammatik.Kern.Semantik.MaschinenKette.T5
