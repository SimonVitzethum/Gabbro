/-
  File:      Grammatik/Maschine.lean
  Subject:   **THE MACHINE** -- threads STARTED over the grammar, interleaved by the
             scheduler; every reachable run yields its worlds and its order from that
             construction, never from a separately asserted link.

  ## The model

  A thread is a STARTED body: its full event trace is what one `exec` run yields from
  the empty trace (`MaschinenFaden`, closed per body by `exec_spur` -- the per-thread
  `Brav` provenance). A machine run (`MaschinenLauf`) is the scheduler's interleaving  of started threads over the grammar:

    * `hvoll` -- every thread started (per-thread `Brav` from the empty trace),
    * `hvers` -- the run interleaves the full traces (`IstVerschraenkung`: every
      observed per-thread trace is a tail of its full trace),
    * `hausschluss` -- (W3) the scheduler rule: who takes a lock takes it while no
      other thread holds it (`ForeignExclusion`, the foreign-lock promise),
    * `hEin` -- (W4) the construction: single-threadedness over the projected run
      (`Marken.Einfaedig`, the Verlauf side),
    * `hungeteilt` -- (W5) the declaration side: an unshared carrier belongs to one
      thread.

  A `MaschinenLauf` IS a reachable run: started threads plus scheduler interleaving.
  `maschinenLeer` is the reachable base (threads started, zero steps taken).

  ## The theorems

    `maschinenWelten`     -- event-to-world: the worlds a real run produces, by
                             folding the run's own events onto the start world
    `w1w2w4_aus_maschine` -- W1/W2/W4 for every reachable run (W1+W2 from the
                             grammar side via `lauf_aus_brav`; W4 from the
                             construction via `marke_eindeutig_aus_einfaedig`)
    `reduktion_maschine`  -- REAL reduction, Lipton sense, order fragment: two
                             conflicting sections of a machine run admit a serial
                             order, via `reduktion_seriell` with `Gesittet`
                             derived from the machine itself
                             (`gesittet_aus_maschine`). The witnesses are run
                             positions; no chain object and no `SerialLink`-style
                             premise appear anywhere.

  Port note: adapted from the WIP `Maschine.lean` at `85cb4f4` (branch
  `wip/maschine-pflicht-2026-09-11`, read-only, stale base, NOT merged) onto the
  current core -- 5-field `Gesittet` with `ungeteilt`, 3-tuple `Brav`, `geteilt`
  still declared. The portable WIP sections (thread shapes, scheduler, start) are
  rebuilt here as data; the W1/W2/W4 derivations go through the current bridge
  (`lauf_aus_brav`, `bruecke_exec_gesittet`) instead of the WIP's reshaped core.
  Read-only inputs: `PORT-MASCHINE.md` (lane-110 audit), `PORT-MIGRATION.md`
  (lane-112), `PORT-SYNTAX.md` (lane-111), `PORT-PFLICHT.md` (lane-113).
  Sibling theorems used read-only, never modified: `reduktion_seriell`,
  `mover_nonwriter_past`, `wache_aus_schuld` (`InterferenzAllgemein.lean`
  sections 21-22).

  Mechanism (k02 `Schrittrelation`, §§6-11): the step relation over shared
  memory (`GenSchritt`: one leaf statement through `execStmt`, `locks L` as
  scheduler rule), inductive reachability from start worlds (`GenErreichbar`),
  and the world history with live memory (`GenMaschine.welten`). A write step
  moves memory by construction (`schreibt_wirkt_*`, `gen_write_glob_moves`);
  the old fold's constant-memory shape is kept below as the NEGATIVE example
  (`maschinenWelten_speicher_gleich`). Reachable runs yield W1/W2 plus the
  scheduler rule (`gen_konsistent`, `gen_gut_obs`, `gen_ausschluss`); W4/W5
  stay explicit construction/declaration premises (`gen_w1w2w4`,
  `gen_gesittet`, `gen_reduktion`), exactly as the bridge books them.

  Compatibility: §§1-5 below are the premise-structure (`MaschinenLauf`),
  kept byte-identical for the consumer (`Ziel.lean` §9 uses every field and
  theorem). It is DEPRECATED in favour of §§6-11: new work builds generated
  runs; the structure stays only so nothing breaks.

  Remainder (booked, not hidden): §12 threads program counters through the
  generated machine -- positions with footprints, the `Einfaedig` projection
  premise discharged from program text (`pc_discharge_einfaedig`) and the
  declaration side likewise (`pc_discharge_unshared`). What stays open: full
  `Block` continuations (`ite` arms, call stacks, loop resumption as explicit
  continuation objects) and the run-to-`Bau` wiring for `Geteilt.lean`.
-/

import Grammatik.Kern.Semantik.Maschine.T1
import Grammatik.Kern.Semantik.Maschine.T2
import Grammatik.Kern.Semantik.Maschine.T3
import Grammatik.Kern.Semantik.Maschine.T4
import Grammatik.Kern.Semantik.Maschine.T5
import Grammatik.Kern.Semantik.Maschine.T6
import Grammatik.Kern.Semantik.Maschine.T7
import Grammatik.Kern.Semantik.Maschine.T8
import Grammatik.Kern.Semantik.Maschine.T9
