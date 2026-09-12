# MUSE-REPORT-106 (lane 106, D9 second half: the rely from lock exclusivity)

## What was built

New file `grammatik/Grammatik/RelySperre.lean` (registered in
`grammatik/Grammatik.lean`), proving the memory-level rely of
`stabil_aus_bewachung` (StabilBewacht.lean) on the PC machine:

- `rely_aus_sperre` — the exact TARGET statement from the task,
  proved verbatim (same binder order and names).
- `rely_aus_sperre_global` — the global mirror (guard list
  `D.gbraucht`, conclusion `M'.speicher.globs x = M.speicher.globs x`),
  statement designed by this lane since the task only sketched it.

Supporting theorems:

- `sperre_exklusiv` — two threads never hold the same lock at a
  `GenErreichbar` machine, by induction over the reachability
  derivation (`blatt` keeps held sets via `blatt_brav`, `nimmt` fires
  only under `GenFrei`, `gibt` shrinks). Lifts the take-time scheduler
  rule to held-state disjointness.
- `blatt_erhaelt_globs` — global mirror of `blatt_erhaelt_slots`
  (CSLInvariante.lean): a firing leaf of a thread not holding `L`
  keeps the `L`-guarded global. Table writers go through
  `schreibSlot`/`schreibBytes` (never touch `globs`); `assignGlob` /
  `publish` to `x` itself contradict `hfrei` via the constructor guard
  (`hL`) and `HeldGenau`; `axiomCall` goes through the oracle frame
  (`hO`) plus `hgd`.
- Small frame helpers: `lese_globs_gleich`, `storeGlob_fremd_global`,
  `schreibSlot_globs_gleich`, `merke_globs_gleich`,
  `schreibBytes_globs_gleich` (induction over the byte list).

Witnesses (rule 13):

- `rely_aus_sperre_zeuge` on the reference fixture: `witProg` extends
  `refB_prog` with an empty-holdings leaf atom for thread 0;
  `wit_reach` replays lock + writing leaf to `refPC2` (thread 1 holds
  the lock of `konto` — `wit_haelt1`); `wit_step0` fires an
  environment-only `assignVar` (`witStmt0`, `witRho0`) on thread 0.
  Conjunction also carries non-degeneracy: the run moves slot 0
  (`refB_pc_schreibt`) and `einzahlen` writes `konto`
  (`refEin_schreibt`).
- `rely_aus_sperre_global_zeuge` on `gD` (WacheGlobal.lean, which has a
  real global): `gM1`/`gM2` reach lock + global write (`gTake`,
  `gLeaf`, `gReach`) moving the global 0 -> 5 (`gMoved`); `gStep0`
  fires the thread-0 local step; non-degeneracy via `gMoved` and
  `gTabWrite`. New defs: `gSp0`, `gO`, `gO_gut`, `gProg`, `gPr`
  (single-function program with trivial contracts), `gWriteE`,
  `gDarfHeld`, `gWriteSt`, `gPc1`, `gM1`, `gW1w`, `gM1haelt`, `gPc2`,
  `gM2`, `gW1w_glob5`, `gSp0_glob0`, `gHaelt1`, `gStmt0`, `gRho0`,
  `gW0'`, `gM3`. Reuses `gGuardInst`, `gTabWrite` from WacheGlobal.

## Exclusivity question (asked in the task)

No lemma "two threads never hold the same lock" existed. What exists
is run-level only: `ForeignExclusion` (Wettlauf.lean:760 — who takes a
lock takes it while nobody else holds it *at that run position*) with
`gen_ausschluss` (Maschine.lean:1088) and `pc_ausschluss` (:1440).
The state-level held-set disjointness is new here as
`sperre_exklusiv`.

## Last build result

`./lean-bau` ends with `Build completed successfully (57 jobs).`
(`✔ [56/57] Built Grammatik`.) `./lean-probe` on the new file: 0
errors; every `#print axioms` in the file reports only
`[propext, Classical.choice, Quot.sound]`.

## Guardian state

- `pruefe-kennungen.py`: ALL PASS.
- `pruefe-englisch.py`: exit 1, but every finding is a pre-existing
  ratchet count in Rust checker/instrument files (7905 vs 7881 German
  comment lines etc.); no finding mentions `grammatik/` or this lane.
- `pruefe-todo.py` / `pruefe-praemisse.py`: cannot run here — they
  shell out to `cargo`, which does not exist on this machine.

## What remains open / notes

- The witnesses use hand-built thread programs, not
  `Extraktion.progAus`: the rely holds for every `PCProg`, so no
  extraction adequacy is owed (booked in CUTS).
- Task suggestion "a `leave` or a read" for the thread-0 step: `leave`
  needs `l = true` and `ret` needs `Λ.Perm V.ende`; the workable
  memory-free leaf at empty holdings was `assignVar` (environment
  only, no events, no memory change). Same proof shape, no weakening.
- Nothing in the task statement itself appears wrong; the TARGET was
  taken over unchanged.
