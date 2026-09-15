# Opus agent report: closing theorem stage (b) (2026-09-15)

*Final report of the Opus agent, handed over from the laptop session for the merge on the
server. Branch base: master 282a45f1. Full `lake build` on fisch (`~/gabbro-opus-nb/`): green,
233 jobs, no `sorryAx`.*

Stage (b) is closed for `beispiele/124`: every SC-interleaved run of its emitted C is simulated
in machine G, and the C's race freedom is proved from G's rather than assumed.

**Which program.** Of the corpus programs with more than one thread (07, 59, 108, 109, 124,
125), only 108 exports through `gabbro lean-g`, and 108 takes no lock. 124 had only the hand
model `mP`, whose `pruefeA` returns nothing and reads nothing, while the emitted C reads `privA`
there. So a new G model `kP` was written from the source's bodies; every premise group of the
goal theorem is proved on it, and `k124_ziel` is `gabbro_ziel` applied.

**Finding about the corpus file:** 124's `setze` promises only `konto[0] == x`; with that
contract the release check in `hauptA`'s locked section fails, so premise (b) does NOT hold for
the source as written. `kP` keeps `mP`'s stronger contract; the `.gab` file is unchanged.

**Statement.** `schlusssatz_124 passes LP K0 hLZ Echt hDRF`: there is a runtime root assignment
`w` such that (1) `K0` is the runtime's start for `w` and premise (d) holds for the matching G
start; (2) the emitted C is data-race free under the real lock primitive (proved); (3) every SC
configuration of the C is related to a reachable G machine where `Ziel` holds (memory, lock
holders, every thread); (4) every real observation is the observation of such a configuration.
In C memory (`schlusssatz_124_c`): whenever the lock is free, `konto[0] == konto[1]`; once
`hauptA`'s thread has returned, `privA[0] == 7`.

**Premises (hypotheses, none an `axiom`):** `DRFSC` -- if the C is race free, every real
observation is that of an SC interleaving of synchronisation-free blocks; its hypothesis is
proved from G (`rennfreiC_aus_sim`). `LaufzeitC` -- threads start only at declared roots,
`L_nimm`/`L_gib` behave as `sperrAbstrakt`, which reveals only held/free
(`sperrAbstrakt_nur_eigen`); the same list as NICHTINTERFERENZ §10.

**Simulation choice.** One C step = one synchronisation-free statement as a block (existing
big-step semantics), mapped to a contiguous segment of G steps by the same thread: a forward
simulation, no reordering argument. Finer interleavings are covered by the region-
serialisability part of DRF-SC, which is not proved.

**Axioms:** propext, Classical.choice, Quot.sound only. No `sorry`, no `native_decide`.

**Witnesses:** `schlusssatz_124_zeuge` (20-step run, thread 1 blocked at `L_nimm();` while
thread 0 holds the lock, hand-over, both return; invariant and `privA[0] == 7` at the end; its
DRF-SC instance is trivial -- it shows joint satisfiability only). `rennfreiC_zeuge_124`: the
critical sections (steps 10 and 15) conflict on `konto`, ordered by release 12 / acquire 13.

**Still open (PLAN §7.6):** (1) region serialisability inside DRF-SC (needs one step per memory
access); (2) general footprint soundness (access-instrumented `Exec`; key lemma `ev_zform_blk`
proved); (3) the ticket lock behaves as `sperrAbstrakt`; (4) a checker producing the
simulation certificate (`sim124` is by hand); (5) exporter support and parse fidelity for 124;
(6) the emitted C is hand-transcribed (no C parser); (7) lock calls only at the top level of a
root function, atomics neither exempt nor ordering, no volatile/foreign calls in blocks.
Chain count stays 1 (124 fails the parse, export and printed-certificate columns).

Files: `grammatik/Grammatik/CNebenlaeufig.lean`, `Korpus124.lean`, `Schlusssatz124.lean`;
PLAN-UEBERSETZUNGSVALIDIERUNG §7, SATZKARTE §26, NICHTINTERFERENZ §10 addendum.
