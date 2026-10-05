# MUSE-REPORT-1325: TSO projection of the locked and direct-memory tags

## What was done

New file `grammatik/Grammatik/X86/HwKapsteinTsoLocked.lean` (~1260 lines)
plus one `import Grammatik.X86.HwKapsteinTsoLocked` line appended to
`grammatik/Grammatik.lean`. No other existing file touched. Every
accepted definition is reused unchanged (lifted, never redefined); no
`sorry`, `admit`, `axiom`, `native_decide`, `unsafe`.

**Classification (task categories (a)/(b)/(c)):**

- lockRmw / LOCK XADD → (b): `kapLockTso_xadd_geerbt` — an admitted
  `hwLockSchritt` XADD step equals the accepted TSO locked event
  `lockSchritt` (`LockedOps`, over `TSOZustand`) on the projection
  `kapTso`, with the word footprint `Fuss tgt` named on both sides,
  old/new words named, `istRmw` set, the own buffer drained
  (`m.puffer c = []` extracted as a separate leg) and foreign buffers
  untouched. Proved by inverting `lockSchrittVoll` (all three refusal
  arms contradict the admitted step). Union lift:
  `kap_union_lockRmw_xadd_tso`.
- lockRmw / MFENCE → (a): `kapLockTso_mfence_still` (only RIP
  advances; union lift `kap_union_lockRmw_mfence_still`).
- lockRmw / CMPXCHG → (c) FINDING: `kapLockTso_cmpxchg_befund` — on a
  failing comparison the coherent step still performs the manual's
  write cycle (needs `write64`, refused on a readable-but-not-writable
  word) while the accepted TSO CAS (`casSchritt_fehlschlag`) stutters
  with the projection unchanged and needs no write; `lockSchritt` has
  no cmpxchg arm at all. So no single accepted TSO locked event
  matches the step.
- lockFetch → inherited off-split (`hwLockFetchSchritt_ohne_split`):
  `kap_lockFetch_xadd_geerbt` (b), `kap_lockFetch_mfence_still` (a),
  union lift `kap_union_lockFetch_xadd_tso`. Split words, parsed #UD
  and absent fetches refuse (accepted pins joined in the witness).
- system, nine legs → (a): `kap_system_hlt/cli/sti/pause/cpuid/rdtsc/
  syscall/sysret/iret_still` via the generic transport
  `kap_system_still_of_mem`, union lift `kap_union_system_still`.
  Every admitted plug step keeps every buffer
  (`kap_system_puffer_bleibt`): SYSCALL/SYSRET/INT perform no drain,
  the plug-level form of S-SYSCALL-KEIN-DRAIN/S-INT-KEIN-DRAIN.
- system / INT n → (c) FINDING, high priority:
  `kap_system_intN_schreibt_direkt` (delivery installs pushed-frame
  memory directly via the accepted `schiebeRahmen` path while every
  buffer is kept) and `kap_system_intN_kein_tso_ereignis` (a delivery
  changing two distinct canonical bytes is no single accepted TSO
  event: issue keeps memory, flush touches exactly its head
  address).

**Witnesses:**

- `kapIretHw` (+ `kapIretReg`, `kapIret_rsp/mem/liest0-4/kanonisch`,
  `kapIretHw_wf`): the witness start with core-0 RSP parked at 16336
  (five readable zero words; the start RSP 20480 points at unreadable
  memory, so no admitted IRET leg exists there).
- `kapLocked_sys_alle_still`: all nine silent legs as reached union
  steps silent on the projection (CLI additionally keeps every
  buffer).
- `kapLocked_zeuge`: LOCK XADD union step with its TSO event and
  footprint (word 10 to 15, own buffer drained, foreign buffers kept),
  MFENCE, fetched XADD, the exhibited core-1 INT delivery (bytes 16344
  and 16369 changed) with its no-single-TSO-event obstruction, the
  failing-comparison twin (word stays 10, RAX takes 10) with the
  write-permission refusal, own-buffer/split/register-#UD/
  freestanding-syscall refusals, well-formedness of all three
  machines, and two-core non-degeneracy (10 to 15 to 22, owner-only
  forwarding 99 vs stale 0).
- CUTS block plus `#print axioms` for every theorem: all depend only
  on subsets of the goal standard (`propext`, `Classical.choice`,
  `Quot.sound`); most on `[propext, Quot.sound]` or less.

## Last build result

`./lean-probe grammatik/Grammatik/X86/HwKapsteinTsoLocked.lean`:
`== 0 error(s)`. `./lean-bau`: `Build completed successfully
(691 jobs)` — whole project green.

## What remains open (see CUTS)

- CMPXCHG success-only correspondence with `casSchritt` (plus the
  flags/RAX effects, which have no TSO-level form).
- A multi-step `TSOErreichbar` characterisation of the INT frame
  push (proved here only as not-one-event).
- The remaining 13 union tags (isa, addr, muldiv, uc, port, fp,
  fehler, tor, vec, nested, int, bild, instanzen) are untouched.
- No W/GX bridge; no source/checker/contract/entry/budget claim; no
  hardware correspondence beyond self-consistency.

## What I believe is wrong in the task

1. The MECHANISM paragraph describes connecting ONE family via a new
   `HwAdapter` with `HwWf` preservation and poison probes. That does
   not match the TASK (capstone projection over the already-composed
   union, reusing `HwKapstein`/`HwKapsteinTso` directly). The file
   follows the TASK: no new adapter, no new event type; `HwWf`
   preservation and refusals ride the accepted lemmas and pins.
2. "The locked RMW as the accepted TSO locked event" holds for XADD
   (and degenerately for MFENCE-as-silence) but not for CMPXCHG: the
   accepted TSO locked vocabulary (`lockSchritt`/`casSchritt`) has no
   single event matching the coherent compare-exchange step (proved
   as a FINDING, not forced into a TSO shape).
3. "Exactly one accepted TSO event" is likewise false for INT n
   delivery (direct multi-byte install, high-priority FINDING) — the
   honest classification the task text itself anticipates for steps
   that write memory off the TSO paths.
