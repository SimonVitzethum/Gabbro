# MUSE-REPORT-1207 — Generic drain-equals-write64 induction

Lane 1207, clone `/home/simon/Dokumente/gabbro-muse/a1207`, branch `muse/1207`
(base `4ed3590d`; verified at start). Follow-up of lane 1185
(`HwForwardingGeneric.lean`).

## Status: PROVED (probe-green), NOT bau-green — apparatus blocker

**UPDATE (after review 1208, same tree `b903e3cf`, no Lean change): `./lean-bau`
is now GREEN — `Build completed successfully (627 jobs).` The box-pressure
blocker has lifted; the deliverable below is fully verified (probe + full
build). The 1208 verdict REPAIR is dispatch-side (the pinned diff was
unreachable inside the reviewer clone) and raises no finding against this
deliverable, so nothing in the owned files was changed or weakened.

The deliverable is complete in `grammatik/Grammatik/X86/HwDrainGeneric.lean`
(~1020 lines) plus the one import line in `grammatik/Grammatik.lean`
(committed). `./lean-probe` reports **0 errors 5 times** (skeleton, each
addition, final file twice), with all `#print axioms` inside the standard
goal set (`propext`, `Classical.choice`, `Quot.sound`). `./lean-bau` fails
**3 times identically** at this module with a resource abort, not a proof
error (details below). Per rule 11 I commit the probe-green partial and
record the blocker precisely.

## What was done

Generic drain-equals-`write64` induction over the accepted TSO model,
reusing accepted definitions unchanged (never copied, never redefined):
`DrainSpur`/`WortGruppe`/`FremdFrei`/`wortEintraege`/`flushKern`/`issueByte`
(`WordAccessGrouping`, `TSO`), `hwWortAusgabe`/`HwSchritt`/`HwWf`/`setTso`
(`HardwareExecution`), `stapelLadeWort`/`issueListe_stern`-family
(`HwStackCalls`), `fwd_wortByte_bytesWort3` (`HwForwardingGeneric`),
`write64`/`writeBytes`/`read64` (`Speicher`), and the accepted eight-drain
witness `grpS2..grpS10` (`WordAccessGrouping`).

Exact new names (definitions):

- `DrainEreignis` (events `speichere`, `eigenSpuele`, `fremdSpuele`,
  `fremdAusgabe`, `beobachte`), `drainAdapter : HwAdapter DrainEreignis`
- Witness state: `drainWitBytes/Daten/Code/Mem/Reg0/Reg1/Kern/M0/Adr/Wort/Null`,
  `drainWitM1`, `drainWitPush/BufLen/MemStill/LoadEigen/LoadFremd`,
  `drainWitEigen/EigenLen`, `drainWitD1..D8`, `drainWitNachFlush/NachRead`,
  `drainWitFremdNachFlush`
- Negative: `ovFremd`, `ovS0`, `ovS1`
- Refusal fixtures: `drainWitGuardMem/GuardM0`, `drainWitDarkMem`

Exact new theorems:

- Adapter: `drainAdapter_wf`, `drainSpeichere_puffer`,
  `drainSpeichere_kein_speicher`, `drainEigen_ist_flush`,
  `drainEigen_ist_schritt`, `drainBeobachte_still`
- Refusals: `drainEigen_leer_verweigert`, `drainSpeichere_wache`,
  `drainBeobachte_dunkel`
- Prefixes: `drainZwischen_praefix` (installed half over
  `drain_installiert_aux`), `drainUninstalliert_bleibt_aux` (new
  `DrainSpur` induction: not-yet-drained bytes still read start memory),
  `drainZwischen_voll` (joined: buffer suffix + installed + uninstalled)
- Induction: `drainFuss_gleich_schreibbytes` (drained footprint bytes
  equal `writeBytes` bytes), `drainGleichWrite64` (agreement with the
  successful `write64` on the footprint plus `read64` read-back over the
  accepted `wort_gruppe_liest_zurueck`)
- Negative: `ov_flush`, `ov_kein_fremdfrei`, `ov_byte_bricht`,
  `ov_read_bricht`
- Fires on the accepted drain: `drainGrp_hwr`, `drainGrp_fuss`,
  `drainGrp_write64`, `drainGrp_mitte`
- Witness facts: `drainWit_wf/puffer8/mem_still/weiterleitung/fremd_alt/
  eigen_sieben/spuelung_aendert_speicher/fremd_neu/anfang_null/pufferform/
  fremdfrei/gruppe/lesbar_all`,
  `drainWit_guard_dicht/guard_speichere_verweigert/dark_dicht/
  dark_beob_verweigert/eigen_leer_verweigert`
- Joint: `drainGeneric_zeuge` (two cores, group guard, owner-only
  forwarding of 42, adapter drain 8→7, full drain 0→42 observed from both
  cores, generic footprint/`write64` fires with mid-trace prefix, guard /
  dark / empty-drain refusals, overlapping-flush break)

Cleanliness: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`, no
`intro _` / `have _ :=` (two `rg` hits for "admit" are the English word
"admits" in comments), every premise of every theorem is used, CUTS block
plus `#print axioms` per main theorem at end of file. No theorem quantifies
over program syntax, so rule 13's syntax clause does not trigger; the joint
`_zeuge` is provided per the task MECHANISM (4) anyway, and it is
non-degenerate (two cores, 8-entry buffer, memory-changing run 0→42).

## Last `./lean-bau` result

Superseded: a fourth run on the unchanged tree passes:

```text
✔ [626/627] Built Grammatik (2.0s)
Build completed successfully (627 jobs).
```

The three earlier identical failures (below) were box thread pressure, now
dipped. Failing tail, for the record:

Tail of output (module 625/627, others cached/built):

```text
✖ [625/627] Building Grammatik.X86.HwDrainGeneric (7.8s–13s)
info: stderr:
libc++abi: terminating due to uncaught exception of type lean::exception:
  failed to create thread
error: Lean exited with code 134
```

The failing command is the per-file `lean -j2 -M4096 ... HwDrainGeneric.lean
-o ...olean -i ...ilean -c .../ir/HwDrainGeneric.c`. This is the apparatus
signature AGENTS.md §9 documents (`failed to create thread` even on
unchanged source; thread/VM pressure under concurrent lanes). Evidence it is
not a proof error: the same file elaborates completely under `./lean-probe`
(0 errors, full axioms dump) 5 times; nothing in the file spawns threads;
no import cycle (probe resolves imports); `Grammatik.lean` edit is one
appended import line. I did not touch locks/, RAM info, or other lanes
(a `free`/locks inspection call was permission-rejected; I did not work
around it).

## What remains open

1. Merge + publication are coordinator business (§5/§11), not this lane's.
   The candidate builds green here; the 1208 re-review needs the pinned
   diff fetchable inside the reviewer clone (dispatch-side repair, explicitly
   not author-side — no change was required or made here).

## Task critique (rule 4/12 honesty)

1. The task sentence "yields canonical memory equal to `write64`" is
   stronger than what holds: foreign flushes satisfying `FremdFrei` are real
   steps that change disjoint bytes, so only footprint equality holds (plus
   separately guarded footprints via the accepted `wort_gruppe_rahmen`).
   I proved the correct scoped version (`drainFuss_gleich_schreibbytes`,
   `drainGleichWrite64`) and documented the scope in CUTS — not a weakening,
   the global reading is false.
2. The task names no `ZEUGE:` target and no fixed target statement, so rule
   12 does not bind; all statement choices are mine, premises are all used.
3. SILICON: no SDM extracts were consulted in this lane (a first CUTS draft
   wrongly implied they were; corrected before this report). Ordering facts
   come only from accepted modules. No hardware correspondence is claimed
   beyond self-consistency; no W/GX bridge is claimed.

Commits on `muse/1207` (all with `Co-Authored-By: muse-agent-1207`):
`72b0f371` skeleton+import, `85c4efb3` adapter duties, `6a2ea52e`
induction, `31651ad5` witness/fires/zeuge, plus the pending CUTS-honesty
fix and this report.
