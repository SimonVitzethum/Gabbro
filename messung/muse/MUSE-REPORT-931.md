# Muse Report 931 — Exact review of author 781 (SFENCE store narrowness)

Lane 931, clone `/home/simon/Dokumente/gabbro-muse/a931`, branch `muse/931`.
Report-only exact review. Own file: this report. No source touched.

## Machine-readable verdict

CANDIDATE: 781 2de9b8b54e380bfafa5b0a2977d1b57c6215709c
VERDICT: ACCEPT

The acceptance above is bounded: the store-narrowness connection as cut;
WC/NT paths, serializing partners, interrupts/devices/timing/fairness and
any W/GX transfer stay OPEN exactly as the file's `CUTS` states.
Pinned base `56537272a31df3de5d9b7898bbade91c3de817b8` (= this clone's
HEAD); files `MUSE-REPORT-781.md`, `grammatik/Grammatik.lean` (+1 import
line), new `grammatik/Grammatik/X86/SfenceStoreNarrow.lean`, 664 lines;
tree clean per `SNAPSHOT.json`. The snapshot file and the `PATCH.diff`
new-file body agree, including the `CUTS` block and all 31 `#print axioms`
lines.

## What was independently checked

Byte forms against the local manual snapshot
(`.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt` in this clone):
SFENCE entry lines 94415–94451 confirm opcode `NP 0F AE F8`, Op/En ZO,
"ordered with respect to memory stores, other SFENCE instructions, MFENCE
instructions, and any serializing instructions", "not ordered with respect
to memory loads or the LFENCE instruction", r/m field ignored
("any opcode of the form 0F AE Fx, where x is in 8-F"), Operation
`Wait_On_Following_Stores_Until(...)`, #UD iff CPUID.01H:EDX.SSE[25] = 0
or LOCK prefix. Vol. 1 §10.4.6.4 lines 15087–15092 confirm the store-only
fence. The codec check `248 ≤ byteNat m` captures exactly F8..FF; every
accepted third byte (≥ 0xC0) has mod=3/reg=7, so no memory form can slip
in. LOCK is `0xF0` = 240, parsed to `.ud .lockAufZaun` with length 4 on
the disjoint reg=7 field. Neighbour refusals are pinned by `decide`:
MFENCE row F0, LFENCE row E8, CLFLUSH memory shape 0x38, LOCK+MFENCE,
truncations, wrong escape byte, and `decodeExt` refusing the SFENCE bytes
(no shadowing either direction; the combined decoder tries accepted
`decodeExt` first by construction).

Semantics: fence-only step over reused `LockMaschine` with named silicon
premise `sse : Bool` (assumed, never probed — no invented determinism).
Success advances only RIP (`sfence_erfolg`, register/flags/load frames
proved; the manual lists no register or flag effect for the ZO form).
`toTSO` is `⟨m.zu.speicher, m.puffer⟩`
(`LockedInstructionExecution.lean:311`), i.e. RIP-insensitive, so
`sfence_behaelt_tso` (TSO-observably the identity over an empty own
buffer) is sound. A pending own buffer refuses (`sfence_puffer_verweigert`)
instead of silently passing: the exact admitted elimination premise the
owner task asked for, in the conservative (sound) direction. The gate
narrowness vs MFENCE is proved twice: abstractly
(`sfence_schmaler_als_mfence_gate`: SSE present, SSE2 absent — SFENCE
succeeds where reused `lockSchrittVoll_mfence_ohne_sse2` raises
`.sse2Fehlt`; call signature verified against the accepted definition)
and on fetched bytes (`sfZeug_mfence_ohne_sse2_ud` on `zeugZaun`).

Interfaces: every reused name was verified to exist in this clone at the
used shape — `lockSchrittVoll_mfence_ohne_sse2`, `lockVoll_mfence_adapter`,
`lockSchritt`, `lockByteschritt`, `lockArt`, `lockZeug`, `lockCodeExec`,
`lockDataRW`, `einEintrag`, `hwOhneSse2`, `zeugZaun`, `basisBereit`,
`merkmalZugelassen`/`.sseDoppel`, `drainVoll`, `drainKernN`, `flushKern`,
`drain_voll_leer`, `zaunBereit`/`zaunBereit_iff_leer`, `TSOErreichbar`
(`.start`/`.schritt`/`.issue`/`.flush`), `issueByte`, `fdStart`, `fdS2`,
`fdS3`, `fdX`, `fd_schritt1/2`, `fd_voll_schritt`, `fd_speicher_aendert`,
`fd_fremd_wartend`, `geholt`, `ausfuehrbarN`, `laengeOk`, `ripNach`,
`loadByte`, `witnessFlags`.

Rules: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` (the only
`admit` substrings are English "admitted"); no `intro _` / `have _ :=`;
no `Prop`-typed premises; every premise of every new theorem is used in
its proof (checked theorem by theorem, including the TARGET
`SfenceStoreNarrow_verbindung`, which consumes `hreach`, `hdrain`,
`hmem`, `hto`, `hsse`). TARGET plus companion
`SfenceStoreNarrow_verbindung_zeuge` are jointly inhabited on a
non-degenerate reached run (two issues on two cores, memory-changing
drain fdS2→fdS3, foreign buffer pending, silicon SSE). Negative
mutations exist at both layers (parsed and fetched): no-SSE #UD,
pending-buffer refusal, MFENCE-without-SSE2 #UD, neighbour refusals.
No new diagnostic/gift/example/CLI numbers, no MARKE_EMIT changes, no
source/checker/Spec/goal/emitter edits, no friend-reserved optimiser
files. `CUTS` is precise and the claims do not exceed it.

Build evidence (pinned, author ran): `./lean-probe
grammatik/Grammatik/X86/SfenceStoreNarrow.lean` → `== 0 error(s)`;
`./lean-bau` → `Build completed successfully (485 jobs)`; `#print axioms
gabbro_ziel` → exactly `[propext, Classical.choice, Quot.sound]`;
per-theorem axioms within the standard set. The log also shows one
mid-development red probe (3 unsolved goals) repaired before the final
commit — honest iteration, final state green.

## Boundary of this review

I did not re-run the build: this lane owns report only ("no source or
live controls"), and every proof step is routine (`decide`/`rfl`/`simp`/
`unfold` over callees whose definitions and signatures I verified in this
clone), with complete pinned build evidence and no suspicious case
requiring reproduction. Acceptance rests on that evidence plus the
static verification above; the serial integration gate re-builds anyway.

## Minor remarks (non-blocking)

- `sfence_mfence_gleiches_tor`'s docstring says "exactly when this gate
  passes" but proves one direction (empty buffer ⇒ accepted MFENCE fence
  succeeds). The formal statement is precise; only the comment overstates.
- `sfence_erfolg`/`sfence_ohne_sse`/`sfence_puffer_verweigert` carry
  `(hok : laengeOk 3 = true)` as a premise though it is `decide`-closed;
  harmless and honestly stated, not a weakening.
- Nothing in the owner task was wrong. WC/NT store paths stay refused
  because canonical TSO has none — correctly marked OPEN, not claimed.
