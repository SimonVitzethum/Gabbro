# Muse Report 928 — Exact review of author 778 (LOCK XADD fetch-add)

Lane 928, clone `/home/simon/Dokumente/gabbro-muse/a928`, branch `muse/928`
(base `56537272`, matches snapshot base).
Review-only lane: owns ONLY this file. No source touched, no live controls used.

CANDIDATE: 778 7f1d760210299e16164813ac25f9e95de3f9b04a

VERDICT: ACCEPT

Scope of this acceptance is bounded (bounds in §5, reproduction boundary in §4).

## 1. What was reviewed

Exact pinned snapshot `.tmp/review/author-778/` against base `56537272`:

- `OWNER-TASK.md` (lane 778 task, TARGET `LockXaddFetch_verbindung` + companion
  `LockXaddFetch_verbindung_zeuge`, joint non-degenerate memory-changing witness).
- `PATCH.diff` (381 lines): exactly 3 files — new
  `grammatik/Grammatik/X86/LockXaddFetch.lean` (258 lines),
  one appended import line in `grammatik/Grammatik.lean`
  (`import Grammatik.X86.LockXaddFetch`), `MUSE-REPORT-778.md`. Nothing else.
- `MUSE-REPORT-778.md` and `BUILD-EVIDENCE.json` (15 command records).
- Clone-local manuals `.tmp/HARDWARE-REFERENCES/`: `REFERENCES.json`
  (Intel SDM combined vols 1–4, edition 325462-093US, Sep 2026, verified
  2026-10-02) and `intel-instruction-reference.txt`.
- Every referenced foundation name re-checked in this clone at base:
  `LockedOps` (`SperrBefehl.xadd64`, `lockSchritt`, `lockKosten`,
  `casKosten`, `cas_schleife_unbeschraenkt`, `lockSchritt_xadd_erfolg`,
  `ausgerichtet8`), `LockedInstructionExecution` (`LockForm.xadd64`,
  `encodeLock`, `lockLen`, `decodeLock`, `decodeLockExt`,
  `decodeLockExt_lock`, `lockSchrittVoll`, `lockSchrittVoll_xadd_erfolg`,
  `lockVoll_xadd_adapter`, `lockFetch`, `lockByteschritt`, `lockArt`,
  observers, `pinXadd`, `pinRegUd`, `pin_lock_xadd_decodiert`,
  `pin_lock_ext_verweigert_xadd`, `zeugXadd`, `zeug_xadd_fetch_ok`,
  `lockSchrittVoll_xadd_erfolg_zeuge`, `zeug_puffer_verweigert`,
  `zeug_unaligned_verweigert`, `zeug_reg_ud_fetched`,
  `zeug_ohne_exec_verweigert`, `lockCodeExec`, `lockCodeNie`,
  `lockDataRW`, `einEintrag`, `basisHw`, `basisBereit`),
  `ExtendedExecution` (`decodeExt`), `Wort.add64`, `Speicher.Fuss`,
  `Ausfuehrung.laengeOk`. All present with compatible statements.

## 2. Architecture findings (each verified, none a defect)

- Byte forms: `pinXadd = [F0,48,0F,C1,85,00,00,00,00]` is LOCK, canonical
  REX.W (`0x48`: W=1, X=0, in `rexLockBits`), opcode 193 (XADD), ModRM
  `0x85` = mod 2 (memory + disp32), reg 000 (rax), r/m 101 (rbp, no SIB),
  length 9 = `lockLen` non-SIB shape. Matches the claimed row exactly.
- Register/width/flags: 64-bit word only; source takes old word, word grows
  by source register, flags are `(add64 alt sval).2` (full defined ADD
  flags per `Wort.lean`; x86-64 ADD has no undefined flag here, so no
  unsound determinism). RIP advances by parsed length. No implicit RAX
  use (correct: XADD has none, unlike CMPXCHG).
- Memory/TSO/atomicity: single RMW event (`ev.istRmw = true`) over the
  pinned 8-byte `Fuss` footprint (`Fuss` is 8 addresses; the length-8
  conjuncts hold); success needs empty own buffer, post-state buffers
  untouched; TSO agreement via accepted `lockVoll_xadd_adapter` on the
  same words. Permission overclaim avoided: the success theorem takes
  `write64` success as premise instead of asserting permission.
- "Full barrier" bound: proved as the LOCAL barrier the accepted model
  reaches (own buffer empty + buffers untouched + canonical-memory op).
  No foreign-buffer drain or device/MMIO fence is claimed; report §"Task
  remarks" and CUTS state this boundary plainly. Bounded acceptance, not
  a silent weakening — a global fence would exceed the accepted vocabulary.
- Gates: no feature gate invented or dropped for XADD (the cited entries
  carry none; the SSE2 gate stays with MFENCE and its owner).
- Dispatch: `decodeExt` refuses the bytes (reused pin, no older row
  shadowed), `decodeLockExt` takes the row whole where it refuses
  (argument order matches `decodeLockExt_lock`: bs, a, rest, h1, h2).
  Admitted bytes enter only through the common architecture.
- Cost: `xaddKosten` reuses `lockKosten` (= 1 for `.xadd64`); `casKosten n
  = n + 1`; the `≤` is a shape count, retry unboundedness stays with
  `cas_schleife_unbeschraenkt`. No latency/timing claim (consistent with
  `HardwareAssumptions`: `lockKosten` is never a latency).
- Refusals (all four reuse accepted `decide` pins with identical
  arguments): pending own store → `.verweigert`, misaligned word (8193)
  → `.verweigert`, LOCK on register destination → `.udFehler`, no-exec
  bytes → `.verweigert`. No silent fetch-add.
- Witness: reuses `lockSchrittVoll_xadd_erfolg_zeuge` (`zeugXadd`: word 10
  at 8192, delta 5 in rax, base rbp, empty buffer, 9 checked bytes),
  fires the connection, and shows the reached FETCHED run changing memory
  10 → 15 with old 10 back through rax and start word observably changed
  (`hne`). Jointly inhabited, non-degenerate, memory-changing. TARGET
  ZEUGE obligation met.
- HARD RULES: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`
  (grep hits are only `#print axioms` lines and prose "admitted");
  no `Prop`-typed premises; every premise is used (`hbuf/hali/hrd/hreg/
  hok/hwr` each pin one guard of `lockSchrittVoll_xadd_erfolg`/adapter;
  `hw`/`bp` passed through as step arguments); CUTS block + `#print
  axioms` per theorem present; English; no new diagnostic/gift/example/
  CLI numbers; no MARKE_EMIT, source/checker/Spec/goal/emitter, or
  friend-reserved optimiser changes.
- Manual provenance: LOCK Vol. 2A 3-565/3-566 and XADD Vol. 2D 6-27/6-28
  confirmed present in the local snapshot text (table-of-contents lines
  31928/32605, entries at 63495ff/137733ff). No silicon, vendor, or cycle
  claim.

## 3. Claim vs proof (no overclaim found)

The report claims only: constant-cost word fetch-add over reused
vocabulary, local barrier, one atomicity unit, pinned bytes, four planted
refusals, joint witness — each discharged by the named accepted lemma.
NOT claimed (CUTS): silicon correspondence, new codec rows, narrower
widths / other LOCK forms / other addressing modes / unlocked XADD, W/GX
refinement, timing/progress/fairness, source/checker/contract/budget/duty/
goal changes. The claim matches the proof.

## 4. Evidence and reproduction boundary

Author evidence is coherent: final `./lean-bau` green
(`== exit 0`, `Build completed successfully (485 jobs)`), final
`./lean-probe` 0 errors with axiom prints (`LockXaddFetch_verbindung`
and witness on `[propext, Quot.sound]`, helpers on `[propext]` or none —
within the `gabbro_ziel` budget), scratch `gabbro_ziel` probe standard
`[propext, Classical.choice, Quot.sound]`. Mid-development probe failures
in the log (one `regSet`/`schrittRegister` subgoal, one anonymous-
constructor notation error) were repaired in-file — an honest trace, and
the fixed lines verify against the foundation here. Transient red builds
(missing-olean root step ×3, `failed to create thread` exit 134 ×3) are
the known apparatus issues (AGENTS.md §11), not candidate defects.

Reproduction boundary (stated honestly): I did NOT execute the candidate
build in this clone, because that would require adding its source file to
`grammatik/` outside my owned files ("Own only MUSE-REPORT-928.md, no
source"). Independent verification is static but complete: every one of
the ~25 referenced names and all four refusal instantiations re-checked
statement-for-statement against base `56537272` (identical to the snapshot
base), byte-level pin decode hand-verified, and the PATCH confirmed
confined to the 3 declared files with `clean: true`.

## 5. Bounded acceptance (not repairs)

- Scope is the 64-bit non-SIB row only; the SIB (len-10) XADD shape is
  covered generically by the owner's `roundtrip_lock_xadd`, not by this
  candidate's pins — correctly left open in CUTS.
- The barrier result is local-only (see §2); any consumer needing a
  global fence must look to the fence owner, not this module.
- No W/GX refinement leg is attempted; the bridge owns it.

None of these is a defect: each is an explicitly stated bound, and
demanding more would exceed the accepted vocabulary or the owner task.

## 6. Result

The reviewed candidate (stated once at the top of this report) is accepted
within the bounds of §5 and the reproduction boundary of §4.

No repairs requested. No guarantee weakened, no desired-simulation premise
introduced, no fake closure found.
