# MUSE-REPORT-662: LOCK atomic and fence final-byte execution

## Task
Lane 662: canonical byte parsing/encoding and real fetched execution for
essential LOCK XADD and LOCK CMPXCHG 64-bit word forms plus MFENCE, with a
proved adapter to the accepted `LockedOps` vocabulary, resolving the
simplified CAS false-path stutter against the manual.

## Owned files (only these touched)
- `grammatik/Grammatik/X86/LockedInstructionExecution.lean` (new, 1144 lines)
- `grammatik/Grammatik.lean` (one additive import line)
- this report

## What was done
1. **Codec (§1-§3):** `LockForm` (xadd64/cmpxchg64 over base+disp32, mfence),
   `LockAnweisung` (admitted form or parsed #UD, each with length),
   `encodeLock` (LOCK + REX.W + 0F C1/B1 + mod=2 ModRM + disp32/SIB;
   MFENCE as 0F AE F0), `decodeLock` (LOCK+register-dest parses to
   `lockAufRegister` #UD len 5; LOCK+MFENCE parses to `lockAufZaun` #UD
   len 4; MFENCE accepts any r/m with reg field 6). Generic round trips
   `roundtripLock`/`roundtripLock_len_ok` over any suffix.
2. **Execution (§4-§5):** `LockMaschine` (canonical `Zustand` + TSO buffers),
   `toTSO`, `LockAusgang` (ok / speicherFehler / udFehler / verweigert),
   `lockSchrittVoll`: XADD exchanges the old word into the source register
   with `add64` flags; CMPXCHG compares against RAX with `sub64` flags,
   installs on success, and on failure loads RAX **and writes the word
   back** (manual write cycle regardless of comparison); MFENCE gates on
   admitted SSE2 (`merkmalZugelassen ... .sseDoppel`) and the empty own
   buffer, moving only RIP. Success equations, #UD lemmas (parsed #UD,
   missing SSE2) and profile-refusal lemmas (buffer, misalignment).
3. **Adapter (§6):** `lockVoll_xadd_adapter`,
   `lockVoll_cmpxchg_erfolg_adapter`, `lockVoll_mfence_adapter` project
   onto `lockSchritt`/`casSchritt`. `lockVoll_cmpxchg_fehlschlag_adapter`
   resolves the mismatch explicitly: the accepted stutter and the
   write-back agree on observable bytes and the `false` answer, while the
   write-back additionally pins full `schreibbar8` of the footprint.
4. **Fetched layer (§7):** `decodeLockExt` tries accepted `decodeExt`
   first (no shadowing by construction; three closed rows proved refused
   by it), `lockFetch` reuses the canonical executable window
   (`geholt`, 15-byte cap, `ausfuehrbarN`), `lockByteschritt` runs
   `lockSchrittVoll` on the fetched instruction only, plus fetch-to-step
   correspondence and decidable observers.
5. **Witnesses (§8-§11):** five decode pins, four fetched runs (XADD
   10->15 returning old 10; CMPXCHG success 10->7 ZF set; CMPXCHG failure
   keeping 10 with RAX loaded ZF cleared; MFENCE with foreign buffer
   pending), nine planted refusals (LOCK-on-register #UD, LOCK-on-fence
   #UD, truncation, execute-denied, buffer, misaligned, SSE2-off #UD,
   read fault, write-back fault on failed comparison), and three joint
   `_zeuge` (XADD success, failure adapter with write permission, fence).

## Manual provenance checked (local snapshot, Intel SDM 325462-093US)
- LOCK prefix Vol. 2A 3-565/3-566 (lockable list, #UD rules, alignment
  does not affect LOCK integrity)
- XADD Vol. 2D 6-27/6-28 (opcodes, TEMP:=SRC+DEST/SRC:=DEST/DEST:=TEMP,
  flags, #GP non-writable, #UD LOCK-on-register)
- CMPXCHG Vol. 2A 3-193/3-194 (opcodes, write cycle without regard to the
  comparison, Operation with DEST:=TEMP on failure, flags, #UD rule)
- MFENCE Vol. 2B 4-15 (0F AE F0 with ignored r/m, ordering description,
  #UD without SSE2 and with LOCK)

## Checks
- `./lean-probe grammatik/Grammatik/X86/LockedInstructionExecution.lean`:
  `== 0 error(s) ...; exit 0`.
- `./lean-bau`: `Build completed successfully (460 jobs).`
- `#print axioms`: every main theorem depends only on subsets of
  `[propext, Classical.choice, Quot.sound]` (standard `gabbro_ziel` set).
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; every theorem
  premise is used; no Prop-typed premises.

## Open (see CUTS for the exact list)
Only 64-bit word rows; only mod=2 base+disp32 addressing; alignment is a
profile contract (silicon locks misaligned fields); no W/GX refinement, no
timing/progress claims; no SMC-overlap guard; device/MMIO/NT/speculation
effects open; generic arbitrary-input dispatcher disjointness beyond the
three pins open; split-lock/HLE/#AC open.

## Finding for the coordinator
Lean's term parser rejects a multi-line `{ s with a := b, <newline> c := d }`
structure update when nested directly inside `⟨...⟩` (single-line form
parses; reproduced in isolation). Workaround used: single-field updates,
each on one line, chained through `let`s. No build impact.
No part of the lane task looked wrong; the "write permission on failed
comparison" requirement is real manual text (CMPXCHG Vol. 2A 3-193) and is
modelled plus pinned (`zeug_schreibfehler_bei_fehlschlag`).
