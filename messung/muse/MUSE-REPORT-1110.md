# MUSE-REPORT-1110: Packed-integer fetched steps with a dispatch-slot API

Clone `/home/simon/Dokumente/gabbro-muse/a1110`, branch `muse/1110` (verified).
New module `grammatik/Grammatik/X86/VectorIntegerFetchedSteps.lean` only
(+ this report). 4 commits on the branch. No network, no push.

## What was built

Fetched packed-integer execution for the accepted 686 `IntVecOp` rows on
the common machine discipline, reusing (never forking) the 686 lane
evaluators `vecShlQ`/`vecShrQ`, `stepIntVec`, `fetchIntVec`,
`intVecByteschritt`, the joint `ivT0..ivT4` chain and its pins.

Definitions (new): `vecGeteiltFrei` (shared-store gate: both store rows
refused iff `geteilt`), `vecFetched` (fetch actual bytes, gate, then
`stepIntVec`), `VecShiftLesart` (saturating-only reading; deliberately
no masked constructor), `VecSlotTag` (10 slots), `vecSlotVon`
(byte discriminator, peer-last order), `vecSattCodeBytes`,
`vecSattCodeMem`, `vecSattT` (count-64 fetch state, xmm4 = `ivX4`).

Target theorems: `vecFetched_schritt` (fetched agreement, every row),
`vecFetched_satt_erhalten` (over-width imm8 shift zeroes all lanes
through fetching; length guard from the fetch discipline, hardware gate
recovered from the successful step), `vecFetched_slot_schnittstelle`
(PADDB bytes classify to `.intVec`).

Zeuge companions: `vecFetched_schritt_zeuge` (pinned fetched PADDB),
`vecFetched_satt_erhalten_zeuge` (fetched count-64 zeroes xmm4),
`vecFetched_slot_schnittstelle_zeuge` (producer side: CPUID bytes land
in `.cpuFeat`), `vecFetched_joint_zeuge` (fetched agreement + 686
lane-shift `ivS3` + memory-changing store `ivS4` with byte 18 changed;
non-degenerate: reached multi-step run with a memory-changing step).

Planted refusal probes: `vecFetched_maskiert_verweigert` (count 64
preserves nothing), `vecFetched_geteilt_u_verweigert` /
`vecFetched_geteilt_a_verweigert` (shared stores refused),
`vecFetched_bit129_shl/shr_verweigert` (no 129th-bit dependence).

720/730 discipline: `vecFetched_adresse_prestate` (accepted `effAddr`,
no second address model; 730 aliasing transfers),
`vecFetched_zwei_chunks` (128-bit store = two ordered chunk writes,
torn intermediate stands; 720 no-single-event rule, via
`vecWrite_aufgeteilt` on `ivHwr`).

Slot coverage: refusal pins per family on the PADDB bytes
(`vecSlot_pilot/intHw/fpHw/lock/ind/mxcsr/cpuFeat/flags_...`, ext reused
from 686) plus `vecSlot_mmio` (694: unified dispatch refuses the load
bytes; empty UC profile covers nothing). No overlap found, so the
peer-last order stands without reordering.

## Check results

- `./lean-probe grammatik/Grammatik/X86/VectorIntegerFetchedSteps.lean`:
  `== 0 error(s)`, no warnings.
- `./lean-bau`: `Build completed successfully (513 jobs).` (project green;
  the new module is probe-checked; see integration note).
- `#print axioms`: every main theorem within
  `[propext, Classical.choice, Quot.sound]` (most use only a subset;
  probes use none). No `sorry/admit/axiom/native_decide/unsafe`;
  every premise is used; nothing is called a semantics.

## Open / CUTS (in-file block is authoritative)

YMM upper bits unmodelled; no 128-bit single-copy atomicity; shared
stores refused until the 6B TSO bridge (TSO/GX open); 730
canonicality not re-proved (per-byte permissions as in 686); slot
disjointness proved for pinned bytes only; masked unification blocked
by construction; source/budget/progress/call-log open; 718/724 not
imported.

## Integration notes / possible task issues

1. The lane sandbox permits editing only the new module + this report,
   so the `import Grammatik.X86.VectorIntegerFetchedSteps` line for
   `grammatik/Grammatik.lean` (HARD RULES §5) is NOT added here;
   integration must append it (merge script unions these imports).
2. The nine "producer decoder" entries used: `decodeExt` (575),
   `decodeIntHw` (666), `fpHwDecode` (668), `decodeLockExt` (662),
   `decodeIndirekt` (680), `mxcsrDecode` (682), `decodeCpuFeature`
   (688), `pushfqByte`/`popfqByte` (692), and for 694 (no own decoder;
   shares `decodeExt` via `fetchExt`) the `istUc` profile side. If the
   task meant different entry points for 682/692/694, the pins make the
   chosen ones explicit.
3. The joint witness reuses the 686 `iv` chain for the memory-changing
   leg (hardware-level non-degeneracy: reached steps + changed byte);
   there is no source-level table/function structure at this layer, so
   the shared-gate "table some function writes" clause is met by the
   analogue (a written memory byte), stated as such, not weakened.
4. Nothing in the task was found wrong; the saturate-vs-mask divergence
   is documented AT `VecShiftLesart`/`vecFetched_shift_satt` such that a
   unifying consumer fails to typecheck (no masked constructor).
