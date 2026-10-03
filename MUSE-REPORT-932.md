# MUSE-REPORT-932: Exact review of author 782 (LFENCE load narrowness)

Lane 932, clone `/home/simon/Dokumente/gabbro-muse/a932`, branch `muse/932`.
Owns ONLY this file. No source touched, no live controls used.

CANDIDATE: 782 a8b4c7a5fbd06b98aa7dff99c363a5b66887ef18
VERDICT: ACCEPT (bounded: TSO/canonical-byte load-ordering narrowness; see scope below)

## Snapshot checked

Base `56537272a31df3de5d9b7898bbade91c3de817b8` matches this checkout's
lineage. Three files, clean: `MUSE-REPORT-782.md`,
`grammatik/Grammatik.lean` (one import line),
`grammatik/Grammatik/X86/LfenceLoadNarrow.lean` (new, 414 lines).
Reviewed the exact PATCH, the owner task, and BUILD-EVIDENCE; inspected the
new module in full and checked every canonical interface it touches against
this clone's accepted modules.

## Architecture verification (independent, not just Lean green)

- Byte forms: `0F AE E8` claimed for LFENCE. Correct: 15=0x0F, 174=0xAE,
  232=0xE8=0b11101000, ModRM mod=11 reg=101 (/5). Neighbour refusals
  `F8` (248=0b11111000, reg=111 /7 = SFENCE) and `F0` (240=0b11110000,
  reg=110 /6 = MFENCE) are the correct adjacent rows. Truncation and empty
  refusals present. Pilot `decode` and locked `decodeLock` disjointness are
  `by decide` on concrete bytes over the accepted computable decoders.
- Semantics: LFENCE as total, state-preserving TSO step (buffers and
  canonical bytes unchanged, acting-core `loadByte` preserved) with a
  fence-only, never-full-barrier event. This is the correct narrow
  abstraction: the local Intel reference text
  (`.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`) states "The
  LFENCE instruction establishes a memory fence for loads" and "the
  sequences LFENCE;SFENCE and SFENCE;LFENCE are not equivalent to MFENCE".
  The proved narrowness gap (MFENCE refuses a nonempty own buffer, LFENCE
  admits it) matches the canonical `LockedOps.lockSchritt` definition
  verified in this clone (`| .mfence => if (s.puffer c).isEmpty then
  some ... else none`), so `mfence_verweigert_bei_vollem_puffer` is a true
  lemma about canonical code, not an assumed premise.
- Byte step: fetch from actual executable memory via canonical `geholt`,
  admission (`lfenceZugelassen`: length equation + `laengeOk` + consumed
  prefix `ausfuehrbarN`) following the `fetchDekodiert` discipline; RIP+3
  with registers, flags and memory bytes preserved. Correct for LFENCE (no
  register/flag/data-memory effect). The standalone step + outcome type
  follows the accepted sibling pattern (`lockByteschritt` in
  `LockedInstructionExecution` is likewise its own def with
  weiter/verweigert selection lemmas); no dispatcher integration is claimed
  and CUTS scopes it out. No REX/width/MXCSR/interrupt claims are made,
  correctly: LFENCE has no operands and this layer raises no fault.
- No invented determinism: undefined/neighboring behaviour (dispatch-
  serializing MSR variant, CPUID gate, faults, silicon correspondence,
  TSO/W/GX bridge, timing/fairness, interrupts/devices) is listed OPEN in
  CUTS, never zeroed or ignored. The no-fault, unconditional-admission
  layering is stated, not smuggled into a guarantee.
- No guarantee weakening, no desired-simulation premise: every theorem is
  proved from canonical definitions; all premises of the target
  `LfenceLoadNarrow_verbindung` are used (`s c a` in the preservation
  conjuncts, `hne` in the MFENCE refusal). The `rfl` preservation legs are
  definitional but constitute the load-ordering claim together with the
  nontrivial refusal gap; the claim boundary is stated exactly.
- Witness `LfenceLoadNarrow_verbindung_zeuge` is jointly inhabited and
  non-degenerate: `sbNach1` reached by a real issue step (`sb_schritt1`,
  `lf_erreichbar`), nonempty core-0 buffer (`lf_puffer_voll`, `by decide`),
  memory-changing flush (`lf_flush` by `rfl` over canonical `flushKern`,
  `lf_speicher_aendert` by `decide`), fetched step 4096 -> 4099 with memory
  unchanged, plus MFENCE refusal on the same state. Negative mutations:
  SFENCE/MFence rows, truncation, empty input, pilot/locked refusals,
  post-image fetch and step refusals.
- Hygiene: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in the new
  file (only English prose matches). Axioms per BUILD-EVIDENCE are subsets
  of `propext, Classical.choice, Quot.sound`. No diagnostic/gift/example/
  CLI numbers, no MARKE_EMIT, no source/checker/Spec/goal/emitter or
  friend-reserved changes. `CUTS` block plus `#print axioms` for every main
  theorem present.

## Build evidence

Author BUILD-EVIDENCE: `./lean-probe .../LfenceLoadNarrow.lean` 0 errors;
`./lean-bau` green, 485 jobs (first attempt died at the final link with
`failed to create thread`, a known resource-exhaustion signature; retry
passed unchanged, no gate touched). Plausible and consistent with the
`decide`-heavy content. No red flags requiring reproduction; per this lane's
report-only scope no builds were launched here.

## Bounded acceptance scope

Accepted as: LFENCE load-only ordering over the ONE canonical `TSOZustand`,
canonical bytes with disjointness/round-trip/refusals, byte-facing
fetch/step under the admission discipline, and the proved MFENCE admission
gap, with a reached memory-changing joint witness. Still OPEN (not claimed):
silicon correspondence, store ordering/drain, dispatch-serializing
MSR/CPUID, faults, TSO/W/GX bridge, timing/fairness/progress,
interrupts/devices, source/checker/goal work.

## Task remarks

Nothing in the owner task appears wrong. The "exact admitted elimination
premise or refusal" is delivered as the MFENCE-on-nonempty-buffer refusal
plus the load-preservation fact, which matches the task.
