# MUSE-REPORT-1111: Exact author-HEAD review of lane 1110

Clone `/home/simon/Dokumente/gabbro-muse/a1111`, branch `muse/1111` (verified:
`git branch --show-current` = `muse/1111`, HEAD `d493860a`). Report-only review;
no source, private, root or network changes. Own deliverable: this file only.

CANDIDATE: 1110 8a4054d77eacf0890483efb8b08e7cda219dded0

Author lane 1110 (base 4cfa9991c6aa33a5283365c3022cd03d915c2ff4), reviewed as
the exact committed snapshot in `.tmp/review/author-1110/` (SNAPSHOT.json:
clean, 2 files: `MUSE-REPORT-1110.md`,
`grammatik/Grammatik/X86/VectorIntegerFetchedSteps.lean`, 499 lines).
PATCH.diff scope confirmed: report + new module only.

## Independent verification performed (all read-only, inside this clone)

1. `./lean-probe` on the exact snapshot file:
   `== 0 error(s) in the COMPLETE output; exit 0`. Every `#print axioms` line
   within `[propext, Classical.choice, Quot.sound]` (probes partly axiom-free),
   matching the author's BUILD-EVIDENCE.json.
2. Unification-block test: byte copy of the exact candidate to private scratch
   (`.tmp/UnifyProbe1111.lean`, gitignored) plus a masked-count consumer
   (`match lesart with | .satt => 0 | .maskiert => 1`). Probe result:
   `== 1 error(s)`, `lean.unknownIdentifier: Unknown constant
   VecShiftLesart.maskiert` at the appended line, everything else elaborating.
   The unifying rewrite fails loudly at the interface, as designed.
3. Text checks with `rg` on the exact candidate file (evidence below).
4. `./lean-bau` on this (untouched) tree: `Build completed successfully
   (569 jobs).` (Author reported 513 jobs at its older base; no drift hit the
   candidate: all reused names below resolve in this tree and the exact file
   probes green here.)

## Criterion-by-criterion findings

- Evaluator reuse, no rival semantics: PASS. No `def` of any shift/step/fetch/
  decode/address/write semantics in the file (`rg` for rival `def`s: no match).
  Everything is reused by exact name from accepted modules, each verified to
  exist here: `vecShlQ`/`vecShrQ`, `vecShlQ_satt_null`, `vecShrQ_satt_null`,
  `vecShlQ_satt_vs_maske` (VectorIntegerHardwareForms.lean:175,182,200,226),
  `stepIntVec`, `stepIntVec_paddb`, `stepIntVec_psllqImm`,
  `stepIntVec_profil_verweigert`, `fetchIntVec`, `fetchIntVec_erfolg`,
  `intVec_fetch_pin`, `roundtrip_paddb`, `intVec_ext_weist_paddb_zurueck`,
  `intVec_ext_weist_movdquLd_zurueck`, `vecWrite_aufgeteilt`, `effAddr_prestate`
  (EffectiveAddress.lean:130), `laneNat_shlQ_satt`, `xmmSet_gleich`,
  `istUc_leer` (MemoryTypeHardwareExecution.lean:59), `decodeCpu_cpuid`,
  `ivT0..ivT4`, `ivM4`, `ivHwr`, `ivS3`, `ivS4`, `ivX4`, `ivCodeT`, `iv_gate`,
  `ivBereit`, `basisHw`, `basisCpu`, `basisKontrolle`.
- Divergence blocks unification: PASS. `VecShiftLesart` has exactly one
  constructor (`satt`); the words `maskiert`/`masked` occur only in doc comments
  and the refusal-theorem name. `vecFetched_shift_satt` closes by `cases` on the
  single reading; `vecFetched_maskiert_verweigert` pins count-64 zeroing via the
  preserved `vecShlQ_satt_vs_maske`. Live failure demonstrated (see item 2).
- 128-bit / shared-store limits are theorems, not comments: PASS.
  `vecGeteiltFrei_versperrt_a/u` (gate equations), `vecFetched_geteilt_u/a_`
  `verweigert` (fetched shared stores refused), `vecFetched_zwei_chunks`
  (128-bit store = two ordered 64-bit chunk writes via `vecWrite_aufgeteilt`,
  torn intermediate standing), `vecFetched_bit129_shl/shr_verweigert`.
- Slot interface coverage, no drift, provided+used: PASS. `VecSlotTag` (10 tags)
  and `vecSlotVon` reference exactly the task list in task order: pilot
  (`decode`), 575 (`decodeExt`), 666 (`decodeIntHw`), 668 (`fpHwDecode`), 662
  (`decodeLockExt`), 680 (`decodeIndirekt`), 682 (`mxcsrDecode`), 688
  (`decodeCpuFeature`), 692 (`pushfqByte`/`popfqByte`), plus `decodeIntVec`.
  All 14 imports are accepted modules present in this tree; 694 is covered by
  the `vecSlot_mmio` profile pin (`decodeExt` refusal via
  `intVec_ext_weist_movdquLd_zurueck` + `istUc_leer`), with the byte-slot
  coincidence with `ext` disclosed in CUTS and report note 2. Provided
  (tag + discriminator + 9 refusal pins) and used (the full chain is exercised
  by `vecFetched_slot_schnittstelle` over PADDB bytes and by the CPUID
  producer-side zeuge).
- No 718/724 import: PASS. `rg` hits for `718|724` are two comment lines only
  (header line 9, CUTS line 477). No such import exists.
- Joint _zeuge + three probes: PASS. `vecFetched_joint_zeuge` conjoins fetched
  agreement (`vecFetched_schritt_zeuge`, pinned fetched PADDB) with the 686
  lane-shift `ivS3` and memory-store `ivS4` legs plus a decided byte-18 change:
  a reached multi-step run with a lane shift AND a memory-changing row. Per-row
  zeugen for all three targets exist. Probes: masked-count reading refused,
  shared store claimed executable refused (aligned + unaligned twins), 129th-bit
  dependence refused (shl + shr twins). The "table some function writes" clause
  has no source-level meaning at this machine layer; the author states the
  analogue (a written memory byte) honestly in report note 3 without weakening
  the run requirement. The task's ZEUGE shape is met exactly.
- CUTS honesty: PASS. Each open point matches what is (not) proved: YMM upper
  unmodelled, no 128-bit single-copy atomicity claimed, shared stores refused
  until the 6B TSO bridge, 730 canonicality reused-not-reproved, slot
  disjointness pinned-bytes-only, masked unification blocked by construction,
  source/budget/progress/call-log open, 718/724 not imported.
- One-line import: PASS WITH INTEGRATION NOTE. The file is the module
  `Grammatik.X86.VectorIntegerFetchedSteps`; `grammatik/Grammatik.lean` here
  takes appended one-line imports. The author could not add the line (lane
  sandbox owns only the new module + report) and documents this as integration
  note 1; the merge script unions these imports. Exactly one line is needed.
- Gates: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` (only `#print
  axioms` lines), every premise used, nothing called a semantics, English only.

## Non-blocking observations

- Author's build log shows two unused-`simp`-arg warnings (`hpush`/`hpop` around
  line 364-365). Cosmetic; 0 errors, proofs unaffected.
- The `bit129` probes are thin by type (pure-function congruence over the
  128-bit `Vektor` type) but genuine: they pin that equal words never shift
  apart, i.e. no hidden extra state influences the shift.
- `vecFetched_slot_schnittstelle_zeuge` uses `Classical.choice`; still within
  the standard `gabbro_ziel` axiom set.

## Machine-readable verdict (substance unchanged from the review above)

VERDICT: ACCEPT

Evidence: exact-file probe `0 error(s)` reproduced independently; unification
attempt fails with `Unknown constant VecShiftLesart.maskiert`; all reused names
resolve to accepted modules; limits are proved theorems; slot coverage matches
the task list with no drift and no 718/724 import; joint witness and all three
probe kinds present; CUTS honest; axioms standard.
