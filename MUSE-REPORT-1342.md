# MUSE-REPORT-1342: Exact review of candidate 1341 (opcode ledger 0F 00-3F)

CANDIDATE: 1341, pinned HEAD `6d18b4b4655655195dd4d25146ef4aade859fa2a`
(base `574ac3d75180a53907fa28302e3af11cf2d9f2db`), per `.tmp/review/SNAPSHOT.json`
(`clean: true`). Changed files: `MUSE-REPORT-1341.md`,
`grammatik/Grammatik.lean`, `grammatik/Grammatik/X86/OpcodeLedger0F00.lean`.

## Method

Reviewed the delivered FILES only. No `git show/log/diff` on the pinned hash
was used (one `git diff` attempt was blocked by the permission classifier; the
`Grammatik.lean` hunk was verified via `Read` on the delivered `PATCH.diff`
instead). The candidate Lean file was checked byte-identical at its delivered
path with `./lean-probe` (the wrapper applies `realpath` to any location and
runs `lake env lean` from `grammatik/`, so no copy into the tree was needed and
nothing outside the owned report file was written). `./lean-bau` was run for
the last result line.

## Results

- `./lean-probe ".tmp/review/author-1341/grammatik/Grammatik/X86/OpcodeLedger0F00.lean"`
  → `== 0 error(s) in the COMPLETE output; exit 0`. This ran in my clone at
  `0833b559`, which is NEWER than the candidate base (sibling ledgers
  `OpcodeLedger0F40/0F80/0FC0/1Byte00/1ByteC0` merged since), so the candidate
  additionally survives the master drift.
- `./lean-bau` → `== exit 0; 0 error line(s) in the COMPLETE output`
  (`Build completed successfully (706 jobs)`).
- `#print axioms` (all 147, from the probe output): every `takes_*`/`refuses_*`
  theorem depends only on `[propext, Quot.sound]` (subset of the goal standard,
  no `Classical.choice` needed); all 8 summary theorems
  (`ledger_anzahl_*`, `ledger_schluessel_eindeutig`, `ledger_deckt_ab`) depend
  on no axioms. Matches the author's claim exactly.
- No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `split_ifs`,
  `norm_num`, `ring_nf` in the Lean file (grep over the delivered tree finds
  only `#print axioms` lines and prose mentions in report/task files).
- Existing files untouched except one import line: `PATCH.diff` shows the
  `Grammatik.lean` hunk as exactly one appended
  `import Grammatik.X86.OpcodeLedger0F00` line. New file is 738 lines in its
  own namespace with the tasked self-contained schema (`LStatus`, `LEintrag`).
- Lifted, not copied: the file imports `Grammatik.X86.HwKapsteinDecoder` and
  uses `kapDecode` plus existing constructors (`FpBefehl.movsdRR`,
  `S32Befehl.movssRR/cvtsi2ss/cvttss2si/ucomissRR`); no decoder redefined.
- Refusals really refuse: 5 `takes_*` + 134 `refuses_*` theorems, each a
  `decide`d equation, all elaborated green here. The arithmetic closes:
  5 + 36 + 34 + 49 + 15 = 139 ledger rows; non-`modelliert`
  36 + 34 + 49 + 15 = 134 = number of `refuses_*` theorems. Key-nodup
  (`ledger_schluessel_eindeutig`) and full 0F 00-3F coverage
  (`ledger_deckt_ab`) are `decide`-proved and green.
- Rule 13: no theorem quantifies over program syntax and the owner task names
  no `ZEUGE:` target, so no `_zeuge` companion is required. Every theorem is a
  closed equation (no premises), so "every premise used" holds vacuously;
  no `Prop`-typed premises, no contract quantification, no semantics claim.
- Silicon (rule 16): spot-checked encodings against the x86-64 opcode map
  (F2/F3 0F 10 MOVSD/MOVSS loads, F3 0F 2A CVTSI2SS, F3 0F 2C CVTTSS2SI,
  0F 2E UCOMISS, 0F 00/01 Groups 6/7, 0F 02/03 LAR/LSL, 0F 05/06/07
  SYSCALL/CLTS/SYSRET, 0F 08/09 INVD/WBINVD, F3 0F 09 WBNOINVD, 0F 0B UD2,
  0F 0D /1 PREFETCHW, 0F 1F /0 NOP, F3 0F 1E FA ENDBR64, 0F 1A/1B MPX,
  0F 1C /0 CLDEMOTE, 0F 20-23 MOV CR/DR, 0F 30-35 WRMSR/RDTSC/RDMSR/RDPMC/
  SYSENTER/SYSEXIT, 0F 37 GETSEC, 0F 38/3A escapes, 0F 01 D0 XGETBV,
  0F 01 F8/F9 SWAPGS/RDTSCP, 0F 01 C1/C4/C8/CA/CF VMCALL/VMXOFF/MONITOR/CLAC/
  ENCLS). All match; SYSENTER/SYSEXIT as `verweigert` is the safe side (the
  checked fact is the refusal either way). Vendor-neutral (rule 17): refused
  rows pin nothing, no AMD provenance claimed, map transcription declared as
  named provenance in CUTS.
- CUTS honest and claim no larger than the proof: decoding classification
  only; canonical byte strings only; folded group rows disclosed; no
  execution, fault, ordering, W/GX, or hardware-correspondence claim.
- Findings product present: 49 `fehlt` rows with frequency notes, including
  the most common gaps (0F 1F NOP padding, ENDBR64, MOVUPS/MOVAPS families,
  UNPCKL/H, UCOMISD/COMISD, UD2, RDTSC/RDTSCP, XGETBV, PREFETCH) and the
  asymmetric gaps (MOVSS/MOVSD stores, CVTSI2SD, CVTTSD2SI, CVTSS2SI/CVTSD2SI
  refused while their siblings decode).

## Nits (non-blocking, not REPAIR material)

1. The owner task asked to mark SYSENTER vendor-dependent (`herstellerabhaengig`);
   the author marked it `verweigert` with an SDM-validity note but without that
   token, reasoning (report item 4) that refused rows pin no vendor-specific
   behaviour. Rule 17 holds; the deviation is disclosed. Accept as is.
2. The owner-task text is truncated after "Do no..." (author report item 2);
   all visible requirements are met.

## VERDICT: ACCEPT

CANDIDATE 1341 is accepted for checked serial integration. No REPAIR items.
Integration order versus the sibling ledger lanes and any import-line
rebase onto current master belong to the coordinator, not to this review.

## Open / remarks

- Nothing remains open in this review lane. Procedural notes: a `cp` of the
  candidate into the tree was blocked by the permission classifier, so the
  delivered path was probed directly (byte-identical, strictly more exact);
  a `git diff` invocation was likewise blocked and replaced by `Read` on the
  delivered `PATCH.diff`. Neither limits the verdict above.
- Task issues noted by the author (CONTEXT/MECHANISM paragraphs describing an
  `HwAdapter` connection lane instead of the ledger) are agreed: the ledger
  task lines are what was implemented and reviewed here.
