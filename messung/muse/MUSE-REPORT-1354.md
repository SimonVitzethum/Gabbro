# MUSE-REPORT-1354: Exact review of candidate 1353 (IntExtend family)

CANDIDATE: 1353 09e6dab8b79bd44259df339f4e547b2a55523433

VERDICT: ACCEPT

Pinned base `b7b96da86bff9c5966bc0356ec07c6ed0ee21cba`, files:
`MUSE-REPORT-1353.md`, `grammatik/Grammatik.lean` (one added import line),
`grammatik/Grammatik/X86/IntExtend.lean` (new, 2452 lines).

Reviewer lane 1354, clone `/home/simon/Dokumente/gabbro-muse/a1354`,
branch `muse/1354` (verified). OWN ONLY this report. The author clone and
the pinned hash were never read (`git show/log/diff` on the hash never
used); the candidate was checked as delivered files under
`.tmp/review/author-1353/`.

## 1. What was checked and how

- Full read of `IntExtend.lean` (all 2452 lines, in sections), `OWNER-TASK.md`,
  `MUSE-REPORT-1353.md`, `BUILD-EVIDENCE.json`, `SNAPSHOT.json`, and the
  `Grammatik.lean` hunk of `PATCH.diff`.
- `grep` over the candidate: `sorry|admit|axiom |native_decide|unsafe|sorryAx`
  (only English prose "admits" plus the quoted HARD RULES text; no tactic or
  declaration use), `intro _|have _ :=|forall rho|split_ifs|norm_num|ring_nf`
  (no hits), AMD claims (none; only Intel SDM provenance, see §4).
- `./lean-probe .tmp/review/author-1353/grammatik/Grammatik/X86/IntExtend.lean`
  run in place (no copy; the wrapper resolves `import Grammatik.*` from the
  project root, so the in-place path elaborates against this clone's current
  dependencies): `== 0 error(s) in the COMPLETE output; exit 0`, with all 27
  `#print axioms` lines inside the standard set
  (`propext`/`Quot.sound`, some `propext`-only, one additionally
  `Classical.choice` via a simp lemma, exactly as the author reports).
- `./lean-bau` on this clone (base `78a14701`, without the candidate, see §5):
  `== exit 0; 0 error line(s) in the COMPLETE output`,
  `Build completed successfully (713 jobs)`.
- `python3 instrumente/lean-layout.py --check`: passes with the expected lane
  note ("nothing moved ... coordinator places it after the merge").

## 2. Findings per review criterion

- **Banned constructs:** none. No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
- **Axioms:** standard only (measured by my own probe run, not copied from the
  report).
- **Existing files:** untouched except exactly one line,
  `+import Grammatik.X86.IntExtend` (`PATCH.diff` line 171). No theorem
  weakened (new file only, all names `ix*`/`Ix*`/`shld*`/`shrd*`).
- **Premises used:** no discarded premises found; adapter theorems
  (`adapterIntExtend_wf/_ok/_proj`, `ixHwRegSchritt_weiter/_verweigert/_weiter_wf`)
  consume every hypothesis (spot-read all proofs); the joint witness
  `ixHw_zeuge` proves a 13-conjunct statement by `refine` with one theorem
  per conjunct, so nothing is weaker than claimed.
- **Lifted, not copied:** `extendNarrow`/`mergeRegNarrow` (NarrowOps),
  `bswap32`/`bswap64` (ByteSwap), `shlB`/`shrB`/`sarB` with
  `shlNachweis`/`shrNachweis`/`sarNachweis` (ShiftLogic), `rotNimmPraefix`/
  `rotBreite`/`rotPraefixBytes`/`rotSibTail` (IntRotate),
  `HwAdapter`/`HwWf`/`setKernVonFp`, `issueByte`/`loadByte`/`flushKern`,
  `basisHw`/`basisBereit`, `zeugeSpeicher`/`bswapZeugenWort` are reused by
  reference; `grep` confirms no `def extendNarrow|mergeRegNarrow|bswap32|shlB`
  redefinition. `shldB`/`shrdB` are new definitions, which is correct: no
  accepted double-shift evaluator exists to lift.
- **Refusals really refuse:** all `decide` pins elaborated green in my probe
  run, including LOCK (`ix_weist_lock_zu`, `ixHw_weist_lock_zu`), REX.R over
  groups, rotate digits /0–/3, memory-mode extension rows, AH without REX,
  66h on MOVSXD/BSWAP, truncation, past-width double-shift counts, and the
  adapter/mem/length refusals (`adapterIntExtend_verweigert_bei_*`,
  `ixSchritt_mem_verweigert`, `ix_laenge_misslungen`).
- **Witness non-degenerate:** `ixHw_zeuge` runs two cores (core 0 MOVSX
  `0xFF` -> all-ones in RAX; core 1 BSWAP plus SHL-by-1 and SHL-by-CL with
  changed registers) beside a buffered byte store with owner-only forwarding
  (`ixHw_weiterleitung` = 42 owner, `ixHw_fremd_alt` = 0 foreign) and a drain
  that changes shared memory 0 -> 42 (`ixHw_spuelung_aendert_speicher`,
  `ixHw_fremd_neu`), with mem/length/LOCK refusals beside it. Genuine
  memory-changing run, not an empty or table-less witness.
- **Silicon facts** (against `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.*`,
  spot-checked): 0F B6/B7/BE/BF, 63 bare + REX.W, 0F C8+rd, D0/D1/D2/D3/C0/C1
  with /4 /5 (/6 SHL alias) /7, 0F A4/A5/AC/AD all correct; 8/16-bit merge and
  32-bit zero-extend writeback correct; count masking reuses the accepted
  `schiebeZaehler`; OF defined exactly at masked count 1 and free otherwise
  (`shldUeberlauf_char`, `shrdUeberlauf_char`); masked count 0 preserves all
  flags (`ShldGueltig`, `shldFlags`/`shrdFlags` return `vor`) and leaves the
  value truncated-identity; past-width counts refused, never pinned. The one
  subtle point I checked (flags at count 0) is silicon-correct.
- **No over-claim:** CUTS names exactly what is proved and lists as NOT proved:
  no hardware correspondence, no source/IR/loader/entry/budget link, no
  per-access W/GX simulation, no whole-word atomicity beyond byte drains, no
  timing/power; the only W/GX mention in the file is in that NOT-claimed list.
  Overlap with `decodeCore` (REX.W extension rows) is handled openly with
  proved prefer-accepted pins, per the WdHw precedent. 66h-BSWAP and
  no-REX-AH stay refused as documented gaps.
- **Layout:** check passes; file stays at the task path until the coordinator
  places it at merge (author report §2.2 already says so).

## 3. What remains open / notes for the merger (not verdict-blockers)

- The candidate base (`b7b96da8`) predates this clone's base (`78a14701`;
  e.g. `SystemDecode`, `SseFourOne` landed since). My probe ran the candidate
  file against the NEW dependencies: green, so no drift breakage in the file.
  The full build WITH the added import line still belongs to the merge gate
  (I could not stage it: this lane owns only the report, and the shell
  blocked the temporary copy into `grammatik/`).
- Author report §7's "uncommitted" line is stale but honest: BUILD-EVIDENCE
  shows the commit `09e6dab8` landed afterwards with the three files staged.
- Nothing in the owner task looks wrong; the one collision it predicted
  (`decodeCore` owning the REX.W rows) was resolved by prefer-accepted
  dispatch, not by weakening.

## 4. Task feedback

The review instruction "copy the candidate's Lean file into your own clone
first" conflicts with "OWN ONLY MUSE-REPORT-1354.md" under the shell
permission filter (the `cp` was rejected). It was unnecessary: `./lean-probe`
accepts any path and resolves imports from the project root, so probing the
delivered copy in place checks the identical content. Suggest rewording to
"probe the delivered copy in place".

Co-Authored-By: muse-agent-1354 <muse-agent-1354@noreply.invalid>
