# MUSE-REPORT-1132: Exact review of candidate 1131 (SIMD integer forms / enabled-state gates)

## VERDICT: ACCEPT

CANDIDATE: lane 1131, HEAD `7168f0ad31dbdb9e2ad0649e2fa644cea22d1f62`
(base `8744590d77cbc7f31d809b4c62cd303bae4ed66f`), reviewed as the exact
snapshot `.tmp/review/author-1131/` (`SNAPSHOT.json`: files
`MUSE-REPORT-1131.md`, `grammatik/Grammatik.lean`,
`grammatik/Grammatik/X86/HwVector.lean`, `clean: true`).

## What was checked

1. Patch shape: `PATCH.diff` (2344 lines) touches exactly the three files
   above. `Grammatik.lean` gains exactly one line,
   `import Grammatik.X86.HwVector`. Nothing else existing is modified.
2. New file `HwVector.lean` (2226 lines, 46 `def`s, 91 `theorem`s):
   read the full diff; grepped for banned forms; read the machine lift
   (§§6-7), agreement, fetch bridge, refusals, witness and CUTS sections.
3. Author build history (`BUILD-EVIDENCE.json`): iterated red-to-green;
   one intermediate full build failed on a duplicate `issueListe_mem`
   (own lemma vs `ConcurrentIntegerExecution`), which the author then
   removed in favour of reuse-by-import. Final author entries: probe
   0 errors, `lean-bau` 601 jobs green.
4. Independent checks in this clone (branch `muse/1132`, HEAD `86a073bc`):
   - `./lean-bau`: `== exit 0; 0 error line(s)`, 
     `Build completed successfully (607 jobs).`
   - `./lean-probe .tmp/review/author-1131/grammatik/Grammatik/X86/HwVector.lean`
     (exact candidate bytes, read-only, imports resolved against this
     tree): `== 0 error(s) in the COMPLETE output; exit 0`. All 32
     `#print axioms` outputs match the file's claims: every main theorem
     depends only on subsets of `[propext, Quot.sound]`.

## Checklist results

- Banned forms: no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`,
  `split_ifs`, `norm_num`, `ring_nf` in code (grep over the diff; the two
  hits are prose inside the author's report). No `Prop`-typed premises;
  no `intro _` / `have _ :=`.
- Lifted, not copied: all 46 `def`s are new `vec*`/`hvec*`/`ladeAcht`/
  `achtFun`/`drainListe`/`adapterVec` names. The accepted evaluator
  (`stepIntVec`, `vecRead`, `vecFuss`, `vecChunks_disjoint`,
  `issueListe`, `issueListe_mem`, `issueListe_anderer_kern`,
  `flushKern`, `vektorLegacyZugelassen`, `laengeOk`, `vektorGpFehler`,
  `fetchIntVec`, `decodeExt`/`encodeIntVec`) is referenced by name,
  never redefined. The mid-history duplicate-lemma collision was
  resolved by deletion + import before the final commit.
- Agreement is genuine: `vecRegSchritt_gleich` concludes about the NEW
  plug from the accepted equation as a premise (unfold + rewrite), not a
  restatement. `hwVecSchritt_einbettet`/`hwVecSchritt_projiziert` embed
  and project `HwSchritt` exactly; `hwVecSchritt_wf` preserves `HwWf` by
  cases with every premise used.
- Refusals really refuse: length, legacy gate (each side planted:
  cpu/kontrolle/osxmm/merkmal), `#GP` alignment on the `movdqa` shapes,
  per-byte read/write permissions, adapter core mismatch / old events /
  bare refusals, plus reused planted negatives (alias overlap, AVX row,
  dispatcher disjointness, saturate-not-mask).
- Witness is non-degenerate: `hvecWit_zeuge` conjoins `decide`-checked
  computations over a two-core run — fetched `paddb` (lane 0 wraps
  `0xFF + 0x02` to `0x01`, lane 1 adds independently), sixteen-issue
  `movdqa` store (buffer length 16, canonical memory unchanged),
  owner-only forwarding (core 0 reads `0x01`, core 1 reads `0`), drain
  changing shared memory `0 -> 0x01` observed from both cores with the
  torn halfway state standing, core-1 fetch refusal, both
  `HwVecSchritt` steps, and the alias/AVX/disjointness refusals beside
  it. Companion `_zeuge` for `vecRegSchritt_gleich`,
  `vecLaden_ist_vecRead` and `vecDrain_schreibt` on the same run.
- Silicon: no new encoding/fault fact is stated anywhere (only test-data
  hex literals); all hardware facts ride the accepted lane-686 rows and
  the CUTS block says exactly that, citing the SDM entry source.
- CUTS honest, no overclaim: no hardware correspondence, no vector
  atomicity (tearing table explicit), no per-access W/GX simulation, no
  source/loader/budget link, LOCK/RMW refused, AVX refused, YMM upper
  bits unmodelled. No W/GX or hardware-correspondence claim made.

## Notes (not verdict-relevant)

- The lane-1132 task pointed at the author clone, which HARD RULE 1
  forbids; the coordinator-supplied in-clone snapshot
  (`.tmp/review/author-1131/` with pinned HEAD in `SNAPSHOT.json`) is
  what made this exact review possible. Future reviewer lanes should
  name the snapshot path directly.
- Shell execution in this lane was intermittent (several `bash` calls
  rejected, single simple commands accepted); all verdict-bearing
  evidence above comes from commands that executed successfully.
  The transient `cp`-into-tree step was NOT performed: the read-only
  probe of the exact snapshot bytes plus the green baseline build give
  the needed evidence without touching owned-file boundaries (working
  tree holds only this report).

## Owned deliverable

New definitions/theorems by this lane: none (report-only review lane).
`./lean-bau` last result line:
`Build completed successfully (607 jobs).` (exit 0, 0 error lines).
Nothing remains open for lane 1132.
