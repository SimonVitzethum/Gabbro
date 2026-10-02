# MUSE-REPORT-586: Independent exact-candidate connection review of 568

## Scope and identity

- Clone verified: `/home/simon/Dokumente/gabbro-muse/a586`, branch `muse/586`.
- Review inputs: `.tmp/review/SNAPSHOT.json`, `.tmp/review/author-568/OWNER-TASK.md`,
  `.tmp/review/author-568/MUSE-REPORT-568.md`, `.tmp/review/author-568/PATCH.diff`,
  `.tmp/review/author-568/BUILD-EVIDENCE.json`, and the exact candidate files under
  `.tmp/review/author-568/grammatik/`.
CANDIDATE: 568 540f620ce41633ea0adf346da8518949ae8e52d1
- The pinned HEAD object itself is not present in this clone (no network fetch
  permitted), so the hash was taken from `SNAPSHOT.json` as authoritative. File-level
  verification: the candidate `AccessExecution.lean` reviewed is byte-identical to the
  file in `.tmp/review/author-568/grammatik/`; `PATCH.diff` touches exactly three paths
  (`MUSE-REPORT-568.md`, `grammatik/Grammatik.lean` additive import only,
  `grammatik/Grammatik/X86/AccessExecution.lean` new); the diff of the candidate
  `Grammatik.lean` against base `8596f83e` is exactly one added import line.

## What the candidate claims

Connect `Zugriffe.zugriff` (potential footprint from the pre-state) to ACTUAL
successful `Ausfuehrung.schritt` / `Byteschritt.byteschritt` for all 14 pilot forms:
realised permission success (§2), realised footprints with frame + exact shape +
stored word / read value from `hstep` alone (§3), a generic 14-form coverage theorem
(§4), alias shapes (§5), a byte-step bridge (§6), refusals (§7), word-vs-atomic
distinction (§8), and a joint witness plus planted refusal (§9).

## Independent reproduction (done by this reviewer)

- Copied the exact candidate file into `grammatik/Grammatik/X86/AccessExecution.lean`
  with the additive umbrella import and ran the queued wrappers on this machine:
  - `./lean-probe grammatik/Grammatik/X86/AccessExecution.lean`:
    `== 0 error(s) in the COMPLETE output; exit 0`.
  - `./lean-bau`: `Build completed successfully (430 jobs).`
    (428 at candidate time; +2 from unrelated modules landed since the base.)
  - All 26 `#print axioms` lines: standard goal set only
    (`propext`, `Classical.choice`, `Quot.sound`, or subsets; one theorem axiom-free).
  - No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` (grep hits are only the English
    words "admits"/"admitted" in comments).
- Temporary reproduction files were fully reverted afterwards; this branch owns only
  this report. `git status` is clean except this file.

## Semantic checks (all major statements inspected, not just the build)

- Real execution, not a computed list: every footprint fact threads through an
  `istRealisiert`/`byteRealisiert` premise. The §2 `gefunden` lemmas derive checked
  read/write success by contradicting the `*_verweigert` lemmas against `hstep`;
  nothing assumes permissions. The `hok : laengeOk = true` premise is redundant
  (derivable from `hstep` via `realisiert_laenge_ok`) but harmless, not a hidden
  correctness assumption.
- Producer lemmas are genuine: verified in `Zugriffe.lean` that
  `erfolg_store64_im_fuss`, `zugriff_load64_liest`, `zugriff_pop64_liest`,
  `zugriff_ret_liest`, `schritt_pop64_speicher` etc. really conclude frame/shape/read
  facts from successful steps. All other referenced names
  (`schritt_*_verweigert/berechtigungen/erfolg`, `zugriff_*`, `fetchDekodiert_entspricht`,
  `byteschritt_weiter`, `zugriff_laenge_versagt_kein_erfolg`, `kein_atomarer_zugriff`,
  `zeugeZustand`, `zeugeReg`, `stumpfStart`, `praefix_abgeschnitten_verweigert`,
  `zugriff_store64_acht`, `stapelOben`, `dispWort`, `ripNach`, `AtomarZugriff`)
  resolve to existing modules. No duplicated evaluator/decoder/ISA/memory model.
- 14-form coverage confirmed by case analysis in `realisiert_fuss_abdeckung`:
  movImm64, movReg64, addReg64, subReg64, xorReg64, cmpReg64, load64, store64,
  jump32, jumpIf32, push64, pop64 (both `dst = rsp` inline branch and non-`rsp`),
  call32, ret.
- Required shapes present: base-is-source alias, `push rsp` old-top store, CALL
  next-RIP stored word evaluated pre-state, POP/RET reads off the old top.
  Invalid length / failed fetch yield no realised trace (refusal lemmas, not vacuous:
  the positive witness shows the premises are jointly inhabitable).
- No forged decoded input: `byte_realisiert_fuss` existentially binds the fetched
  instruction; `byte_realisiert_aus_bytes` requires `fetchDekodiert s = some (d, rest)`.
- No unproved atomic grouping, no guessed ISA/FP faults, no contract-duty weakening,
  no source-width claims: the eight-byte word vs. one TSO event is distinguished by
  construction and the W/GX mapping is left explicitly OPEN in CUTS.
- Joint witness is non-degenerate: `realisiert_fuss_abdeckung_zeuge` instantiates all
  generic-coverage premises on a real reached store step that observably changes byte
  8192 from 0 to 42 (`schritt_zeuge_speicher` by `decide`, reproduced green);
  `byte_zeuge_verweigert` is a planted byte-level refusal. CUTS block is exact and
  honest (including the `pop rsp` destination-value limitation, which matches the code).
- Forbidden paths untouched: no Spec/goal/checker/emitter changes, no friend
  optimiser files, no source widths invented. `Grammatik.lean` change is one additive
  import line (merge note: take the union with the `DecoderSoundness`/`BudgetExecution`
  lines landed since the candidate base).

## Accepted bounded claim

`Zugriffe.zugriff` footprints hold of ACTUAL successful pilot `schritt`/`byteschritt`
executions per the §2–§7 theorems, over all 14 pilot forms, with a jointly
instantiated memory-changing witness and planted refusals. No source/IR link and no
W/GX per-access mapping is claimed or established. Consumer interface:
`realisiert_fuss_abdeckung`, `byte_realisiert_fuss`, `realisiert_fuss_abdeckung_zeuge`,
`realisiert_versagt_laenge`, `byte_ohne_fetch_kein_realisiert`.

## Minimal repairs

None required. Merge note only: union the umbrella import with current master
(`DecoderSoundness`, `BudgetExecution` lines) at integration time.

VERDICT: ACCEPT
