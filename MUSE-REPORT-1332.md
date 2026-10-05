# MUSE-REPORT-1332: Exact review of candidate 1331 (ValidatorKapLength)

Lane 1332, report-only exact review. Clone `/home/simon/Dokumente/gabbro-muse/a1332`,
branch `muse/1332` (verified). Candidate 1331, pinned HEAD
`f1f508185e471d45ed03e525cab1afdb8e5201d8` (from `.tmp/review/SNAPSHOT.json`;
hash itself never inspected per HARD RULE 1 -- review is over the delivered FILES only:
`PATCH.diff`, `OWNER-TASK.md`, `BUILD-EVIDENCE.json`, copied sources).

## VERDICT: REPAIR

The candidate is green and its theorems are true, but two points need bounded repair
before integration (concrete items R1/R2 below). This is not a rejection of the approach:
the VEX-prefix core (§2-§3) and the per-sub-arm progress wrappers (§4) are solid and should
be kept as-is.

## What I checked (independent)

- `./lean-probe .tmp/review/author-1331/grammatik/Grammatik/X86/ValidatorKapLength.lean`
  (candidate file probed unmodified against my clone's accepted modules):
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau` on my clean tree (candidate not applied; OWN ONLY report):
  `== exit 0; 0 error line(s) in the COMPLETE output`, `Build completed successfully (692 jobs).`
- `#print axioms` (reproduced by my probe): every theorem depends only on subsets of
  `propext` / `Classical.choice` / `Quot.sound`; no `sorryAx`. Most `decide`/`rfl` facts
  on no axioms at all.
- Forbidden tokens: grep over the candidate file for `\bsorry\b|\badmit\b|`
  `\bnative_decide\b|\bunsafe\b|^axiom ` finds nothing (the only `admit`/`axiom`
  substrings are the English word "admits" and `#print axioms` lines). No `split_ifs`,
  no `intro _`, no `have _ :=` discards.
- Existing files: PATCH touches only `grammatik/Grammatik.lean` (+1 import line) plus the
  NEW file and the report. No existing theorem edited, weakened, or deleted.
- Premise use: read every proof. `avxPrefix_genau` / `avxPrefix_verbraucht` drive their
  four-way splits off the hypothesis and consume it in each branch; `kapDecodePrefix_genau`
  rewrites all seven `none` hypotheses and feeds `h8` into `avxPrefix_genau`; every §4
  wrapper feeds its hypothesis into exactly one accepted length lemma (`have`-bound
  equations are consumed by the closing `omega`); `kapDeckt_schritt_verbraucht` uses
  `hdec` for the step rewrite, `hprog` for `if_pos`, and both for the arithmetic.
- Lift-not-copy: `kapDecodePrefix` mirrors accepted `kapDecode` arm-for-arm with only the
  VEX arm changed; `dekodiereAvx2Prefix` is the task-mandated NEW prefix function. The four
  pinned rows are byte-identical to accepted `dekodiereAvx2` (checked against
  `Avx2Join.lean` lines 123-132: same bytes, same ops, same lengths 5/5/6/6), and
  `avxPrefix_genau` proves exact-list agreement. No accepted evaluator redefined.
- Planted refusals really refuse: `avxPrefix_vex128_verweigert`,
  `avxPrefix_fremd_verweigert`, `kapZeilenLaenge_lockAdr_verweigert` are closed
  `decide`/`rfl` evaluations -- my green probe means they evaluate as claimed.
- Witness: `kapVerbraucht_zeuge` covers all eight chain arms with strictly positive
  measured lengths over the accepted non-empty `kapW_*` byte witnesses. Rule 13 needs no
  `_zeuge` (no premise quantifies over program syntax); the joint witness is provided
  anyway. The "two cores / memory-changing step" criterion is not relevant here: this lane
  is decoder-level (byte lists), involves no `HwSchritt`, and claims none.
- Silicon/vendor neutrality: no new hardware fact stated; rows restate accepted pins;
  CUTS disclaims silicon re-check and W/GX. Clean.

## Repair items (concrete, bounded)

- R1 (§7 `kapUeber_laenge_*` are vacuous as "chain-side" evidence). `kapVerbraucht bs [] =
  bs.length` holds BY DEFINITION for any `bs` (`kapVerbraucht_voll`), so the four theorems
  prove list-length arithmetic without running any decoder. The §7 header claim -- "each
  overlap row below is consumed whole (empty rest) by the chain with the stated length" --
  is therefore not established by these theorems, and the task's overlap clause ("a row
  whose consumed length differs between two decoders of an overlap is a FINDING") is
  unaddressed: no two decoders' consumptions are ever compared. Genuine chain facts are
  within reach (e.g. `pin_ext_wdmul64` shows `decodeExt` decides `[73,247,224]`), so this is
  left work, not obstruction. Fix EITHER (a) run the real chain on each overlap row
  (`kapDecode <row> = some (<winning row>, <rest>)` by `decide`, then measured length =
  stated length), which would also discharge chain progress for those rows; OR (b) restate
  §7 as byte-length pins of the overlap rows with no "consumed by the chain" language and
  move conflict-exhibition to CUTS-open. Until then, "no chain-side conflict exhibited"
  overclaims what was measured.
- R2 (CUTS omits two gaps a follow-up reader needs). (i) There is NO progress wrapper for
  the top-level breit arm: `kapFortschritt_breit_wd` covers `decodeWd`, a sub-decoder the
  chain never calls directly, while `decodeMulDivWidth`/`decodeExt` (the actual first chain
  arm) have no accepted arbitrary-input length lemma (verified by grep over `grammatik/`)
  and no wrapper. CUTS lists the open arms but never names this one, so a reader can
  mistake `breit_wd` for chain-arm progress. (ii) Declared-vs-measured agreement
  (`kapZeilenLaenge` vs `kapVerbraucht`) is proved for NO arm -- e.g. the avx2 case would
  follow directly from `avxPrefix_verbraucht`. Both need explicit CUTS lines (proof work
  only where the author chooses (a) in R1).

## What remains open (unchanged, already honest in CUTS)

Arbitrary-input progress for s32/MXCSR/LOCK/lockAdr/FP/vector arms; chain-level mid-section
VEX (seven earlier arms' refusal of VEX-led lists with trailing bytes unmeasured);
cross-decoder comparison; no silicon/W-GX/source/checker/contract/entry/ABI/loader/budget
claim. The author correctly notes the MECHANISM paragraph (`HwAdapter`) is boilerplate
conflicting with the specific TASK; the specific task was implemented.

## Note on the lane file

Nothing in the task text is wrong; the TARGET-equivalent deliverables (consumed length,
progress, coverage advance, VEX prefix, refusal of unfixed rows) are well-posed. The gap
is between the delivered §7/CUTS text and the proofs, fixed by R1/R2 above.
