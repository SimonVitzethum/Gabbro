# MUSE-REPORT-1332: Exact review of candidate 1331 (ValidatorKapLength)

Lane 1332, report-only exact review. Clone `/home/simon/Dokumente/gabbro-muse/a1332`,
branch `muse/1332` (verified). Candidate 1331, NEW pinned HEAD
`b3de736b6ff1a647eebf51455400966d76bc6c6e` (from the NEW `.tmp/review/SNAPSHOT.json`;
hash itself never inspected per HARD RULE 1 -- review is over the delivered FILES only:
`PATCH.diff`, `OWNER-TASK.md`, `BUILD-EVIDENCE.json`, copied sources).
This supersedes my review of the stale snapshot (`f1f50818`), whose two bounded repair
items R1/R2 the author has now closed; every previous finding was re-inspected below
against the new files. Substantive verdict changed on new evidence, not for formatting.

CANDIDATE: 1331 b3de736b6ff1a647eebf51455400966d76bc6c6e

VERDICT: ACCEPT

## Re-review: R1/R2 closure verified

- R1 (vacuous §7) closed per option (a). The four `kapUeber_laenge_*` are now genuine
  chain-tied triples: first conjunct reuses the accepted chain evaluations VERBATIM --
  `kapUeber_wd_ext_mul64`, `kapUeber_wd_ext_div64`, `kapUeber_wd_ext_imul2`,
  `kapUeber_wd_neu_div32` -- whose statements in my clone's accepted
  `HwKapsteinDecoder.lean` (lines 539-570) match the candidate's claims byte-for-byte
  (same rows, same winning arms, same rests). Measured length = stated length (3/3/4/2)
  and positivity are closed `decide` evaluations. This also discharges chain progress
  for those four rows. The header claim ("run through the REAL chain") is now true.
  Nit (not verdict-relevant): the author's report writes `_neu_div32` once where the
  accepted name -- used correctly in the code -- is `kapUeber_wd_neu_div32`.
- R2 (CUTS gaps + unproved agreement) closed. CUTS now names both gaps explicitly: no
  progress wrapper for the top-level width-dispatcher arm (`breit_wd` covers only the
  `decodeWd` sub-decoder; `decodeMulDivWidth`/`decodeExt` have no accepted
  arbitrary-input lemma), and agreement open only for s32/MXCSR/LOCK/lockAdr/FP/vector/
  top-level-breit. New §8 proves declared-vs-measured agreement for all ten arms with an
  accepted equation (`kapLaenge_stimmt_kompakt/kern/breit_wd/breit_pilot/breit_narrow/
  breit_muldiv/breit_shift/breit_setcc/breit_cmov/prefix_avx2`; each: declared `= some
  stated`, stated `+ rest = input`, measured `= stated`, each reusing exactly one accepted
  equation with the hypothesis consumed). New `#print axioms` lines cover all of them.

## Independent checks on the NEW snapshot

- `./lean-probe .tmp/review/author-1331/grammatik/Grammatik/X86/ValidatorKapLength.lean`
  (candidate file probed unmodified against my clone's accepted modules):
  `== 0 error(s) in the COMPLETE output; exit 0`. All 43 theorems depend only on subsets
  of `propext` / `Classical.choice` / `Quot.sound`; no `sorryAx`. The strengthened
  `kapUeber_laenge_*` sit on `[propext, Quot.sound]`, consistent with real chain reuse.
- `./lean-bau` on my clean tree (candidate not applied; OWN ONLY report):
  `== exit 0; 0 error line(s) in the COMPLETE output`, `Build completed successfully (692 jobs).`
- Forbidden tokens over the new file (`sorry|admit|native_decide|unsafe|^axiom |intro _|
  have _ :=|split_ifs`, word-boundary): no matches.
- PATCH scope: exactly the same three files; `Grammatik.lean` hunk is still the single
  `+import Grammatik.X86.ValidatorKapLength` line. No existing theorem touched.
- Premise use re-verified for all NEW proofs: §7 first conjuncts reuse accepted
  evaluations (closed theorems, no premises needed); §8 hypotheses each feed one accepted
  equation, with the obtained equations consumed by the closing `rfl`/`omega`.
- Earlier findings (§§1-6, refusals, witness, silicon neutrality, premise use) re-read
  against the new file: unchanged and still holding; the §3/§5 limitations remain exactly
  as honestly cut (chain-level mid-section VEX, conditional coverage advance, shadow-side
  comparison open). No claim exceeds its proof now.

## What remains open (all explicitly in CUTS, not claimed)

Arbitrary-input progress/agreement for s32/MXCSR/LOCK/lockAdr/FP/vector arms and the
top-level width dispatcher; chain-level mid-section VEX (seven earlier arms' refusal of
VEX-led lists with trailing bytes unmeasured); shadow-decoder length comparison (a
differing row would be a finding; none recorded). No silicon re-check; no W/GX bridge; no
source/checker/contract/entry/ABI/loader/budget/liveness claim. Vendor-neutral.

## Note on the lane file

Nothing in the task text is wrong. The MECHANISM paragraph (`HwAdapter`) remains generic
boilerplate beside the specific TASK, as the author also notes; the specific task is what
was implemented and reviewed.
