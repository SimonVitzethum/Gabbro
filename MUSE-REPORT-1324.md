# MUSE-REPORT-1324: exact review of candidate 1323 (valX86 decode coverage over the capstone chain)

CANDIDATE: 1323 b8fa5c51b5d5fd0c510bb0ab3f858eda1e7592a4
VERDICT: ACCEPT

## Scope

Report-only independent exact review of author lane 1323 at the pinned
HEAD stated above (base `f92c2649`,
SNAPSHOT.json `clean: true`). Reviewed strictly as delivered files under
`.tmp/review/author-1323/` (SNAPSHOT.json, PATCH.diff, OWNER-TASK.md,
BUILD-EVIDENCE.json, candidate file copy). No `git show/log/diff` on the
pinned hash was used. Own clone verified first:
`/home/simon/Dokumente/gabbro-muse/a1324`, branch `muse/1324`, clean tree.

## What was checked

- Full read of the candidate `ValidatorKapDecoder.lean` (458 lines).
- `rg` scan for `sorry|admit|native_decide|sorryAx|unsafe|^axiom`: only the
  English words "admits"/"admitted" in comments (lines 298, 381, 412, 423).
  Clean.
- Definition inventory: only new wrappers (`KapGrund`, `kapDecktFuel`,
  `kapKetteFuel`, `KapErw`, `kapDecodeErw`, `kapDecktErwFuel`,
  `kapAbschnittDeckt`, `kapBildDeckt`, `valKap`, `kapGrundFuel`) plus
  witnesses. No redefinition or copy of any family decoder; `kapDecode`,
  `kapDecode_nichts`, `kapW_lock`, `kapW_avx2`, all eight level decoders
  and `Bild`/`wohlgeformt`/`Profil` vocabulary are imported and reused.
  `kapStreu_kette` consumes all eight `kapDecode_nichts` premises; names
  and order match `HwKapsteinDecoder.lean` lines 153-161 in this clone.
- Premise use (read every proof): `valKap_deckung`, `valKap_monoton`,
  `kapDecodeErw_kanonisch`, `valKap_wohlgeformt`, `valKap_deckt` all use
  their hypotheses; `kapGrund_klassifiziert` has no hypotheses; the four
  `*_schritt` lemmas are `rfl` over data binders only; all refusal
  lemmas are closed `decide`; `kapStreu_grund` rewrites with
  `kapStreu_kette`; `kapZeuge_gelenk` joins all four parts. No `intro _`,
  no `have _ :=`, no Prop-typed premises, no contract quantification.
  `valKap_wohlgeformt`/`valKap_deckt` project conjunction components of
  the admission Bool: standard admission-characterization pattern, premise
  genuinely used, not a restatement of a premise.
- Byte facts: `pinXadd` is 9 bytes
  (`F0 48 0F C1 85 00 00 00 00` = LOCK XADD [rbp+disp32], rax, as
  documented); `kapW_avx2` is 5 bytes; 9 + 5 = 14 = witness `dateiLen`.
  VEX-last ordering respects the accepted exact-match AVX2 arm (chain
  returns `[]` remainder there). Stray byte `0x06` refused at all eight
  chain levels by closed evaluation. No new silicon fact is stated
  anywhere; vendor-neutral (rule 17) holds.
- PATCH scope: exactly three files; `Grammatik.lean` hunk is one appended
  import line. Nothing else in existing files is touched.
- Axioms per BUILD-EVIDENCE `#print axioms` output: every main theorem
  `[propext]` or `[propext, Quot.sound]` — standard subset, no
  `Classical.choice`, no `sorryAx`.
- CUTS block is honest: `valX86_sound_full` stays OPEN; no source,
  refinement, TSO/GX, concurrency, contract, entry, budget, cost/time,
  FP, or hardware claim. The VEX-tail limitation, the guarded (not
  proved) per-row progress, and the inherited chain priority are all
  disclosed. Claim matches proof.
- Witnesses deliver exactly the owner task's first-paragraph ask: LOCK+VEX
  image covered and admitted (`kapZeuge_gedeckt`, `kapZeuge_valKap`),
  stray byte refused at every level, at admission, and with a named
  reason (`keinDekoder`), plus the joint witness `kapZeuge_gelenk`. No
  `ZEUGE:` lines exist and no premise quantifies over program syntax, so
  no rule-13 `_zeuge` obligation arises.

## Task note (agrees with author)

OWNER-TASK.md's second CONTEXT paragraph and MECHANISM paragraph describe
a different lane shape (family-to-`HwMaschine` connection via `HwAdapter`,
`HwWf` preservation, multi-core memory witness) and contradict the TASK
line, the OWN line, and the first CONTEXT paragraph (coverage check over
`kapDecode` with `valKap_deckung`, monotonicity, LOCK+VEX + stray
witnesses, `valX86_sound_full` OPEN). The author implemented the
self-consistent deliverable. The review checklist's "two cores /
memory-changing step" item belongs to the inapplicable paragraph; for a
decode-coverage check the delivered witnesses are the correct
non-degenerate form (a covered 14-byte two-row image and a refusal
proved at all eight chain levels). Not a defect in either the task's
intent or the candidate.

## Build status

- `./lean-bau` on this pristine clone (candidate not applied; applying it
  would exceed OWN ONLY MUSE-REPORT-1324.md and the copy was refused):
  `Build completed successfully (687 jobs).` Green baseline.
- Candidate build evidence (BUILD-EVIDENCE.json, 16 command/output pairs
  showing real iterative development including repaired intermediate
  failures): final `./lean-probe` on the new file `0 error(s)`,
  `./lean-bau` `Build completed successfully (688 jobs)` (the +1 job is
  the new file), full `#print axioms` listing as above.
- Limitation stated plainly: no independent re-execution of
  `./lean-probe` on the candidate was possible from this lane (copying
  the file into `grammatik/` is outside the owned file set). The ACCEPT
  below rests on complete static verification plus the author's
  step-by-step build evidence; the serial merge gate rebuilds anyway.

## What remains open

Per the candidate CUTS (endorsed): `valX86_sound_full`; VEX exact-match
tail limitation; no per-row consumed-length theorem; no chain-tie facts
beyond `kapDecode`; no silicon re-check; no loader/entry/relocation/
control-flow claim. Nothing else is owed by this lane.

## Verdict (substance unchanged from review)

Candidate 1323 `b8fa5c51b5d5fd0c510bb0ab3f858eda1e7592a4` is accepted as
reviewed: sound coverage check over the accepted capstone chain with
monotonicity, named refusals, and the two required witnesses; no
unsupported premises, no weakened guarantees, no over-claim.
