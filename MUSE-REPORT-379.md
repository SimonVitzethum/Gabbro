# MUSE-REPORT-379 — Independent exact-candidate B1 review of 341 AccessList

## Scope and method

- Reviewed candidate 341, pinned HEAD `49240df152c4732ed7b0f66bd2b82591b4acddeb`
  (SNAPSHOT.json base `f737a6f04c22dfdd9499532e0535ad119cf2e56d`, clean).
- Inspected `.tmp/review/author-341/` (OWNER-TASK.md, PATCH.diff, AccessList.lean
  snapshot, MUSE-REPORT-341.md, BUILD-EVIDENCE.json) against the accepted source
  models in this clone (`RennfreiVoll.lean`, `RennfreiG.lean`,
  `Speichermodell/RMW.lean`, `Speichermodell/MaschineW.lean`,
  `TravAwaitsLauf.lean`, `ZielOrt.lean`).
- Staged ONLY the candidate's owned module (`grammatik/Grammatik/X86/AccessList.lean`)
  plus the one additive import at the end of `grammatik/Grammatik.lean` privately,
  probed, built, then fully restored. This report is the only file owned/committed.

## Verification results (measured in this clone, candidate staged)

- `./lean-probe grammatik/Grammatik/X86/AccessList.lean`: **0 errors**
  (first COMPLETE-output line trusted). All 10 `#print axioms` lines depend only
  on subsets of the standard three.
- Full `./lean-bau`: **Build completed successfully (387 jobs)**, whole project green.
- Axiom probe `Gabbro.Grammatik.Zielsatz.gabbro_ziel` with candidate staged:
  `[propext, Classical.choice, Quot.sound]` — unchanged.
- After restore: `git status` clean except this report.
- Banned-token grep over the candidate file: no `sorry`/`admit`/`axiom`/`native_decide`/
  `unsafe`, no `intro _`/`have _ :=`. The only matches are ten required
  `#print axioms` lines and the English word "admission" in a comment.
- Changed files per PATCH.diff: exactly `MUSE-REPORT-341.md`,
  `grammatik/Grammatik.lean` (+1 import line), `grammatik/Grammatik/X86/AccessList.lean`
  (new). No checker/Spec/goal/central/Rust/emitter/docs touched; no refusal tightened.

## What the candidate delivers (checked against source)

Definitions (all `Gabbro.Grammatik.X86`, over the real model):
`TraegerWert`/`traegerWert`, `ZugriffEintrag` (`.liest`/`.schreibt`),
`ZugriffBefund` (`.voll`/`.luecke`), `eintraege`, `accessList`, `IstRMW`, `pruefeBefund`.
Theorems: `eintraege_liest`, `eintraege_schreibt_aufgezeichnet`, `schreibG_voll`,
`zugriffG_voll`, `accessList_kein_luecke`, `accessList_besteht`, `luecke_faellt`,
`exchange_rmw_voll`, `exchange_zwei_liest`, `accessList_ta_zeuge`.

- Semantics check: `eintraege` maps the decided `zugriffe` trace delta
  (`RennfreiG.lean:27`, newest-first trace slice through `zugriffVon`) and reads
  values from endpoint memories. This matches the accepted definitions exactly:
  `LiestG` is `(c,false) in zugriffe` (`RennfreiVoll.lean:522`),
  `SchreibG` is `(c,true) in zugriffe \/ ~TraegerGleich` (`:517`),
  `ZugriffG` is `(exists w, (c,w) in zugriffe) \/ ~TraegerGleich` (`:513`).
  The completeness proofs unfold these definitions; the unrecorded-change
  disjunct is kept explicit, never dropped. No new evaluator, no second IR,
  no renamed-correctness premises. The events carry no values
  (`Ereignis` carries carrier plus write-flag), so endpoint-memory slices are the
  honest source of values; nothing is invented.
- RMW check: `IstRMW := ExchangeKopf` (`MaschineW.lean:127`), and
  `exchange_rmw_voll`/`exchange_zwei_liest` reuse `exchange_liest_schreibt`
  (`RMW.lean:117`) instead of duplicating the rule inversion. No behavioural
  read-plus-write is mislabelled RMW.
- Witness check: `accessList_ta_zeuge` destructures the accepted `taLauf`
  (29-step `taP` run) and proves a recorded read at step 24, a `flag` memory
  change at step 16 (`0 -> 1`), a table write (`tab[0]`, `0 -> 1`, nondegenerate),
  and post-write value `1`. Joint, concrete, memory-changing. Staged build confirms
  the `taLauf` destructure pattern matches the accepted statement in this tree.
- Refusal check: `luecke_faellt` proves `pruefeBefund .luecke = false` concretely.
  The `Bool` is documented as validator admission, never a hardware fault.
- No invented physics: no alignment/width/tearing/TSO/LOCK-latency/float/ABI/cost/
  source-to-bytes claim anywhere; all are OPEN in CUTS. Safety-correction items
  from the owner task are respected, not triggered.
- Bounded claim is truthful: the report and CUTS scope the delivery to ownership,
  generic completeness, the exchange instance and the admission refusal; per-rule
  syntactic classification (~69 rules), the re-derived exchange write entry, the
  concrete two-carrier exchange application, byte/TSO/IR-bridge work stay OPEN.
  The "What I believe is wrong" section correctly flags the plan's
  "Closes: O-access/D-access" as overstated and the value-location mismatch.
- English comments/docs; identifiers follow canonical German model vocabulary
  (`LiestG`, `ZugriffG`, `ExchangeKopf`), consistent with the accepted tree.

## Findings (minor, not verdict-changing)

1. `exchange_rmw_voll` concludes `IstRMW M u g` from premise `hk : ExchangeKopf M u g`
   where `IstRMW` is definitionally `ExchangeKopf` — first conjunct restates a
   premise under another name (HARD RULE 4a-adjacent). Repair direction: drop the
   flag conjunct from the conclusion (keep it as the `IstRMW` definition plus a
   one-line unfold lemma) or document it as the definitional RMW-flag projection.
   The remaining conjuncts carry the real content, all premises stay used.
2. `exchange_zwei_liest` concludes `c /= .inr g`, verbatim premise `hne`
   (HARD RULE 4a). Repair direction: drop the third conjunct; distinctness is
   already carried by the two differently-carriered entries.
3. Witness scope: the task ZEUGE line asks for a concrete multi-access leaf
   (exchange reading two carriers) with a memory-changing run; the concrete run
   delivered is the non-exchange `taP` publish/await run, and the two-carrier
   exchange shape is conditional (`exchange_zwei_liest`). This is honestly CUT,
   not claimed — acceptable as bounded delivery, recorded here so the follow-up
   (concrete exchange application with full rule premises) stays booked.
4. Nit: report says "282 lines"; the file has 280 lines.

## CUTS (of this review)

- Reviewed the pinned PATCH content only, staged and built in this clone; the
  author-clone commit itself was not re-created here (no network/clone access).
- Consumer citation (bridge D-access/L-access-complete, IR LowerMap) remains an
  OPEN interface until those lanes cite `accessList`.
- No TSO bridge, IR map, byte-level, hardware, cost or binary claim was reviewed
  because none is made.

CANDIDATE: 341 49240df152c4732ed7b0f66bd2b82591b4acddeb
VERDICT: ACCEPT
