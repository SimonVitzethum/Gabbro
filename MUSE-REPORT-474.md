# MUSE-REPORT-474: Independent exact-candidate review of 426 (round 2)

## Scope
Re-review of candidate 426 (VectorFootprints) per the NEW SNAPSHOT.json pin.
The previous verdict (on 5cda4a4f) is stale after author repairs; this report
supersedes it. Clone verified: /home/simon/Dokumente/gabbro-muse/a474, branch
muse/474. No other clone read. Candidate files inspected from
.tmp/review/author-426/ (SNAPSHOT.json, OWNER-TASK.md, PATCH.diff, supplied
module, BUILD-EVIDENCE.json, now 35 evidence entries).

## Candidate (NEW pin)
- HEAD (pinned): 8aeecaf30ee3d0b0c4336dcd10f424eb87e7909e
- Files: unchanged set — MUSE-REPORT-426.md, grammatik/Grammatik.lean (one
  additive trailing import), grammatik/Grammatik/X86/VectorFootprints.lean
  (new, 327 lines).
- What changed vs the stale commit 5cda4a4f: REPORT ONLY. Commit 8aeecaf3
  ("report gate-repair analysis, module unchanged") appends a "Gate-repair
  round" section (report lines 96-132) after the integration gate FAILED on
  the same umbrella thread-creation crash. PATCH.delta is exactly +38 lines,
  all in MUSE-REPORT-426.md; the VectorFootprints.lean hunk is byte-consistent
  with the supplied module file (verified by diff), and the umbrella-import
  hunk is unchanged.
- Nothing else touched: no Zielsatz/Spec, no checker/Rust/emitter, no canonical
  Typen/execution/codec, no friend-owned OptimizationRules/Witnesses. Confirmed
  from PATCH.diff hunk list (3 file headers only).

## Independent reproduction (own clone, NEW pinned files)
- Staged the NEW supplied VectorFootprints.lean in my tree and ran
  `./lean-probe grammatik/Grammatik/X86/VectorFootprints.lean`:
  **0 errors**, all 12 `#print axioms` lines emitted, identical to round 1 and
  to the author's fresh evidence (subsets of [propext, Classical.choice,
  Quot.sound]; `vecFuss_teilueberlapp_verweigert` axiom-free).
- Staged file removed afterwards; tree is clean (only this report owned).
  Round-1 full `./lean-bau` on the clean tree already showed the identical
  environmental failure (`exit 134`, `failed to create thread`, exactly 2
  error lines, zero Lean file errors); the author's gate log (step 397/398 vs
  local 392/393 — tree file-count drift, same crash signature) is consistent
  with that. No re-run of the multi-minute full build was needed to confirm
  an unchanged module.
- Forbidden-token scan of the NEW module file: no `sorry`/`admit`/`axiom`/
  `native_decide`/`unsafe` (two false-positive substrings in doc comments:
  "admitted", "alias-admitted"); no `intro _` / `have _ :=`; imports are
  exactly the three accepted parents (Vektor, Regionen, OverlapRefusal).

## Semantic checks (against accepted sources in my tree)
- All consumed names resolve to accepted definitions: `vecWrite`/`vecRead`/
  `vecHiAddr`/`OhneUmbruch16`/`vecChunks_disjoint`/`vecZeugenSpeicher`/
  `vecZeugenVektor`/`vecZeugenM1`/`vecZeugenM2`/`vecRead_nach_write` (Vektor.lean),
  `Fuss`/`Disjunkt`/`disjunkt_von_intervallen`/`fuss_laenge`/`addrOff_nat`
  (Speicher.lean), `Region`/`inRegion`/`natAdresse`/`natAdresse_addrs`
  (Regionen.lean), `fussEnthalten`/`fussDisjunktB`/`klassifiziere`/
  `aliasZulassen`/`klassifiziere_disjunkt`/`fussDisjunktB_klingt`
  (OverlapRefusal.lean), `fuss_mem` (Zugriffe.lean). No invented IR/executor.
- `fussDisjunktB_von_Disjunkt` (Prop-to-Bool bridge): proof direction is sound
  (`fuss_mem` decomposition + per-byte `≠` discharged by the `Disjunkt`
  premise). Genuinely new (nothing in Speicher/OverlapRefusal stated it).
- `vecFuss_disjunkt`: all four chunk pairs placed via `vecOhneUmbruch_chunks`
  + `eA`/`eB` address equations; the 16-byte separator `h` is required by each
  `omega` (premise used, not decorative). No-wrap premises `hA`/`hB` both used.
- Extent accept/refusal: `vecFuss_in_traeger` covers both chunks with explicit
  wrap bound; `vecFuss_teilschwanz_verweigert` witnesses the outside byte
  (`c+23`) and routes through the reusable refusal half. Concrete overlap
  refusal at 8192/8200 is arithmetically correct (shared bytes 8200..8207,
  8 bytes; neither equal nor disjoint, so `.unbekannt`) and `decide`-closed.
- Witness `vectorFootprints_zeuge` is JOINT and NON-DEGENERATE: nonzero vector
  (`0x100F...01`), real two-chunk `vecWrite`, read-back, byte-0 change proved
  via hit/miss framing (not asserted), plus carrier admission, tail refusal,
  disjointness and alias admission on the same concrete values.
- No atomicity or lowering claim: CUTS explicitly leaves `vecWrite_teilt`'s
  torn state standing, `simdFreigabe` untouched (`false`), native lowering,
  TSO-tearing, FP lanes, FolgeG/budget/progress all OPEN. No safety weakening.
- Every theorem's premises are used; conclusions are not restatements of
  premises; no contract-quantification games; no fake semantics.

## Findings (round 2)
No defects. The repair round changed no proof: every round-1 finding carries
over unchanged (re-verified against the NEW pinned files, not assumed). The
new report section's gate analysis is accurate as far as independently
checkable: zero Lean file errors + umbrella thread-creation crash matches my
own clean-tree reproduction; the "no proof-level defect to repair" conclusion
and the deliberate no-churn decision are correct — re-proving green theorems
would not move a resource-exhaustion crash. The coordinator-side remedy order
(retry at low load, serialize builds, send back only on a Lean file error
naming the module) is sound. One note: the gate-log excerpt itself was not
independently inspected (coordinator-side artefact), but its quoted signature
is byte-identical to locally reproduced crashes, so no forgery signal.
Process note (not a defect): full `./lean-bau` was never green anywhere during
this review window, including the clean tree — the merge gate must rebuild;
the module itself is self-contained green.

## Bounded claim accepted
Generic 16-byte packed-vector byte footprint/tail/disjointness facts over
accepted vector/byte memory with checked extent and alias admission/refusal,
joint memory-changing witness included; no vector-store atomicity; full native
vector lowering OPEN. Not a compiler-closure claim.

CANDIDATE: 426 8aeecaf30ee3d0b0c4336dcd10f424eb87e7909e
VERDICT: ACCEPT
