# MUSE-REPORT-474: Independent exact-candidate review of 426 (round 4)

## Scope
Re-review request received; the NEW SNAPSHOT.json pin is
62388c2df31e8d3372df31e91eaf7354fff2a5c6 — IDENTICAL to the round-3 pin
already reviewed and accepted in commit ab32d4f2. No new author repairs
exist: same 3 files, same sizes (PATCH 504 / report 156 / module 327 lines),
module md5 4865af0eda15213d97cd7f04820472f2 unchanged since round 2. This
round is therefore a confirmation, not a new review: the prior verdict is NOT
stale. Clone verified: /home/simon/Dokumente/gabbro-muse/a474, branch
muse/474. No other clone read.

## Prior rounds (unchanged, retained)
Re-review history: round 1 (5cda4a4f), round 2 (8aeecaf3), round 3
(62388c2d) — each verified fresh at the time. Candidate files inspected from
.tmp/review/author-426/ (SNAPSHOT.json, OWNER-TASK.md, PATCH.diff, supplied
module, BUILD-EVIDENCE.json, 39 evidence entries).

## Candidate (NEW pin)
- HEAD (pinned): 62388c2df31e8d3372df31e91eaf7354fff2a5c6
- Files: unchanged set — MUSE-REPORT-426.md, grammatik/Grammatik.lean (one
  additive trailing import, hunk byte-identical to round 2),
  grammatik/Grammatik/X86/VectorFootprints.lean (new, 327 lines).
- What changed vs 8aeecaf3: REPORT ONLY again. Commit 62388c2d ("report
  gate-repair round 3, module unchanged") appends a "Gate-repair round 3"
  section (report lines 134-156) after a second identical gate failure.
  PATCH delta is exactly +24 lines, all in MUSE-REPORT-426.md; the
  VectorFootprints.lean hunk is byte-consistent with the supplied module file
  (verified by diff), and the theorem inventory is unchanged (same 12
  theorems, same signatures/line numbers as the round-1 full read).
- Nothing else touched: no Zielsatz/Spec, no checker/Rust/emitter, no canonical
  Typen/execution/codec, no friend-owned OptimizationRules/Witnesses. Confirmed
  from PATCH.diff hunk list (3 file headers only).

## Independent reproduction (own clone, NEW pinned files)
- Staged the NEW supplied VectorFootprints.lean in my tree and ran
  `./lean-probe grammatik/Grammatik/X86/VectorFootprints.lean`:
  **0 errors**, all 12 `#print axioms` lines emitted, identical to rounds 1-2
  and to the author's fresh evidence (subsets of [propext, Classical.choice,
  Quot.sound]; `vecFuss_teilueberlapp_verweigert` axiom-free).
- Staged file removed afterwards; tree is clean (only this report owned).
  Round-1 full `./lean-bau` on the clean tree already showed the identical
  environmental failure (`exit 134`, `failed to create thread`, exactly 2
  error lines, zero Lean file errors); the author's gate logs (step 397/398,
  4.5s vs 4.8s fast crashes) are consistent with that. No re-run of the
  multi-minute full build was needed to confirm an unchanged module.
- Forbidden-token scan of the NEW module file: completely clean this round —
  no `sorry`/`native_decide`/`axiom`/`unsafe`/`intro _`/`have _ :=` matches at
  all; imports are exactly the three accepted parents (Vektor, Regionen,
  OverlapRefusal).

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

## Findings (round 4: pin unchanged, confirmation)
Pin identical to round 3 — no new repairs to inspect. Fresh confirmation
this round: module md5 matches round 2, and `./lean-probe` on the staged
pinned file again returns **0 errors** (axiom lines re-emitted, standard
only). Staged file removed; tree clean. All round-1–3 findings stand
unchanged: no defects, no vacuity, no hidden assumptions, no forged evidence,
no over-claim; umbrella `exit 134` remains a pre-existing environmental
failure reproduced on the clean tree; merge gate must rebuild.
No defects. The repair round changed no proof: every round-1/2 finding carries
over unchanged (re-verified against the NEW pinned files, not assumed). New
this round, assessed on its merits:
- The refined diagnosis (9 GB free RAM per `free -g` in evidence, so not plain
  OOM; thread-*spawn* failure) is a reasonable inference from the quoted
  machine data and consistent with the fast 4.5s crash. It changes nothing
  about the candidate: still no Lean file error naming the module in any log.
- The restated blocker (gate cannot pass any lane while the umbrella `lean`
  step cannot spawn threads; diagnose cgroup/pids.max/sandbox machine-side)
  is sound and correctly directed at the coordinator, not at lane content.
- The gate-log excerpts remain coordinator-side artefacts not independently
  inspected, but their quoted signature is identical to locally reproduced
  crashes — no forgery signal.
Process note (not a defect): full `./lean-bau` was never green anywhere during
this review window, including the clean tree — the merge gate must rebuild;
the module itself is self-contained green.

## Bounded claim accepted
Generic 16-byte packed-vector byte footprint/tail/disjointness facts over
accepted vector/byte memory with checked extent and alias admission/refusal,
joint memory-changing witness included; no vector-store atomicity; full native
vector lowering OPEN. Not a compiler-closure claim.

CANDIDATE: 426 62388c2df31e8d3372df31e91eaf7354fff2a5c6
VERDICT: ACCEPT
