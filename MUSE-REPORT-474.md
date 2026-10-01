# MUSE-REPORT-474: Independent exact-candidate review of 426

## Scope
Review of candidate 426 (VectorFootprints) per SNAPSHOT.json pin.
Clone verified: /home/simon/Dokumente/gabbro-muse/a474, branch muse/474.
No other clone read. Candidate files inspected from .tmp/review/author-426/
(SNAPSHOT.json, OWNER-TASK.md, PATCH.diff, supplied module, BUILD-EVIDENCE.json).

## Candidate
- HEAD (pinned): 5cda4a4fb311636a98b8dfb5e5ffab2667c838d4
- Files: MUSE-REPORT-426.md, grammatik/Grammatik.lean (one additive trailing
  import), grammatik/Grammatik/X86/VectorFootprints.lean (new, 327 lines).
- Nothing else touched: no Zielsatz/Spec, no checker/Rust/emitter, no canonical
  Typen/execution/codec, no friend-owned OptimizationRules/Witnesses. Confirmed
  from PATCH.diff file list.

## Independent reproduction (own clone)
- Staged the supplied VectorFootprints.lean in my tree and ran
  `./lean-probe grammatik/Grammatik/X86/VectorFootprints.lean`:
  **0 errors**, all 12 `#print axioms` lines emitted, matching the author's
  evidence exactly (subsets of [propext, Classical.choice, Quot.sound];
  `vecFuss_teilueberlapp_verweigert` axiom-free).
- Removed the staged file (tree clean), ran full `./lean-bau`:
  **identical environmental failure** (`exit 134`, `failed to create thread`,
  exactly 2 error lines, zero Lean file errors) with NO candidate content
  present. The author's "proven environmental" claim reproduces independently;
  the umbrella-red is pre-existing and not caused by 426.
- Forbidden-token scan of the module: no `sorry`/`admit`/`axiom`/`native_decide`/
  `unsafe` (one false-positive substring in a doc comment: "admitted");
  no `intro _` / `have _ :=`; imports are exactly the three accepted parents
  (Vektor, Regionen, OverlapRefusal).

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

## Findings
No defects. No vacuity, no hidden assumptions, no forged evidence (all 12
axiom lines reproduced bit-for-bit in my probe), no duplicated IR, no
over-claim beyond the bounded footprint/extent/alias facts. One process note
(not a defect): full `./lean-bau` was never green anywhere during this review
window, including the clean tree — the merge gate must rebuild; the module
itself is self-contained green.

## Bounded claim accepted
Generic 16-byte packed-vector byte footprint/tail/disjointness facts over
accepted vector/byte memory with checked extent and alias admission/refusal,
joint memory-changing witness included; no vector-store atomicity; full native
vector lowering OPEN. Not a compiler-closure claim.

CANDIDATE: 426 5cda4a4fb311636a98b8dfb5e5ffab2667c838d4
VERDICT: ACCEPT
