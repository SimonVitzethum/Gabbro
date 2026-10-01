# MUSE-REPORT-380: Independent exact-candidate B2 review of 342 OverlapRefusal

## Scope and method

Reviewed the exact snapshot in `.tmp/review/author-342/` (SNAPSHOT file
`grammatik/Grammatik/X86/OverlapRefusal.lean`, 415 lines; `PATCH.diff`;
`BUILD-EVIDENCE.json`; `MUSE-REPORT-342.md`) against the actual accepted
source modules in this clone (`grammatik/Grammatik/X86/{Speicher,Zugriffe,
Regionen,Bild,Ausfuehrung}.lean`, `dokumente/x86/TSO-GX-BRUECKE.md`).
Ownership: report only. Staged the candidate module plus the additive
umbrella import privately, reproduced the probes and a full `./lean-bau`,
then restored the tree (`rm` staged file + `git checkout -- grammatik`)
before committing this report. No other clones read, no network calls.

Pinned author commit (from BUILD-EVIDENCE git log):
`7d1fa46b9daf3cec605628d9cffd3166ead15c37`.

## Task-done check

The B2 direction (decided alignment/containment/non-overlap checker over
footprints plus aligned-single-carrier bytes-value agreement; tearing
stays OPEN; witness adjacent-carrier layout with proved disjoint accepted
access and refused spanning access; counterexample-C shape as negative
probe; `unknown-overlap => refuse`) is fully delivered:

1. `addrAusgerichtet`, `fussEnthalten` (reuses canonical `inRegion`),
   `zugriffBasis`, `zugriffOk` over canonical `Zugriffe.Zugriff`.
2. `fussDisjunktB`, `UeberlappAntwort`, `klassifiziere`,
   `aliasZulassen` (only `.disjunkt` admits), soundness link
   `fussDisjunktB_klingt` (Bool answer means set disjointness).
3. `einzelTraeger_wertUeberein` over `wortTraeger`: read-back via
   canonical `read64_nach_write64`, per-byte `wortByte` agreement via
   `writeBytesN_hit`, containment via `fuss_mem` + `ohneUmbruch_addrs`,
   alignment via `hbasis`/`hcel`. Every premise is used somewhere.
4. Adjacent-carrier witness `nachbarBild` (sections at 8184/8192):
   `wohlgeformt`, both `abteilFinden` facts, real-extraction accepts
   (`push`/`store` through canonical `zugriff` on `zeugeZustand`,
   all `by decide` kernel computations over the real definitions),
   disjoint carriers/footprints/classification/admission, two refused
   spanning accesses.
5. `gegenbeispielC_unbekannt` / `gegenbeispielC_verweigert`: 8-byte
   access at misaligned 8196 overlapping two carriers classifies
   `unbekannt` and is refused. Matches `TSO-GX-BRUECKE.md` section 2,
   counterexample C (8-byte store to a misaligned address / access
   overlapping two carriers). Refusals are proved `decide` facts.
6. Joint `_zeuge` witnesses conjoin the real `zeugeProg` reached run
   (`zeuge_speicher_aendert_sich`: byte 8192 observably 0 -> 42),
   non-degenerate with a memory-changing step, plus an explicit
   byte-inequality proof. No empty-run witnesses.

## Rule and safety checks

- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` (word-boundary
  grep clean); no `intro _` / `have _ :=` discards; no `Prop`-typed
  premise (`OhneUmbruch a` is a specific Prop, the project-standard
  pattern). All theorem premises occur in statement or proof.
- No conclusion-as-premise: `klassifiziere_verweigert_unbekannt`
  derives a new `aliasZulassen` Bool fact from the classifier
  equation, an honest policy unfolding, not a restatement.
- No second IR/evaluator: no new semantics, only Bool checkers,
  one `Region` constant, one image constant family. Only the 14
  pilot forms pass through, via the canonical `zugriff` extraction.
- No source admission tightened: PATCH touches exactly 3 paths
  (`MUSE-REPORT-342.md`, additive end-of-file import in
  `grammatik/Grammatik.lean`, new `OverlapRefusal.lean`).
- No invented hardware: header and CUTS state refusal is
  validator/profile admission, actual x86 allows many unaligned
  accesses, tearing/TSO atomicity stays OPEN, same-footprint sharing
  refusal defers to lock/atomic discipline, no source lowering
  claimed, consumer (shared IR 287) pending with no substitute.
- CUTS block present; `#print axioms` for every main theorem.
- English throughout. Bounded claim only.

## Reproduced evidence (this clone)

- `./lean-probe grammatik/Grammatik/X86/OverlapRefusal.lean` (staged):
  0 errors; axiom lines byte-match the author's BUILD-EVIDENCE
  (defs axiom-free; lemmas `propext`, `propext + Quot.sound`, or
  `propext + Classical.choice + Quot.sound` — all standard).
- `./lean-bau` (staged): 386 jobs, build completed successfully.
- Spot-verified against source: `Abschnitt` fields match the
  section literals; `fuss_mem` (`x in Fuss a <-> exists k < 8,
  addrOff a k = x`) matches the `obtain ... rfl` use; `inRegion`,
  `regionDisjunkt`, `natAdresse`, `zeuge*` names all resolve to the
  canonical modules. No symbol-guess mismatch found.

## Findings

No material findings. Two non-blocking notes: (a) the vacuous
`zugriffOk = true` for empty footprints is correct (no memory
involved) and explicitly documented; (b) `zugriffOk_zeuge` reuses
proved conjuncts rather than re-deciding, which is fine since each
conjunct is itself a `decide`d fact on the same layout.

CANDIDATE: 342 7d1fa46b9daf3cec605628d9cffd3166ead15c37
VERDICT: ACCEPT
