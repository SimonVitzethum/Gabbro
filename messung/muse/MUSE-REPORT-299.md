# Muse Report 299: Independent review of candidate 283

Model: opencode-go/muse-spark-1.3-contributor. No delegation, no other files.
Scope: review ONLY of the exact snapshot in `.tmp/review/` pinned by
`SNAPSHOT.json` (author 283, HEAD `04ee2ef6f2afabd9899753447d01d4e53a2b71d0`,
base `dd02d9120be5540dc3773affcc4c647c4bae940b`, clean). No code or central
file edits; this report is the only owned file.

## What was reviewed

- `.tmp/review/author-283/grammatik/Grammatik/X86/Bild.lean` (578 lines)
- `.tmp/review/author-283/grammatik/Grammatik.lean` (umbrella import only)
- `.tmp/review/author-283/MUSE-REPORT-283.md`, `OWNER-TASK.md`,
  `BUILD-EVIDENCE.json`, `PATCH.diff` (675 lines)
- Existing in-tree sources `grammatik/Grammatik/X86/Speicher.lean`,
  `dokumente/x86/IMAGE-ABI.md` (contract the lane builds against)

## Snapshot integrity

- `PATCH.diff` contains exactly 3 file diffs
  (`MUSE-REPORT-283.md`, `grammatik/Grammatik.lean`, `Bild.lean`),
  matching the `SNAPSHOT.json` file list. No Typen/Spec/Rust/number changes.
- The `Bild.lean` body extracted from `PATCH.diff` is byte-identical to the
  copied `Bild.lean` except a trailing newline: the reviewed copy is the
  committed content.
- `Grammatik.lean` diff is one additive line at end of file:
  `import Grammatik.X86.Bild`. No existing theorem touched.

## Claim-by-claim cross-check (every report claim verified in code)

- Representation: `Profil` (exactly `p48`/`p57`), `Abschnitt`
  (fileOff/fileLen, vaddr/memLen, r/w/x, declared `ausr`), `RelArt`
  (`codeOperand`/`datenFeld`), `RelStatus`
  (`aufgeloest`/`offen`/`verweigert`), `Relok`, `Modus` (`fest`/`param`),
  `Bild` (file bytes, sections, relocs, entries, mode). All present.
- `wohlgeformt` decides every owner-task check: `groesseOk`
  (filesz<=memsz), `dateiOk` (file containment), `virtuellOk`
  (bias+vaddr+memLen<=2^64), whole-interval `kanonischBereich`,
  `ausrOk` (nonzero, divides biased base), `wxOk` (W^X), `paarweise`
  disjointness in BOTH file and virtual space, `eintragEnthalten`,
  `relokOk`, `modusOk` (param base 4096-aligned). File offsets reach
  virtual addresses only via `virtReich`/the `ladenByte` mapping; no
  offset-equals-vaddr equation exists.
- `geladen : Bild -> Nat -> Speicher` builds loaded memory over the shared
  `Speicher` vocabulary. Reused `Speicher.lean` names
  (`lesbar8`, `schreibbar8`, `read64`, `write64`, `writeBytes`,
  `writeBytesN`, `writeBytesN_hit`, `read64_nach_write64`, `addrOff_null`)
  all verified present in the in-tree `Speicher.lean`.
- Generic theorems use every premise (`simp` with `hfind` plus the bound
  hypothesis in each case): `geladenByte_datei`, `geladenByte_bss`,
  three permission-agreement facts, `ausserhalb_rahmen` conjunction.
  No conclusion restates a premise; no `forall`-over-contract-values;
  nothing called a semantics; no `intro _` / `have _ :=`.
- Probes are real: 48/57 boundary facts by `decide` (low-top, high-bottom,
  hole refusal, 57-wider-than-48); accepted two-section witness
  (`zeugenBild_wohlgeformt` by `decide`, code 0x1000 + data 0x2000, byte 9
  at file offset 4); find probes for data base and inter-section hole;
  nonzero mapped byte through the GENERIC equality (`zeugenByte_geladen`
  rewrites with `geladenByte_datei`, not a restated literal); BSS accept
  plus zero through the generic BSS fact; param-base accept plus mapping
  through the generic fact with biased entry `0x101000`.
- Four refusal witnesses proved `= false` by `decide`: overlap, wrap,
  outside entry, unresolved reloc. Isolation checked: overlap (only file
  disjointness fails), outside entry and open reloc are cleanly isolated;
  the wrap shape additionally fails alignment/canonicality (see observation
  O1) but genuinely wraps and is refused.
- Memory-changing witness `schreibLese_zeuge` is genuine: byte at loaded
  `0x2000` proved `= 9`, `write64 ... 42` succeeds via `zeugenSchreibbar8`,
  reads back `42` via `read64_nach_write64`, and `m.bytes != m'.bytes`
  via `writeBytesN_hit` + `addrOff_null` with `decide` closing `9 != 42`.
- Boundaries honestly kept: no source correspondence, no decoder/encoding/
  boundary claim, no relocation correspondence beyond containment/class/
  target, no loader contract, no concurrency/hardware claim. CUTS block in
  file matches the report's OPEN list. Alignment is the declared `ausr`,
  stated as such, not a proved 4096 demand.
- Hard rules: no `sorry`/`admit`/`axiom` command/`native_decide`/`unsafe`
  (mechanical scan clean; only hits are the English word "admits" in two
  doc comments and `#print axioms` lines); no `Prop`-typed premise;
  English only; CUTS plus `#print axioms` for all 26 theorems present;
  INHABITATION rule needs no `_zeuge` (no premise quantifies over program
  syntax, no `ZEUGE:` line in the owner task) and the owner-task probe
  requirement (boundary + memory probes) is met with non-degenerate
  writable content.

## Independent build evidence (this lane, queued wrapper only)

- `./lean-probe .tmp/review/author-283/grammatik/Grammatik/X86/Bild.lean`
  (imports resolve via the built project oleans):
  `== 0 error(s) in the COMPLETE output`.
- Full `#print axioms` output reproduced: `[]` for boundary/find facts,
  `[propext]` for mapping/permission/witness theorems,
  `[propext, Quot.sound]` for `schreibLese_zeuge` only — each a subset of
  the goal's `propext, Classical.choice, Quot.sound`, exactly as reported.
  (Author's `BUILD-EVIDENCE.json` shows the same list plus exit-0
  `./lean-bau` at 369 jobs; no gratuitous full rebuild run here since the
  file is not in this clone's tree and probe evidence is complete.)

## Observations (follow-ups, NOT defects, NOT blocking)

- O1: `bildUmbruch` is refused for wrap AND misalignment AND
  non-canonicality jointly (`vaddr = 2^64-4`, `ausr = 4096`). A future
  witness with `ausr = 1` would isolate the wrap leg. The claim "wrap is
  refused" stays true.
- O2: the `aufgeloest` (resolved) relocation path has no positive witness;
  all accepted images carry `reloks := []`. `relokOk`'s resolved branch is
  therefore definition-checked only. Matches the booked-OPEN relocation
  correspondence; suggest an accepted resolved-reloc witness in wave B.
- O3: `Modus.param` carries one given base with checked side conditions,
  not a universally quantified base as IMAGE-ABI Mode P foresees. The
  owner task asks only for bias modes with side conditions, which is what
  is delivered and claimed; universal quantification stays wave-B work.
- O4: `relokOk` hardcodes data-field sites to non-executable sections.
  Safe (refusal) direction, stricter than IMAGE-ABI's kind-declared
  section kinds (e.g. constant pools in text). Fine for this bounded
  component; wave B owns the per-kind section table.

No mandatory owner-task deliverable is missing; no defect reproduced.

CANDIDATE: 283 04ee2ef6f2afabd9899753447d01d4e53a2b71d0
VERDICT: ACCEPT
