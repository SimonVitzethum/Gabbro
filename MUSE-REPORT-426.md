# MUSE-REPORT-426: VectorFootprints (continuous Lean proof reserve)

## Task
Create ONLY `grammatik/Grammatik/X86/VectorFootprints.lean` plus one additive
X86 import in the umbrella. Prove generic packed-lane byte
footprint/tail/disjointness facts over the accepted vector/byte memory,
with checked extent and alias constraints. No vector store atomicity or
padding-overread guarantee without evidence. Nonempty memory-changing
witnesses including partial tail refusal; full native vector lowering OPEN.

## What was done
New module `grammatik/Grammatik/X86/VectorFootprints.lean` (327 lines),
imported additively at the end of `grammatik/Grammatik.lean`. It consumes
ONLY accepted vocabulary, invents no IR/executor/machine:
`vecWrite`/`vecRead`/`vecHiAddr`/`OhneUmbruch16`/`vecChunks_disjoint`/`Disjunkt`
(`Vektor.lean`), `Fuss`/`fussDisjunktB`-Bool/`addrOff`/`natAdresse_addrs`
(`Speicher.lean`), `Region`/`inRegion`/`natAdresse` (`Regionen.lean`),
`fussEnthalten`/`klassifiziere`/`aliasZulassen`/`klassifiziere_disjunkt`/
`fussDisjunktB_klingt`/`fuss_mem` (`OverlapRefusal.lean`/`Zugriffe.lean`).

Definitions:
- `vecFuss a : List Adresse := Fuss a ++ Fuss (vecHiAddr a)` — the 16-byte
  footprint as the two ordered canonical chunk footprints (per-byte events,
  not one atomic occurrence).
- `vecTraeger basis : Region` — 16-byte readable/writable, never-executable
  carrier extent.

Theorems (every premise is used; all proved, no sorry/admit/axiom/unsafe):
- `vecFuss_laenge` — 16 per-byte events.
- `vecFuss_mem` — membership is membership in either chunk.
- `fussDisjunktB_von_Disjunkt` — NEW reusable bridge the checker consumes:
  Prop `Disjunkt` decides to a positive `fussDisjunktB` Bool answer
  (nothing in `Speicher`/`OverlapRefusal` stated this direction).
- `vecFuss_chunks_disjunkt` — inner-chunk checker-disjointness under
  `OhneUmbruch16` (via `vecChunks_disjoint`).
- `vecOhneUmbruch_chunks` — `OhneUmbruch16` covers both chunk checks.
- `vecFuss_disjunkt` — two vector footprints checker-disjoint from checked
  16-byte Nat intervals + no-wrap both sides (all four chunk pairs via
  `disjunkt_von_intervallen`).
- `fussEnthalten_verweigert_ausserhalb` — reusable checked-extent refusal
  half: one outside byte refuses containment.
- `vecFuss_in_traeger` — CHECKED EXTENT ACCEPT at the carrier base.
- `vecFuss_teilschwanz_verweigert` — PARTIAL-TAIL REFUSAL: footprint at
  `c+8` against carrier at `c` refused (last tail byte `c+23` witness).
- `vecFuss_alias_zugelassen` — disjoint footprints classify `.disjunkt`
  and pass the conservative policy.
- `vecFuss_teilueberlapp_verweigert` — concrete alias refusal: footprints
  at 8192/8200 share 8 tail bytes, classify `.unbekannt`, refused
  (by `decide`).
- `vectorFootprints_zeuge` — JOINT NON-DEGENERATE WITNESS: nonzero packed
  vector store at address zero through both ordered chunk writes reads back
  (`vecRead_nach_write`), observably changes the byte, footprint admitted
  in its carrier, shifted tail refused, next footprint disjoint and
  alias-admitted — all jointly on concrete values with real
  memory-changing execution.

Axioms (`#print axioms`, one per theorem): standard only — subsets of
`[propext, Classical.choice, Quot.sound]`; the overlap refusal depends on
no axioms at all.

## Verification
- `./lean-probe grammatik/Grammatik/X86/VectorFootprints.lean`: **0 errors**
  repeatedly, including the final 327-line file.
- `./lean-bau` (full project): module itself builds cleanly every run (all
  12 `#print axioms` lines emitted in the lake log); **zero Lean file
  errors** in the complete output (only 2 lines: `Lean exited with code
  134` / `build failed`). The final umbrella target `Grammatik` (step
  392/393, the import-all file) crashes with
  `libc++abi: ... failed to create thread` — a resource/environment
  failure, not an elaboration error.
- Proven environmental, not caused by this lane: with my work stashed
  (skeleton-only tree: one import line + 60-line file) `./lean-bau` fails
  identically (same exit 134, same 2 lines). Retried 5 times across ~40
  minutes; identical each time.
- `gabbro_ziel`: untouched — `git status` shows the ONLY modified/added
  files are `grammatik/Grammatik/X86/VectorFootprints.lean` and the
  one-line umbrella import. No `Zielsatz/Spec`, goal, checker, Rust,
  emitter, or canonical Typen/execution/codec file was touched
  (friend-owned `OptimizationRules.lean`/`OptimizationWitnesses.lean`
  not touched).

## Open / CUTS (also in the file)
Full native vector lowering stays OPEN and `simdFreigabe` stays `false`:
decoder/ABI/image, source correspondence, fault order across lanes,
tearing correspondence against the per-access TSO bridge, FP lanes,
call-log preservation, budget transfer, progress interaction. No vector
store atomicity claimed (`vecWrite_teilt`'s torn state stands).
Umbrella-green `./lean-bau` pending only on the environmental thread
failure; the merge gate should rebuild (module is self-contained green).

## Believed-wrong in the task
Nothing. The task's constraints (owned files, no invented mini-machine,
explicit CUTS, witnesses with memory change + tail refusal) were all
satisfiable; the only blocker met was the machine-level build flake above.
