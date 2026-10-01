# MUSE-REPORT-578: Independent exact-candidate connection review of 560

Lane 578, branch `muse/578`, clone `/home/simon/Dokumente/gabbro-muse/a578`.
Review of candidate 560, pinned HEAD `d9cc6cc9d115dc48ebc3008ad3ff16af447bc9b6`
(base `8596f83e`, snapshot `clean: true`, verified via FETCH_HEAD from a560).
Owns only this report; final commit is report-only.

## What was checked

- Read the owner task, the candidate file (517 lines,
  `grammatik/Grammatik/X86/LoadedExecution.lean`), the report, the full
  PATCH.diff, and BUILD-EVIDENCE.json.
- Verified every consumed name is real in this tree: `Bild.geladen`,
  `abteilFinden`, `ladenByte`, `geladenByte_datei`, `geladenByte_bss`,
  `wohlgeformt`, `Byteschritt.holeFetchAux`, `geholt`, `fetchDekodiert`,
  `byteschritt`, `ausfuehrbarN`, `ausgangRip`, `ausgangByte`, `fetchCap`
  (15). No private loader or executor; `bildZustand` wraps `geladen` by `rfl`.
- Reproduced independently: staged the exact candidate file plus its one
  import line in this clone (Bild/Byteschritt/DecodingCoverage unchanged
  vs the candidate base; only `Grammatik.lean` gained 9 unrelated import
  lines from other merges) and ran `./lean-probe`: **0 errors, exit 0**,
  all 25 `#print axioms` at `[propext]` or `[propext, Quot.sound]`
  (subset of the goal axioms). Reverted afterwards; tree clean.
- Author's build evidence (incremental probe history with real failures
  fixed, final full `./lean-bau` 428 jobs green) is consistent with this.

## Semantic findings

- Real connection, not decorative: `holeFetchAux_geladen` derives fetched
  bytes = mapped file bytes by induction over actual `geladen` memory with
  the checked map (relative start, wrap-free window, file-backed extent,
  stable `abteilFinden`, execute permission) as premises; the concrete
  `bildStore_datei_vorne` discharges all premises by `decide`, so the
  generic is non-vacuous. BSS and execute/data-read distinction likewise.
- Execution is real: `bildStore_schritt_speichert` runs `byteschritt` (not
  a hand-fed `schritt`) and shows 42 moved into the data section, zero
  before. Joint witness `bildStore_ausfuehrung_zeuge` is nondegenerate
  (writable data section written by a reached step) with two planted
  refusals. Four further negative probes (mutation keeps map / refuses
  decode, data-RIP, W^X, hole-RIP, outside entry) separate map refusal
  from decode refusal correctly.
- No copied premises, no forged input, no guessed ISA (decode facts come
  from `Codec.decode` via `decide`), no contract weakening (no contracts
  involved), no atomicity claims. No `sorry`/`admit`/`axiom`/
  `native_decide` (two grep hits are substrings of "admits" in comments).
  Every premise visibly used; CUTS block honest (source refinement,
  hardware correspondence, relocations, concurrency, termination open).
- Prior-art check: `DecodingCoverage` proves decoder-side coverage and
  entry-window reads but nothing about `geholt`/`fetchDekodiert` over
  `geladen` memory under the checked map. The 560 generic is the missing
  link in that direction, not a duplicate. The concrete image differs from
  `dcEintrittBild`.
- Non-blocking notes: the four inversion lemmas use brittle `.1.1...`
  projection chains over `wohlgeformt`'s `Bool.and` nest (break on any
  reordering of the conjunction; correctness unaffected); the full-window
  `geholt_geladen_innen` (needs 15 file-backed bytes) stands proved but
  uninstantiated on this 7+8-byte image, as the author discloses.

## Bounded accepted claim

Candidate 560 connects the checked `Bild` map to actual fetch: for an
accepted image, the `holeFetchAux`/`geholt` window over `geladen` memory
equals the mapped file bytes (interior `n`-prefix form, BSS zero form),
fetch ignores data-read permission, and one accepted store image executes
a real memory-changing store through `byteschritt`. No source refinement
or hardware correspondence claimed or delivered.

## Verdict inputs (for the merge gate)

CANDIDATE: 560 d9cc6cc9d115dc48ebc3008ad3ff16af447bc9b6

VERDICT: ACCEPT

No repairs required. Suggested follow-up (not a condition): instantiate
`geholt_geladen_innen` on a 15-file-byte executable section and feed the
file-byte list into `decode_abdeckung` for the map-to-decoder bridge.
