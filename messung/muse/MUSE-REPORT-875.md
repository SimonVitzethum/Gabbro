# MUSE-REPORT-875: Optimiser rule: vectorisation gate rule

## What was done

Implemented the DESIGN section 7 "Vectorisation (future)" rule lemma as a
tier-2 gate in the single owned file
`grammatik/Grammatik/X86/OptVectorGate.lean` (new, ~340 lines), plus the
required `import Grammatik.X86.OptVectorGate` line at the end of
`grammatik/Grammatik.lean`. No other file was touched: no diagnostic/gift/
example/CLI numbers, no MARKE_EMIT changes, no source/checker/Spec/goal/
emitter edits, no friend-reserved optimiser files.

## Exact names of new definitions/theorems

Gate and admission:
- `VecGateCert` (fields `spurOk atomOk privatOk schwanzOk`), `vecTorZulassen`
- `vecTorVerweigert_spur`, `vecTorVerweigert_atom`,
  `vecTorVerweigert_geteilt` (the DESIGN failure case: lane-disjoint but
  shared-observable order inversion refuses), `vecTorVerweigert_schwanz`
- `probe_vecTorZulassen_ok`, `probe_vecTorZulassen_geteilt`,
  `probe_vecTorZulassen_atom`

Certificate shape (local rewrite record + recomputed analysis citations,
DESIGN certificate "A+B+C"):
- `VecZertifikat` (fields `tor verfuegbar blockKarte pflichtBindung`),
  `zertifikatOk`, `zertifikatOk_tor`, `zertifikatVerweigert_verfuegbar`
- `probe_zertifikatOk`, `probe_zertifikatOhneKarte`

Lane separation (reuses `Vektor.lean`, never redefined):
- `vektorAdd_zugelassen` (validator-recomputed per-lane equation,
  conditional on admission, lifted to `addB` words)
- `probe_vektorAdd_b64`

Connection and witness (ZEUGE target):
- `OptVectorGate_verbindung` (scalar bind value + `execEnd` outcome +
  width-exact word image + admitted per-lane word equality)
- `OptVectorGate_verbindung_zeuge` (jointly inhabited on `refD`: `3 + 4`
  folds to `7` with two admitted 64-bit lanes, `refEin_schreibt` beside
  the reached memory-changing run `refB_erreicht`/`refB_schreibt`)

## Last `./lean-bau` result line

`Build completed successfully (511 jobs).` — whole project green.
`./lean-probe grammatik/Grammatik/X86/OptVectorGate.lean` reports
`0 error(s)`. `#print axioms` for the main theorems is exactly
`[propext, Classical.choice, Quot.sound]` (standard; helpers are
`[propext]` or axiom-free). `gabbro_ziel` statement files were not
touched, so its axiom triple is unchanged.

## What remains open (see CUTS in the file)

No native vector lowering (decoder/ABI/image, fault order across lanes,
tearing correspondence against the per-access TSO bridge, FP lanes,
budget transfer for packed accesses, progress interaction);
`simdFreigabe` stays `false`. The rewritten window is integer `.int`
binds only; IEEE/downstream float agreement travels through the equal
`execEnd` outcome. No totalCost inequality (level-(c) machine-work bound
OPEN per IR-VALIDIERUNG lane 278). No silicon/TSO/GX correspondence.

## Anything believed wrong in the task

Nothing blocking. One note: the task asks for "IEEE preservation" of a
pure packed-INTEGER rule; since the rewritten window contains no float
node, this is correctly carried by the unchanged `execEnd` outcome over
identical environments rather than by a float rewrite lemma — stated
explicitly in section 4 of the file. The shared-IR (lane 287) interface
is still unaccepted, so both rewrite sides are source `Syntax`/`Semantik`
fragments with the target side cited at lane-value/word level only.
