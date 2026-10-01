# MUSE-REPORT-560: Loaded image to actual instruction fetch

Lane 560, branch `muse/560`, clone `/home/simon/Dokumente/gabbro-muse/a560`.
Owned paths only: `grammatik/Grammatik/X86/LoadedExecution.lean` (new),
`grammatik/Grammatik.lean` (one added import line), this report.

## What was done

Connected the checked `Bild` file/virtual mapping and its actual memory
construction (`geladen`, `abteilFinden`, `ladenByte`) to the byte fetch
(`Byteschritt.geholt`, `fetchDekodiert`, `byteschritt`). The checked map is
a premise everywhere; fetched-byte equality and the loaded execution step
are derived conclusions. No private loader or executor was invented; all
names are the actual `Bild`/`Byteschritt` constructions.

Prior art checked first: `DecodingCoverage` already covers decoder length
soundness, fetch corollaries from the decoder side, and an entry-window
(`eintrittFenster`) read of loaded bytes, plus a `schritt`-level store
witness over a loaded image and a fetch witness over a hand-built memory.
The missing link closed here is actual `geholt`/`fetchDekodiert`/
`byteschritt` over `geladen` memory: executable-prefix fetch with the
15-byte cap against the checked section map, with nonzero offset/base/bias,
BSS, and the execute/data-read distinction.

### New definitions

- `bildZustand (bild bias rip reg fl)`: `Zustand` whose memory is exactly
  `geladen bild bias` (no second loader).
- `bildStoreDatei`, `bildStoreCode`, `bildStoreDaten`, `bildStore`:
  accepted store image. File = 3 unmapped pad bytes ++ 7-byte
  `store [rbx], rax` encoding ++ 8 zero data bytes. Code: `dateiOff = 3`,
  `vaddr = 0x1000`, `memLen = 16` (9-byte executable BSS tail),
  `lesbar = false`, executable. Data: `dateiOff = 10`, 8 file + 8 BSS
  bytes, readable/writable, never executable. Bias `0x100000`, entry
  `0x101000`, no relocations.
- `storeReg`, `storeFlags`, `bildStoreStart`: loaded start state
  (`rax = 42`, `rbx = 0x102000`, `rip` at the biased entry).
- `bildStoreMutiert`, `bildStoreStartMutiert`: first executed opcode byte
  forged (`72 -> 74`, REX.X set, non-canonical).
- `bildStoreWx`: code section writable (W^X violation).
- `bildStoreEintrittAussen`: entry outside every section.

### New theorems

Acceptance-premise inversion (checked map as premise):

- `wohlgeformt_groesse`, `wohlgeformt_datei`, `wohlgeformt_wx`,
  `wohlgeformt_ausr`: `wohlgeformt p bild = true` implies the per-section
  size, file-containment, W^X and alignment facts for a member section.

Generic connection:

- `holeFetchAux_kopf`: one executable fetch step takes the head byte.
- `holeFetchAux_geladen`: fetching `n` bytes from loaded memory at an
  interior position yields exactly the mapped file bytes
  (`dateiOff + (k + j)`), under section-relative start, wrap-free window,
  file-backed extent, stable `abteilFinden` lookup and execute permission.
- `geholt_geladen_innen`: state-window (`fetchCap`) corollary.
- `holeFetchAux_geladen_bss`: fetching inside the BSS tail yields defined
  zero bytes.
- `holeFetchAux_lesbar_unabhaengig`, `geholt_lesbar_unabhaengig`,
  `ausfuehrbarN_lesbar_unabhaengig`, `fetchDekodiert_lesbar_unabhaengig`:
  fetch and fetch-and-decode never consult data-read permission.
- `bildZustand_speicher`: loaded state carries `geladen` memory.

Concrete execution and probes (all premises discharged by `decide`):

- `bildStore_wohlgeformt`: image accepted under profile 48.
- `bildStore_datei_vorne`: generic `holeFetchAux_geladen` applied to the
  image (nonzero offset/base/bias).
- `bildStore_fetch_store`: actual fetch decodes to
  `store64 rbx rax 0` with an eight-byte zero rest; code is not
  data-readable, yet fetch succeeds.
- `bildStore_schritt_speichert`: one `byteschritt` moves 42 into the data
  section (zero before): real reached memory-changing execution over
  `geladen` memory.
- `bildStore_bss_geholt`: generic BSS lemma applied (executable BSS byte
  fetches zero).
- `bildStore_mutiert_mapping_bleibt` + `bildStore_mutiert_verweigert`:
  mapping still accepts, execution refuses (decode refusal, not map).
- `bildStore_datenRip_verweigert`: no fetch without execute permission.
- `bildStoreWx_verweigert`: W^X refused by the mapping.
- `bildStore_lochRip_verweigert`: no fetch in the inter-section hole.
- `bildStoreEintrittAussen_verweigert`: outside entry not accepted.
- `bildStore_ausfuehrung_zeuge`: joint witness conjoining acceptance, the
  generic fetch conclusion on the image, the memory-changing step and two
  planted refusals, over a nondegenerate image (writable data section is
  written by a reached step).

## Check results

- `./lean-probe grammatik/Grammatik/X86/LoadedExecution.lean`:
  `0 error(s)`, exit 0.
- `./lean-bau`: `Build completed successfully (428 jobs)`, whole project
  green including the new module.
- `#print axioms`: every main theorem depends only on `[propext]` or
  `[propext, Quot.sound]` (subset of the goal axioms; no `Classical.choice`,
  no `sorry`/`admit`/`axiom`/`native_decide` anywhere in the file).

## Producer/consumer interface and next integration

- Consumes (reused, not duplicated): `Bild.geladen/abteilFinden/
  ladenByte/geladenByte_datei/geladenByte_bss`, `Byteschritt.geholt/
  fetchDekodiert/byteschritt/ausgangRip/ausgangByte`, `Codec.decode`,
  `Ausfuehrung.schritt`, `Speicher.read64/write64` facts.
- Produces for the validator-soundness owner: `geholt_geladen_innen`
  rewrites the actual fetch window of an accepted image to its file bytes,
  so `valX86_sound` work can replace fetch reasoning by file-byte
  reasoning under the already-checked map; `fetchDekodiert_lesbar_
  unabhaengig` removes data-read permission from fetch obligations.
- Measurable next step: apply `geholt_geladen_innen` to a 15-byte
  file-backed executable section (this image has 7 file + BSS bytes, so it
  instantiates the `n = 7` prefix form; the full-window form is proved and
  waiting), then feed the resulting file-byte list into `decode_abdeckung`
  for a map-to-decoder bridge without re-fetching.

## What remains open (also in CUTS)

Source refinement, hardware correspondence, whole-binary control flow,
relocation re-decoding, ABI/cost, concurrency/TSO-GX, and termination are
explicitly not claimed. `verweigert` is absence of transition, never halt.

## Task critique

Nothing in the task was wrong. One scoping note: the full-window
`geholt_geladen_innen` needs 15 file-backed executable bytes, which a
minimal store image does not have; the image therefore demonstrates the
general `n`-prefix form plus BSS continuation, and the full-window form
stands proved for longer programs. No premises were added beyond checked
bounds; no conclusion restates a premise (fetch equalities are computed
from `geladen`, never assumed).
