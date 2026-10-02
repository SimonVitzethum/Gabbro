# MUSE-REPORT-634: Direct-source closure (SourceCodeFrame)

Lane 634, clone `/home/simon/Dokumente/gabbro-muse/a634`, branch `muse/634`.
Owned files only: `grammatik/Grammatik/X86/SourceCodeFrame.lean` (new),
one additive import in `grammatik/Grammatik.lean`, this report.

## What was done

New module `Grammatik.X86.SourceCodeFrame` connects the accepted
SourceMemory570 representation interface (real `execStmt` table writes:
`repOk`, `zahlWort`/`wortZahl`, `RepSlot`, `rep_schritt_bleibt`) with the
accepted ImageStoreFrame602 mapping frame
(`codeFremd_von_abbildung`, fetch/decode/code-byte preservation over real
`write64`) and the loaded-image/decoder/fetch definitions
(`geladen`/`abteilFinden`, `paarweise (virtReich _)`, `geholt`,
`fetchDekodiert`). Foreignness is derived from the checked mapping in
every main result, never assumed; unchanged-memory facts come from the
actual store frames, never from an assumed-unchanged premise.

Definitions/theorems (all in `Gabbro.Grammatik.X86`):

- §1 width-generic foreignness: `CodeFremdN`, `codeFremdN_acht`,
  `codeFremdN_von_intervallen`, `holeFetchAux_nach_fremdN`,
  `ausfuehrbarN_gleich`.
- §2 narrow stores: `geholt_nach_write8_fremd`,
  `fetchDekodiert_nach_write8_fremd`, `geholt_nach_write16_fremd`,
  `fetchDekodiert_nach_write16_fremd`, `geholt_nach_write32_fremd`,
  `fetchDekodiert_nach_write32_fremd`, `unversetzt_byte_bleibt`
  (unaligned 1-byte store at 8196 preserves fetch/decode, changes byte).
- §3 main frame: `quellDaten_schritt_laesst_code` — one represented
  source data-store step (real `execStmt` `assignSlot` + matching target
  `write64`) preserves fetch window, decode outcome and every fetched
  code byte under checked mapping/permission shapes/no-wrap bounds,
  and establishes `RepSlot` with read-back plus both W^X verdicts.
- §4 named refusals: `wx_schreibbar_code_verweigert` (SM-WX, generic),
  `datenende_spanne_verweigert` (SM-SPAN, data end),
  `codeende_spanne_verweigert` (SM-SPAN, code end),
  `schutz_fuss_aussen` (SM-SCHUTZ, guard),
  `umbruch_kein_rahmen` (SM-UMBRUCH, wrap); SM-UEBERLAPP is the generic
  producer `an_rip_nicht_fremd`, cited in the witness.
- §5 joint witness: `quellDaten_schritt_laesst_code_zeuge` — all main
  premises jointly on `witD` (one table the witness function writes),
  reached `execStmt` step moving slot `0 → 42`, real target word write
  at `slotAddr 0x102000 0` moving the byte `0 → 42` on the accepted
  frame image, preserved fetch/decode, and all planted refusals.
  Non-degenerate on both sides.

Axioms: every `#print axioms` is a subset of
`[propext, Classical.choice, Quot.sound]` (main theorem and witness use
exactly the standard triple via the source semantics; narrow/frame
lemmas use `[propext, Quot.sound]` or less). No `sorry`/`admit`/
`axiom`/`native_decide`/`unsafe`.

## Last check results

- `./lean-probe grammatik/Grammatik/X86/SourceCodeFrame.lean`:
  `== 0 error(s) in the COMPLETE output`.
- `./lean-bau`: `Build completed successfully (447 jobs).`
  (includes the new additive umbrella import; no existing file touched
  otherwise).

## What remains open

Full source-to-final-loaded-bytes validation stays OPEN: this file
covers one `assignSlot` shape on one `.int` slot (narrow §2 is
target-only), not whole units; `valX86_sound` and any closing theorem
belong to the consumer (direct statement lowering). No concurrency
(per-access TSO/GX), no silicon, no OS-loader enforcement claims —
all named in CUTS.

## Task remarks

Nothing in the task statement appears wrong. One scoping note: the
task asks for "generic data values/table map/code intervals" — values
(`v : Zahl lo hi`), layout (`base/len/off` via `repOk`) and code/data
intervals (generic sections `sc`/`sd`, bias, `rip`) are all universally
quantified in the main theorem; only the witness fixes them. The
`hsMem : s.speicher = m` premise (target state shares the
representation memory) is the explicit, minimal connection between the
two legs — it states identity of the memory, not an unchanged-memory
conclusion.
