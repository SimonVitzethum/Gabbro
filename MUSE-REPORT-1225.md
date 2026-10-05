# MUSE-REPORT-1225: Precise exceptions at the store buffer

Lane 1225, clone `/home/simon/Dokumente/gabbro-muse/a1225`, branch `muse/1225`.

## What was done

NEW FILE `grammatik/Grammatik/X86/HwPreciseFault.lean` (469 lines) plus one
`import Grammatik.X86.HwPreciseFault` line appended to `grammatik/Grammatik.lean`.
Nothing else touched. No existing definition, theorem or model was copied,
redefined or weakened; everything is lifted from the accepted modules
`HardwareExecution`, `HwFaults` (lane 1123) and `HwInterrupts` (lane 1125).

Contents, by section:

- §1 Family event type `PrzEreignis` (`.fehler : PrioritaetsFehler`,
  `.liefere : AsyncEreignis`) and the `HwAdapter` plug `adapterPraezise`:
  faults refuse (no successor BY CONSTRUCTION, the `adapterFehler1123`
  discipline), delivery IS the accepted `asyncSchritt` with the event's own
  control snapshot (`adapterPraezise_liefere_treue`, proved by `rfl`).
- §2 Precise fault, from the accepted `hwFehlerSchritt_fehler_still`
  (a fault step is a self-loop): `przFehler_speicher_still` (memory still),
  `przFehler_puffer_still` (every buffer on every core still),
  `przFehler_eintrag_bleibt` (every older buffered store survives),
  `przFehler_beobachtung_still` (every core view still). The faulting
  instruction has no architectural effect; an older store is either still
  buffered or drained by somebody else -- never by the fault itself.
- §3 Delivery is not a drain (accepted S3, lane 1125): `przFertig_erhaelt`
  (push stage keeps profiles and all buffers) and `przLieferung_erhaelt`
  (full `asyncSchritt` case split over vector/IF/limit/gate-read/check/
  stack/canonical/push, every refusal branch closes, every success branch
  lands in the push-stage lemma), with projections `przLieferung_wf`
  and `przLieferung_puffer_still` (no buffer on any core is drained).
- §4 Agreement, refusals, handler forwarding: `adapterPraezise_wf`,
  `adapterPraezise_maskiert_verweigert` and
  `adapterPraezise_vektor_verweigert` (lifting the accepted
  `asyncSchritt_verweigert_*` lemmas), and `przHandler_weiterleitung`
  (a store buffered on the acting core keeps forwarding to it after
  delivery; the frame push is elsewhere, readability at the cell is an
  explicit premise).
- §5 Joint witness `prz_zeuge`: core 0 issues byte 42 at `hwWitAdr` on the
  accepted `hwWitStart` machine (`przWitM`), core 1 takes the fetch #PF
  (`przWit_wahl` via the accepted priority lift, `przWit_schritt` as a
  reached `HwFehlerSchritt` self-loop). At fault time the store is still
  buffered (`przWit_gepuffert`, length 1), forwarded to the owner
  (`przWit_eigen` = 42) and invisible to core 1 (`przWit_fremd` = 0);
  the drain installs 42 into shared memory observed from both cores
  (`przWit_spuelung`, `przWit_fremd_neu`); the masked-delivery refusal
  (`przWit_maskiert_verweigert`) and the plug fault refusal sit beside it.
  Non-degenerate: the drain changes ACTUAL shared memory while the fault
  fires on the second core.

Axioms: every main theorem depends only on `propext`, plus `Quot.sound`
where `simp` reasoning over the accepted step equations leaks in --
both inside the standard goal set (`propext`, `Classical.choice`,
`Quot.sound`). No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.

## Last check results

- `./lean-probe grammatik/Grammatik/X86/HwPreciseFault.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `Build completed successfully (641 jobs).` (tail line:
  `✔ [640/641] Built Grammatik (3.6s)`).
- Two earlier `./lean-bau` runs failed environmentally, not on proof:
  once `failed to read .../Codec.olean` (the file exists; transient),
  once `failed to create thread`, exit 134 at job 639/641 (resource
  exhaustion; the known virtual-address ceiling failure mode). The retry
  passed unchanged. No proof was modified between the failures and the
  green run.

## What remains open (see CUTS block in the file)

- No hardware verification: classes, vectors and S3 NAME the accepted
  manual entries (Table 6-1, memory-ordering chapter; provenance
  MUSE-REPORT-660/1125). Delivery racing a concurrent drain is not
  modelled (drains are separate steps).
- No fault DELIVERY (IDT path stays with lanes 672/1125/1181), no
  per-access target-to-W/GX simulation, no whole-word atomicity beyond
  the accepted `WortGruppe` guard, no word-level forwarding interaction
  beyond the shared byte equations with lane 1185 (imported in spirit,
  not re-proved: the owner/foreign byte facts here rest on `loadByte`/
  `neuestens`, the same equations lane 1185 builds on).

## Task feedback

Nothing in the task is wrong. One scoping note: the "delivery is not a
drain unless the SDM says so" clause resolves to the accepted S3
assumption lifted to a step theorem -- there is no residual "unless"
branch in the model, because the accepted `asyncSchritt` has no drain
path at all. If silicon ever showed a draining delivery form, it would
be a new accepted evaluator, not a case of this file.

Co-Authored-By: muse-agent-1225 <muse-agent-1225@noreply.invalid>
