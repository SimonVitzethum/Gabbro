# Muse Report 845: Composition closing — relaxation-layout closing

## Task
Close bounded branch relaxation to final-byte revalidation: every narrowed
branch re-decoded, `layoutOk` re-decided after each round. Compose
already-accepted modules into one checked closing step; never re-prove
their internals, never duplicate an interpreter or executor.

## What was done
New file `grammatik/Grammatik/X86/ComposeRelaxLayout.lean` (registered in
`grammatik/Grammatik.lean`), closing this producer/consumer interface:

- Producers reused by name: `BranchLayout` (`zweigOk`, `zweigLaenge`,
  `dispSigned`, `zweigOk_kurz`), `TableLayout` (`layoutOk`, `layoutFuer`,
  `zeugenU`, `ueberlapp_verweigert`, writer facts), `RelocatedExecution`
  (`PatchSite`, `siteStart`/`siteNext`, `patchSiteOk` + acceptance/refusals,
  `relocLen`, `relocBefehl`, `relocBytes` + `relocBytes_decode`,
  `patchSite_ziel`, `patchSite_ruf_schritt`, `siteRuf`/`zustandRuf`,
  `aussen_verweigert`).
- Consumer: the layout validator and the whole-image coverage proof
  (`DecodingCoverage`/`ValidatorSkeleton.valX86`), which discharge one call
  site by `ComposeRelaxLayout_verbindung`.

Definitions: `RelaxStelle` (certificate + carried layout + site class +
field), `relaxArtOk` (class/condition agreement), `patchAusRelax` (site as
zero-bias `PatchSite`), `relaxStelleOk` (certificate AND layout AND class,
re-decided), `relaxRundeOk` (list round), `relaxNarrow` (normalize to the
wide fallback), `relaxZeuge` (concrete call +16 to 0x1015).

Theorems: three `relaxStelleOk_*` projections; `relaxRunde_nil/_glied`;
`relaxNarrow_start/_bytes` (no start ever moves, no byte ever changes);
`relaxStelle_dekode` (every narrowed branch re-decodes through the one
canonical decoder); `relaxNarrow_ok` (accepted stays accepted, so
`layoutOk` is re-decided green after each round; short excluded via reused
`zweigOk_kurz`); `ComposeRelaxLayout_verbindung` (TARGET, call sites:
certificate + layout + class + site admission + carried-length agreement
+ decode + executed-target equation + reached `byteschritt` call step over
actual loaded bytes with real return-address store + read-back — every one
of the 16 premises is used); four planted refusals (short, out-of-range,
interior target, overlap); `ComposeRelaxLayout_verbindung_zeuge`
(companion: all premises jointly on concrete values — accepted call site,
loaded call image, nondegenerate writer unit `konto`/`setze` — with
re-decoded bytes, reached memory-changing step zero-to-0x1005, read-back,
observably changed byte, and the planted out-of-range refusal).

## Verification
- `./lean-probe grammatik/Grammatik/X86/ComposeRelaxLayout.lean`: 0 errors.
- `./lean-bau`: exit 0, 0 error lines, 509 jobs, build completed
  successfully. Whole project green.
- `#print axioms`: every theorem depends only on subsets of
  `[propext, Classical.choice, Quot.sound]` (standard `gabbro_ziel` set).
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; no Prop-typed
  premises; no source/checker/Spec/goal/emitter edits; no new
  diagnostic/gift/example/CLI numbers; no MARKE_EMIT changes; friend
  optimiser files untouched.

## What remains open (explicit CUTS in the file)
Short-branch acceptance (refused by the round check; stays with
`Rel8Reach`); whole-image convergence/coverage (stays with
`ValidatorSkeleton`); conditional-branch and data-field sites (stay with
`RelocatedExecution`); source correspondence, TSO/GX bridge, concurrency,
cost/time, ABI/loader/entry, hardware correspondence.

## Notes on the task itself
Two notation pitfalls cost iterations and may help other lanes: nested
`{ field := value }` structure creation inside a `def` failed to parse
here (anonymous `⟨⟩` constructors worked), and a function application
split across lines inside `{ s with ... }` failed to parse (the accepted
files keep that record on one line). Nothing in the task statement turned
out to be wrong; the wide-fallback reading of "narrowed branch
re-decoded" (short stays refused, the carried wide bytes re-decode) is
documented in the file header.
