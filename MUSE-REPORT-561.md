# MUSE-REPORT-561: Relocated bytes to re-decoded instruction execution

## Result

Delivered and green. New module `grammatik/Grammatik/X86/RelocatedExecution.lean`
(1088 lines) plus the additive umbrella import in `grammatik/Grammatik.lean`.
Last `./lean-bau` result line: `== exit 0; 0 error line(s) in the COMPLETE output`
(428 jobs, `Built Grammatik`). No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
every `#print axioms` is within `[propext, Classical.choice, Quot.sound]`.

## What was built

A checked patch-and-redecode correspondence for rel32 branch/call sites that
connects five existing producer modules without redefining any of them
(no second decoder, loader, executor, ISA, IR):

- Site vocabulary over the canonical encoder: `RelocArt` (`sprung`/`ruf`/
  `bedingt`), `relocLen`, `relocBefehl`, `relocBytes`, with `relocBytes_len`
  and `relocBytes_decode` (decoder round-trip reuse).
- Displacement bridge `dispWort_bridge`: execution's `sext`-based `dispWort`
  equals relocation's `rel32Enc64 (dispSigned d)`. Needed two new core-only
  lemmas because `omega` cannot see through `Nat.testBit`:
  `testBit_div_pow`, `bit31_equiv`. Plus `dispVonFit` (every in-range
  displacement is some field's signed value).
- Checked site `PatchSite` (bias, section base, offset, class, displacement,
  intended virtual target) with `siteStart`/`siteNext` and the `patchSiteOk`
  Bool (next-RIP equation, signed-32 fit, 64-bit bounds, interior-target
  refusal): `patchSiteOk_akzeptiert`, `patchSiteOk_disp_aussen`,
  `patchSiteOk_innen`.
- Generic target `patchSite_ziel` (machine-word and Nat): decoded target
  equals intended mapped target, via `rel32_adress_gleichung` through the
  bridge and `rel32_next_rip` over the carried final length.
- Actual-memory execution to the target: `patchSite_sprung_schritt`,
  `patchSite_ruf_schritt` (memory-changing: real `write64` of the return
  address), `patchSite_bedingt_genommen_schritt`,
  `patchSite_bedingt_nicht_schritt` — all via `kanonisch_schritt_ueberein`
  on the fetched window, never on metadata.
- Image layer: `fenster5`/`fenster6` loaded windows, `ladenByte_fenster`
  (one window byte through `geladenByte_datei`), `bildSite_sprung_dekode`,
  `bildSite_ruf_dekode`, `bildSite_bedingt_dekode` (file bytes checked
  against the actual `datei` list, re-decoded independently).
- Explicit class cut: `siteArtOk` with `siteArtOk_code_akzeptiert` and
  `siteArtOk_daten_verweigert` (abs64/data fields never decode here).
- Joint witnesses over accepted images (`wohlgeformt` by `decide` in each
  case): `vor_gelenk` (jump +16, 0x1000 -> 0x1015), `rueck_gelenk`
  (jump -16, 0x1010 -> 0x1005), `versetzt_gelenk` (nonzero bias 0x100000,
  jump -5), `ruf_schritt_zeuge` (call stores 0x1005 at 0x1FF8, reads back,
  byte changes 0x00 -> 0x05, lands on 0x1015), plus planted refusals
  `aussen_verweigert`, `aussen_rel32Fuer`, `innen_verweigert`
  (0x1002 satisfies the next-RIP equation but lies inside the site).

## Producer/consumer interface (stable)

Producers (all reused, none modified): `Relokation` (fit/bytes/round-trip/
address equation/next-RIP), `BranchLayout` (`dispSigned`, codec bridge,
widths), `Bild` (`abteilFinden`/`ladenByte`/`geladen`/`geladenByte_datei`),
`Codec` (`encode`/`decode`/`roundtrip_*`), `Byteschritt`
(`kanonisch_schritt_ueberein`), `Ausfuehrung` (`schritt_*`, `dispWort`,
`ripNach`), `Wort`/`Vektor`/`Speicher`/`ControlFlow` helpers.
Consumer: the future layout validator discharges one rel32 site by
`patchSiteOk` + `patchSite_ziel` + the matching `_schritt` theorem;
`DecodingCoverage`/`ValidatorSkeleton.valX86` get per-site decode facts.
Measurable next integration: feed `fenster5`/`fenster6` windows from a real
emitted image and close one `valX86` site obligation.

## Open / cuts

Per-site final layout only (no multi-site convergence); no loader execution
(`geladen` is the pure mapping); no source correspondence, no TSO/GX bridge,
no concurrency/cost/time; abs64-data, rel8-short and non-branch/call/cond
sites are explicit cuts (see file CUTS). Full CUTS block and per-theorem
`#print axioms` are at the end of the module.

## Notes on the task

Nothing in the task turned out to be wrong. Two apparatus findings, both
worked around (no rule changes needed): (1) `omega` does not reason about
`Nat.testBit` — bridged with `testBit_div_pow`/`bit31_equiv` from core
`Nat.testBit_succ`/`Nat.testBit_zero`; (2) this toolchain's structure
syntax rejects a multi-line `{...}` literal with trailing commas inside a
`[...]` list or after `some` (while the same layout parses after `:=` with
a known type) — worked around with named section definitions; single-line
`{ z with ... }` updates are used throughout.

Owned paths only: `grammatik/Grammatik/X86/RelocatedExecution.lean`,
`grammatik/Grammatik.lean` (one import line), `MUSE-REPORT-561.md`.
