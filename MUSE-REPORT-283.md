# Muse Report 283: Checked byte image and loaded memory

Model: opencode-go/muse-spark-1.3-contributor. No delegation, no other files.

## Owned deliverable

`grammatik/Grammatik/X86/Bild.lean` (new, ~580 lines), plus one additive
umbrella import (`import Grammatik.X86.Bild` at the end of
`grammatik/Grammatik.lean`). Nothing else touched: no Typen/Spec edits,
no Rust, no diagnostic/gift/example/CLI numbers, no MARKE_EMIT.

## What was built

One canonical finite image representation over the shared `Typen`/`Speicher`
vocabulary (reused, not reinvented):

- `Profil` (`p48`/`p57` only; `breite`), `Abschnitt` (fileOff/fileLen,
  vaddr/memLen, r/w/x, declared `ausr`), `RelArt` (`codeOperand`/`datenFeld`),
  `RelStatus` (`aufgeloest`/`offen`/`verweigert`), `Relok`, `Modus`
  (`fest`/`param`), `Bild` (file bytes, sections, relocs, entries, mode).
- Decidable well-formedness `wohlgeformt`: `groesseOk` (filesz<=memsz),
  `dateiOk` (file containment), `virtuellOk` (no wrap under bias),
  `kanonischBereich` (whole interval in low or high half: implies no wrap
  plus per-address canonicality), `ausrOk` (declared alignment divides the
  biased base), `wxOk` (W^X), `paarweise` file/virtual disjointness,
  `eintragEnthalten` (entry in an executable section), `relokOk`
  (resolved, sited, class-vs-kind checked, value target rule), `modusOk`
  (parametric base 4096-aligned). File offsets become virtual addresses
  only through `virtReich`; no loader assertion is trusted.
- Loaded memory `geladen : Bild -> Nat -> Speicher` (bias-indexed) from
  `abteilFinden` + `ladenByte`/`ladenLesbar`/`ladenSchreibbar`/
  `ladenAusfuehrbar`: file-backed bytes map, BSS tail and outside read zero,
  permissions come from the containing section, outside all are false.
- Generic theorems (every premise used): `geladenByte_datei` (mapped-byte
  equality), `geladenByte_bss` (BSS zero), `geladenLesbar_fund`,
  `geladenSchreibbar_fund`, `geladenAusfuehrbar_fund` (permission agreement),
  `ausserhalb_rahmen` (outside-domain frame conjunction).
- Real probes: 48/57 boundary facts (`kanonisch_tief_48`,
  `kanonisch_hoch_48`, `kanonisch_loch_48`,
  `kanonisch_57_weiter_als_48`); accepted two-section witness
  (`zeugenBild_wohlgeformt`, code 0x1000 + data 0x2000 with nonzero byte 9);
  find probes (`zeugenFund_daten`, `zeugenFund_loch`); mapped nonzero byte
  through the generic fact (`zeugenByte_geladen`); BSS image and zero
  (`bildBss_wohlgeformt`, `bildBss_null`); parametric-bias image and mapping
  (`bildParam_wohlgeformt`, `bildParam_byte`, entries are biased addresses).
- Four refusal witnesses: `bildUeberlapp_verweigert` (overlap),
  `bildUmbruch_verweigert` (wrap), `bildEintrittAussen_verweigert`
  (outside entry), `bildRelokOffen_verweigert` (unresolved relocation).
- Memory-changing witness: `zeugenLesbar8`, `zeugenSchreibbar8` (by decide
  over loaded memory) and joint `schreibLese_zeuge`: nonzero `write64` at
  loaded 0x2000 reads back via `read64` and changes byte 9 to 42, reusing
  `read64_nach_write64`/`writeBytesN_hit` from `Speicher.lean`.

## Checks

- `./lean-probe grammatik/Grammatik/X86/Bild.lean`: 0 errors.
- `./lean-bau`: exit 0, 0 error lines, "Build completed successfully
  (369 jobs)". Goal theorem files untouched; no new axioms anywhere:
  `#print axioms` per main theorem is [] / [propext] / [propext, Quot.sound]
  (subset of the goal's propext, Classical.choice, Quot.sound).
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in the new file.

## Open (CUTS)

Decoder/encoding/boundaries, patched-site re-decode and relocation
correspondence, source correspondence, loader contract, concurrency/hardware
claims. `relokOk` is containment/class/target only. Alignment is the
declared `ausr`, not a proved 4096 demand. Only profiles 48/57 exist.

## Task remark

Nothing in the task was found wrong. One interpretation note: the task's
"configurable canonical-address width (48/57 admitted only via explicit
profile)" is implemented as an inductive with exactly two constructors
plus a whole-interval check, which is stronger than endpoint checks (a range
spanning the non-canonical hole is refused even with canonical endpoints).
