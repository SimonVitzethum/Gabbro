# MUSE-REPORT-738: Precise fault ordering across fetched instruction accesses

## What was done

New module `grammatik/Grammatik/X86/ExceptionPriorityHardware.lean`
(1474 lines) plus the additive umbrella import in `grammatik/Grammatik.lean`.
It closes lane 670's documented gap ("no fault PRIORITY between pending
classes") with a generic ordered-access/fault relation over the actual
fetched-byte producers (`decodeExt` / `fetchExt` / `extByteschritt`,
`read64` / `write64`, `mulDivSchritt`), with architectural priority
fetch < decode < address < access < divide < control and precise
pre-fault observable state. Nothing else in the tree was touched.

## Exact new names

- Stages/order: `FehlerStufe` (abruf/dekodiere/adresse/zugriff/teilung/
  steuerung), `stufenRang`, `rang_kette`.
- Explicit oracles (never inferred): `SeitenInfo` + `seitenKlasse` (+
  `seitenKlasse_nicht_vorhanden`, `seitenKlasse_vorhanden`), `IllegalInfo`,
  `SteuerInfo`, `PrioritaetsFehler`, `ZugriffsBeschreibung`.
- Collectors + exact-behavior theorems: `abrufKandidat` (3),
  `dekodiereKandidat` (4), `adressKandidat` (2, reuses `adrKlasse`),
  `schreibKandidat`/`zugriffKandidat` (3), `teilungsKandidat` (2),
  `steuerKandidat` (2).
- Selection: `kandidatenReihe`, `ersteWahl`, `ersteWahl_reihe`,
  `wahl_fallunterscheidung` (six-way case split),
  `abruf_schlaegt_alles`, `adresse_schlaegt_spaete`,
  `zugriff_schlaegt_teilung_steuerung`, `teilung_schlaegt_steuerung`,
  `dekodiere_schlaegt_spaete`, `steuerung_als_letzte`.
- Producer: `FehlerUrteil`, `bindeUrteil` (+ 5 soundness theorems),
  `halt_kommt_von_teilung` (halt only from the fetched muldiv arm).
- Delivery: `fehlerVektor` (+ 2 vector pins), `urteilRip`,
  `fehlerRipVor`, `vorFehler_beobachtung`, `kein_teilschreiben`
  (proved from `writeBytesN_hit`/`_miss`).
- Boundary (Table 7-2): `GrenzEreignis`, `GrenzEntscheid`,
  `istAusfuehrungsfehler`, `burstAusfuehrung`, `grenzEntscheid` (+ 6
  order theorems incl. `ausfuehrungsfehler_sofort`).
- Witness states/descriptors/oracles: `divFalleBytes/Speicher/Kern/Start`,
  `hellFalleSpeicher/Start`, `konfliktAbrufStart`, `divZ`,
  `dunkelKonfliktZ`, `hellKontrollZ`, `overlapZ`, `illLeer`, `illE9`,
  `pgDunkel`, `pgHell`, `stScharf`, `stStumpf`.
- Probes: `geholt_divFalle`, `decode_divFalle`, `zugelassen_divFalle`,
  `abruf_divFalle_keiner`, `dekodiere_divFalle_keiner`, `falle_divFalle`
  (reuses `fehler_div_null_haelt`), `wahl_divFalle`, `halt_divFalle`
  (reuses `extByteschritt_weiter`, `stepExt_muldiv_halt`),
  `urteil_divFalle`, `kandidat_konflikt_abruf`, `wahl_konflikt_abruf`,
  `hadr_konflikt_adresse`, `zugriff_konflikt_haette_auch`,
  `wahl_konflikt_adresse`, `geholt_hellFalle`, `abruf_hellFalle_keiner`,
  `dekodiere_hellFalle_keiner`, `hadr_hellFalle_keiner`,
  `hlese_hellFalle`, `hzug_hellFalle_keiner`, `hsteuer_hellFalle`,
  `wahl_kontrolle_teilung_gewinnt`,
  `wahl_kontrolle_gewinnt_ohne_teilung`, `geholt_trunk`,
  `decode_trunk`, `wahl_trunk`, `abruf_trunk_keiner`,
  `wahl_trunk_entscheidung`, `wahl_trunk_ud`, `kein_erschlichenes_ud`,
  `hwrite_overlap`, `zugriff_overlap_dunkel`, `zugriff_overlap_hell`,
  `hadr_overlap_keiner`, `wahl_overlap`.
- Joint witness `prioritaet_zeuge_gemeinsam`: the reached two-cell
  store run (cells 8192/8200 from 0 to 42, reusing
  `extWit_zwei_schritte_speichern`/`extWit_anfang_null`) jointly with
  the divide choice, its halt verdict, the address-conflict choice,
  the control choice, and never-inferred #UD. Non-degenerate (two
  memory-changing steps from zeroed cells).

## Last check results

- `./lean-probe grammatik/Grammatik/X86/ExceptionPriorityHardware.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `Build completed successfully (482 jobs)` (whole
  `grammatik/` green including the new module through the umbrella).
- `#print axioms` for all 19 main theorems: `none`, `[propext]`, or
  `[propext, Quot.sound]` only -- subset of the `gabbro_ziel` axioms.
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` (word-boundary
  grep clean). No unproven premises; every theorem premise is used.
- No source-syntax premises are quantified over, so HARD RULES 13's
  source-`_zeuge` trigger does not apply; joint instantiation is
  provided by `prioritaet_zeuge_gemeinsam` anyway.

## What remains open (also in the file's CUTS block)

Within-class silicon order where the manual leaves it
implementation-dependent (decode illegal/overlong/truncated pins and
read-before-write are stated-model rules); overlong-by-decode-success
#GP unreachable through the 15-byte fetch cap; no unmasked #NM/#XM
producer (admitted profile runs masked); no #DB class in `ArchFehler`
(boundary classes 4/7 travel as `GrenzEreignis`); `SeitenInfo` page
presence is a consumer-stated hardware assumption; sequential only, no
TSO/GX bridge; delivery (IDT/handler/error code) stays with lane 672;
no silicon, source, cost or time transfer.

## Notes / possible task objections

- The divide-trap evidence is a caller-supplied `Bool` tied to
  `mulDivSchritt = .hardwareHalt` at each use (same selection pattern
  as the accepted `stepExt_muldiv_halt`), not an assumption: the
  probes discharge it against the actual evaluator.
- Two commits in the branch share one message line by accident
  ("bright-window control probes" for `a2495b63` and the next); the
  latest message was amended message-only to describe its real
  content, history is accurate.
- Manual provenance is the clone-local snapshot
  `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`: Table 7-2
  (~line 164271), canonical addressing (line 4220), DIV/IDIV entries
  (lines 31795/31887), #AC entries (lines 42479/62386), Table 6-1
  vectors (lines 9641-9671). No AMD provenance claimed.
