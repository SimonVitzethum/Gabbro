# MUSE-REPORT-1283: Paging — 4-level page walk, permissions, A/D, #PF error code

Clone `/home/simon/Dokumente/gabbro-muse/a1283`, branch `muse/1283`.
Owned files only: `grammatik/Grammatik/X86/HwPaging.lean` (new, ~1450 lines),
one import line in `grammatik/Grammatik.lean`, this report.

## What was delivered

IA-32e 4-level page translation as a NAMED hardware model, connected to the
coherent `HwMaschine`/`HwSchritt` machine, reusing accepted definitions
unchanged (`istKanonisch`, `adrKlasse`, `seitenKlasse`,
`seitenKlasse_nicht_vorhanden`, `vektor_pf_vierzehn`, `HwWf`, `hwSchritt_wf`,
`HwAdapter`/`verweigertAdapter`, `hwWitStart` family). No existing file was
modified except the one import append.

Definitions: `SeitenEintrag`, `wortBit`, `eintragDekodieren`,
`eintragKodieren`, `SeitenAnfrage`, `SeitenSteuerung` (CR3/WP/SMEP/SMAP/NXE),
`PfFehlerCode`, `pfCodeBits`, `GangErgebnis`
(ok/seitenFehler/gpFehler/grossVerweigert/steuerVerweigert),
`gangIndexPML4/PDPT/PD/PT`, `gangOffset`, `istKanonischNat`,
`blattPruefung`, `gangRechte`, `gangEbenen`, `gangEbenen_kongr`,
`SeitenTabellen`, `seitenTabEintrag`, `wortZugriff`, `wortSchmutzig`,
`tabAD`, `seitenGangTab`, `seitenGang`, `seitenGang_fst`,
`witRahmenTab`, `witRahmenBlatt`, `witEZwischen`, `witBlattRW`,
`witBlattRO`, `witTab`, `witSeitenSteuer`, `FlachStimmt`,
`allWahrSpeicher`, `witFlach`, `gangKlasse`, `adapterSeiten`,
`SeitenZustand`, `SeitenEreignis`, `HwSeitenSchritt`.

Theorems (all green, see axiom list at file end): 8 entry round-trips
(`kodieren_*`); canonical bridge (`kanonischNat_bruecke`,
`gangGp_adrKlasse`); walk rules (`gangEbenen_smep/smap/gp`,
`gangEbenen_nichtvorhanden3/0`, `gangEbenen_gross2/1`,
`gangEbenen_rechte`, `blatt_wp_schuetzt`, `blatt_wp_offen_erlaubt`,
`blatt_benutzer_schreibschutz`, `blatt_abruf_xd`, `blatt_lese_ok`,
`gangEbenen_kongr`); A/D preservation (`wortZugriff_*`,
`wortSchmutzig_*`, `tabAD_unberuehrt_*`, `tabAD_nur_beruehrt`);
walk stillness/determinism (`seitenGangTab_nichtOk`,
`seitenGang_nichtOk_still`, `seitenGang_steuer_gleich`); witness walks
(`wit_lese_rw_ok/ro_ok`, `wit_gleiches_blatt`, `wit_schreibe_rw_ok`,
`wit_schreibe_ro_pf/wp`, `wit_lese_loch_pf`, `wit_nichtkanonisch_gp`,
`wit_zugriff_gesetzt`, `wit_schmutzig_gesetzt`, `wit_unberuehrt_still`);
bridge (`gangOk_flach_schreibbar/lesbar`, `flachStimmt_allwahr`,
`wit_flach_liest/schreibt`, `gangKlasse_pf/gp/steuer_keine/gross_keine`,
`gangPf_seitenKlasse_eins`, `gangPf_vektor`, `wit_code_loch/ro`);
machine link (`adapterSeiten_verweigert`, `hwSeitenSchritt_einbettung_vor`,
`hwSeitenSchritt_alt_invert`, `hwSeitenSchritt_einbettung_zurueck`,
`gangOk_invert`, `gangPf_invert`, `hwSeitenSchritt_fehler_still`,
`hwSeitenSchritt_wf`, `seitenGross/Steuer/Gp_verweigert`); joint witness
`hwSeiten_zeuge` (both mappings onto frame 32, RO-write #PF, owner-only
forwarding, memory-changing drain, flat agreement, two cores).

## Last `./lean-bau` result line

`== exit 0; 0 error line(s) in the COMPLETE output` —
`Build completed successfully (659 jobs).`
`./lean-probe grammatik/Grammatik/X86/HwPaging.lean`:
`== 0 error(s) in the COMPLETE output; exit 0`.
Every `#print axioms` is within `propext`/`Quot.sound` (subset of the goal's
`propext, Classical.choice, Quot.sound`); no `sorry`/`sorryAx`/`admit`/
`axiom`/`native_decide`/`unsafe` in the file.

## Design decisions (all stated in CUTS)

- Large pages (PS at PDPT/PD) are REFUSED (`grossVerweigert`), never mapped.
- SMEP/SMAP-armed configurations are REFUSED wholesale
  (`steuerVerweigert`); CR0.WP IS modelled. No per-access SMEP/SMAP semantics.
- The walk's RW/US/XD protection faults are `#PF` with P=1 (SDM §4.7); the
  accepted `seitenKlasse` `.gp` arm names NON-PAGING protection, so there is
  no contradiction — consensus is proved for non-present (both `.pf`) and
  canonical/#GP.
- `FlachStimmt` for a real OS is user logic; proved: the two bridge
  directions, the all-permissive instance, the witness agreement.
- Tables live outside `HwMaschine`, hence `adapterSeiten` refuses (faults
  have no successor; A/D touches tables, not machine state) and behaviour
  lives in `HwSeitenSchritt` with exact two-way `HwSchritt` embedding.

## What remains open

See the file's CUTS block: no silicon verification of bit positions (the
clone references are the Vol 2 instruction-set extract; no Vol 3A paging
tables were supplied — positions/codes are named assumptions), no large-page
mapping, no per-access SMEP/SMAP, no TLB, no fault delivery, no W/GX bridge,
no timing.

## Task remarks (things believed wrong or risky)

- The MECHANISM paragraph demands a non-degenerate witness with "buffered
  store visible via forwarding to the owner only" — satisfied by reusing the
  accepted `hwWit*` run inside `hwSeiten_zeuge`, not by a paging-native
  buffer (paging has no buffers by design).
- `by_contra` is NOT available in this toolchain (unknown tactic); used
  `by_cases` instead. `rw [h]` does not close `match`-defined classifiers
  (reducible-transparency rfl fails); used `simp [f, h]`.
- `cases` on `HwSeitenSchritt` with a computed target state hits a fatal
  occurs-check (`s` in its own successor tuple); fixed with an explicit
  successor-table variable in the `gang` constructor plus inversion lemmas
  over variable targets.
- Commit `d920d653` carries the skeleton message text but contains piece 2
  (entry encode/decode); the amend was not permitted to this lane
  (`git commit*` denied, only `./commit.sh`). Content per commit:
  `9334681a` skeleton, `d920d653` piece 2, `4b2197b1` piece 3, `28892e32`
  piece 4, `7aead189` piece 5a, `5cf1f5a4` pieces 5b–10, `4484de7e` renames.
- Slot congestion: two `./lean-probe` calls timed out (300 s, 900 s) mid-lane
  with no output while other lanes held the shared Lean slot; no work was
  lost and later probes succeeded.

Co-Authored-By: muse-agent-1283 <muse-agent-1283@noreply.invalid>
