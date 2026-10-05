# MUSE-REPORT-1141: ISA-strand families (compact/core/cond) on the coherent machine

Clone: `/home/simon/Dokumente/gabbro-muse/a1141`, branch `muse/1141` (verified:
`.git/HEAD` = `ref: refs/heads/muse/1141`).
Owned files only: `grammatik/Grammatik/X86/HwIsaFamilies.lean` (new, ~1150 lines),
`grammatik/Grammatik.lean` (one appended import line), this report.

## What was done

NEW FILE `grammatik/Grammatik/X86/HwIsaFamilies.lean` plugs the ISA strand
(`ISA.lean` `Instr`/`stepI`, previously imported by NO coherent-machine module)
into `HwMaschine` as a `HwAdapter IsaEreignis`, reusing the accepted definitions
unchanged (nothing copied, nothing redefined):

- §1 Register-path admission classifier `isaNurRegister : Instr → Bool`
  (`false` exactly for the memory-touching forms: pilot load/store/push/pop/
  call/ret, narrow store32, compact disp loads/stores) plus the frame theorem
  `stepI_nurRegister_speicher` and per-family helpers `stepI_pilot_speicher`,
  `stepI_muldiv_speicher`, `stepI_shift_speicher`, `stepI_narrow_speicher`,
  `stepI_cond_speicher`, `stepI_kompakt_speicher` (core/shift via the accepted
  `coreSchritt_speicher`/`shiftSchritt_speicher`; pilot via the accepted
  `schritt_*_speicher` lemmas; muldiv via the accepted `md_*` equations;
  narrow via `stepNarrow_*` + `moveNarrow_memory`; cond via
  `setCCAnwenden_speicher`/`cmovAnwenden_speicher`; compact by unfolding
  `schrittC`). Helper `stepI_muldiv_laenge`.
- §2 The adapter `adapterIsa : HwAdapter IsaEreignis` with events
  `.reg`/`.lade`/`.gibAus`/`.verweigert`; re-embedding `setKernVonZustand`
  (+ `setKernVonZustand_wf/_register/_flags/_rip/_speicher/_puffer`); nine
  selection equations `adapterIsa_reg`, `adapterIsa_reg_verweigert_schritt`,
  `adapterIsa_reg_verweigert_speicher`, `adapterIsa_lade`,
  `adapterIsa_lade_verweigert_wert`, `adapterIsa_lade_verweigert`,
  `adapterIsa_gibAus`, `adapterIsa_gibAus_verweigert`, `adapterIsa_verweigert`.
- §3 Preservation and stepI agreement: `adapterIsa_wf`,
  `adapterIsa_reg_stimmt` (successful register step carries EXACTLY the
  `stepI` successor's register file, flags, RIP over shared memory and
  buffers), `adapterIsa_gibAus_kein_speicher` (no SC word effect
  substituted, via accepted `issue_kein_speicher`).
- §4 stepExt agreement on all six shared families (14 theorems):
  `isa_stepExt_pilot(_verweigert)`, `isa_stepExt_narrow(_verweigert)`,
  `isa_stepExt_muldiv_ok/_halt/_misslungen/_verweigert_oder_halt`
  (halt/refusal trichotomy), `isa_stepExt_shift(_verweigert)`,
  `isa_stepExt_setcc(_verweigert)`, `isa_stepExt_cmov(_verweigert)` — each a
  direct application of the accepted `stepExt_*` selection lemmas.
- §5 Planted refusals: `adapterIsa_schlechte_laenge` (concrete, length 0),
  `adapterIsa_falle_verweigert` + `adapterIsa_falle_kein_nachfolger`
  (divide trap, via `stepI` and via `stepIE`), 
...[truncated 3885 chars]