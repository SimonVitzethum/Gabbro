# MUSE-REPORT-1297: Paging follow-up — large pages and SMEP/SMAP

## What was done

New file `grammatik/Grammatik/X86/HwPagingLarge.lean` (plus the one
`import Grammatik.X86.HwPagingLarge` line in `grammatik/Grammatik.lean`),
as a follow-up of lane 1283 (`HwPaging.lean`), whose CUTS refused large
pages (`grossVerweigert`) and armed SMEP/SMAP configurations
(`steuerVerweigert`). This lane maps both and enforces SMEP/SMAP
per access:

- §1 `GrossSteuerung` (accepted `SeitenSteuerung` + EFLAGS.AC),
  decided checks `smepVerletzt` (supervisor fetch from a user page)
  and `smapVerletzt` (supervisor data access to a user page with AC
  clear; fetches and user accesses never fire), with off/user/fetch/AC
  shape lemmas and true/false examples.
- §2 alignment `grossAusgerichtet2M` (frame % 512 = 0) /
  `grossAusgerichtet1G` (frame % (512*512) = 0), 21/30-bit offsets,
  and the shared leaf check `grossBlatt`: SMEP/SMAP gate first, then
  the ACCEPTED `blattPruefung` with the caller offset on success.
  `grossBlatt_ohne_schutz` proves it IS the accepted leaf check with
  disarmed control and the 4 KiB offset (via `blatt_ok_payload`).
- §3 `gangGross2M` (PD with PS maps; PDPT with PS stays refused),
  `gangGross1G` (PDPT with PS maps; PD with PS stays refused),
  dispatcher `gangGross` (PDPT-large through 1G, else 2M). Each EQUALS
  the accepted 4 KiB walk where it applies: `gangGross2M_gleich`
  (needs PD not large), `gangGross1G_gleich` (needs PDPT not large --
  a PD large page refuses on both sides), `gangGross_gleich`,
  `gangGross_bei_1G/2M`.
- §4 fault behaviour: misaligned leaves fault RSVD (2M + 1G), SMEP /
  SMAP violations fault as protection with live access bits,
  `grossBlatt_ac_gleich` (AC set falls through to the accepted leaf),
  pinned error-code values 13 (misaligned user read), 17 (SMEP fetch),
  3 (SMAP write).
- §5 `seitenGangGross`: the accepted lookups, the combined outcome
  (`seitenGangGross_fst`), touched-only write-back through the
  accepted `seitenGangTab` (2 entries for 1 GiB, 3 for 2 MiB, 4
  otherwise), agreement with the accepted walk without large pages
  (`seitenGangGross_gleich`), stillness of non-success walks.
- §6 machine connection: refusing `adapterGross`, `GrossZustand`,
  `GrossEreignis`, `HwGrossSchritt` with the EXACT two-way embedding
  of `HwSchritt` (`einbettung_vor/zurueck`, `alt_invert`), walk/fault
  inversion, fault stillness, `hwGrossSchritt_wf` (via accepted
  `hwSchritt_wf`), planted noncanonical refusal.
- §7 witness tables (frames 40/41/42; aligned 2M leaf frame 512;
  misaligned twin frame 513; aligned 1G leaf frame 512*512):
  `wit_gross2M_ok` (.ok 2097152), `wit_gross1G_ok` (.ok 2^30),
  `wit_gross_fehl_rsvd`, `wit_gross_smep`, `wit_gross_smap`,
  `wit_gross_ac_erlaubt`, `wit_gross_nichtkanonisch_gp`,
  accessed/dirty set on exactly the touched entries, untouched words
  still.
- Joint `hwGross_zeuge`: well-formedness, both large mappings, the
  three faults, beside the accepted two-core TSO run (owner-only
  forwarding, drain 0 to 42 observed from both cores). Non-degenerate:
  two page sizes, two cores, a real memory change.

## Names of new definitions/theorems

See the `#print axioms` block at the end of the file (44 prints).
Entry points: `GrossSteuerung`, `smepVerletzt`, `smapVerletzt`,
`grossBlatt`, `gangGross2M`, `gangGross1G`, `gangGross`,
`seitenGangGross`, `adapterGross`, `GrossZustand`, `GrossEreignis`,
`HwGrossSchritt`, `witGrossTab`, `hwGross_zeuge`.

## Last build result

`./lean-probe grammatik/Grammatik/X86/HwPagingLarge.lean`:
`== 0 error(s)`. `./lean-bau`: `Build completed successfully
(677 jobs).` Axioms are subsets of standard (none / propext /
propext+Quot.sound); no `sorry`/`admit`/`axiom`/`native_decide`/
`unsafe`. No existing file changed except the one import line; no
existing theorem weakened.

## What remains open

- Reserved-bit STATUS on large leaves (RSVD fault) follows the 4 KiB
  walk's reserved-XD precedent; silicon's exact reporting stays a
  named assumption (CUTS).
- No TLB, no PAT/memory-type on large pages, no fault delivery, no
  per-access W/GX simulation, no timing (CUTS).
- Every bit position is a NAMED assumption: no Vol 3A paging text was
  supplied to this lane, so nothing here claims checked provenance.

## Task remarks

Nothing in the task was wrong. One implementation note: the
`touched`/leaf address expressions must repeat the accepted lookup
chain exactly (a four-level nesting in the leaf fallback does not
parse as the intended address); fixed by mirroring `seitenGang`.
