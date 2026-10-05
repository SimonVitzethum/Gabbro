# MUSE-REPORT-1299: Translation -- page walk joined with the TLB and the flat memory model

Clone: /home/simon/Dokumente/gabbro-muse/a1299, branch muse/1299 (verified).
Owned files only: `grammatik/Grammatik/X86/HwTranslate.lean` (new, ~770 lines),
one import line in `grammatik/Grammatik.lean`, this report.

## What was done

Joined lane 1283 (`HwPaging.lean`, 4-level walk, no TLB) with lane 1285
(`HwSegTlb.lean`, TLB over a walk PARAMETER): `walkLesen` instantiates the
TLB walk parameter with the page walk (page `s` probed as a user read of
`s * 4096`; success names the frame, any other outcome is a miss), and
`uebersetzeMitTlb` is the joined resolution (hit answers from cache, miss
walks). All accepted definitions reused unchanged (lifted, never redefined).

Sections and exact names:

- §1 join agreement: `walkLesen_ok`, `walkLesen_keinOk`, `uebersetze_trifft`
  (stale rule, from `tlbAufloesung_trifft`), `uebersetze_verfehlt` (miss rule,
  from `tlbAufloesung_verfehlt`).
- §2 fresh vs stale: `seitenNr_mal_basis`, `walkLesen_ausgerichtet`,
  `uebersetze_frisch_ok`, `uebersetze_frisch_braucht_gang` (admitted fresh
  access comes from the walk), `uebersetze_stal_unabhaengig` (on a hit the
  tables are never consulted -- the exception mechanism).
- §3 INVLPG/CR3: `uebersetze_nach_invlpg` (from `tlbNachEntfernen_geht_durch`),
  `uebersetze_cr3_leert` (from `tlbCr3Spuelung_leert`), `uebersetze_invlpg_lokal`
  (from `tlbEntfernen_lokal`).
- §4 flat bridge: `uebersetze_frisch_flach_lesbar`,
  `uebersetze_frisch_flach_schreibbar` (fresh admission meets the flat byte
  permission via the lane-1283 obligation `FlachStimmt`; the write direction
  states both the read-probe walk and the write walk explicitly since they
  may differ).
- §5 machine connection: refused plug `adapterUebersetz` +
  `adapterUebersetz_verweigert`; state `UebersetzZustand`; events
  `UebersetzEreignis` (alt/invlpg/cr3/zugriffOk/zugriffAlt/zugriffPf); step
  relation `HwUebersetzSchritt` (fresh = miss + walk + A/D write-back; stale =
  hit self-loop with tables kept; fault = miss + fault self-loop); exact
  two-way `HwSchritt` embedding (`hwUebersetzSchritt_einbettung_vor`,
  `hwUebersetzSchritt_alt_invert`, `hwUebersetzSchritt_einbettung_zurueck`);
  inversion/stillness (`zugriffOk_invert_gang/miss`, `zugriffAlt_invert_hit`,
  `hwUebersetzSchritt_veraltet_still`, `zugriffPf_invert_gang/miss`,
  `hwUebersetzSchritt_fehler_still`); `hwUebersetzSchritt_wf`; planted
  refusals (`uebersetzGross_verweigert`, `uebersetzSteuer_verweigert`,
  `uebersetzGp_verweigert`, `uebersetzSchritt_frisch_braucht_miss`,
  `uebersetzSchritt_veraltet_braucht_treffer`); forward agreements
  (`uebersetz_invlpg_vereinbarung`, `uebersetz_cr3_vereinbarung`).
- §§6-7 witness (task: mapping changed, stale access, INVLPG, faulting
  access): `witUebersetzTab1` (RW leaf of linear page 1 cleared in memory),
  `witUebersetzTlb` (`[⟨1, 32⟩]`), `witUebersetzAdr` (4096); pins
  `witUebersetz_seite/_offset_null/_phys/_veraltet/_veraltet_ist_trifft`
  (stale use IS the lifted hit rule), `_neu_pf` (changed walk faults
  non-present), `_walk_fehl`, `_nach_invlpg_fehl`; joined state
  `witUebersetzM` (+`witUebersetzTlbs/_null/_wf`); reached steps
  `witUebersetz_veraltet_schritt`, `witUebersetz_invlpg_schritt`,
  locality pin `witUebersetz_invlpg_lokal`; joint `hwUebersetz_zeuge`
  (old walk admits 131072 via reused `wit_lese_rw_ok`, changed walk faults,
  stale entry admits, INVLPG re-faults as resolution and as reached steps,
  plus reused two-core TSO leg `hwWit_weiterleitung/_fremd_alt/_spülung`).

Silicon provenance (checked this lane, clone-local extract): Intel SDM
325462-093US Sept 2026 -- INVLPG page-granular (Vol 2; Vol 3A §5.10.4.1),
PCIDE=0 gives PCID 000H, MOV-to-CR3 drops all non-global entries for PCID
000H (§5.10.4.1); model runs PCID-off with no globals (lane-1285
`tlbGlobal`). No hardware correspondence claimed (see CUTS).

## Verification

- `./lean-probe grammatik/Grammatik/X86/HwTranslate.lean`: 0 errors.
- `./lean-bau` (full project): `Build completed successfully (677 jobs).`
- `#print axioms`: every new theorem depends only on subsets of
  `[propext, Quot.sound]` (several on nothing); within the standard goal set.
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; English only; every
  premise used (the write-direction bridge carries both walk premises for
  exactly this reason).
- Rule 13: no theorem quantifies over program syntax (`Vertrag`/`Stmt`/…),
  so no syntax-witness companion is triggered; the `_zeuge` joint witness
  joins all legs (mapping change, stale use, INVLPG, fault, two-core
  memory-changing TSO run).

## What remains open (also in CUTS)

Write-probe walk (read-probe + write-walk split is explicit, not unified);
per-entry permission caching (a hit reuses the frame with no rights
re-check -- stated as the exception, not closed); large pages refused;
SMEP/SMAP per-access semantics refused wholesale; fault delivery (no IDT
path); `FlachStimmt` for a real OS is user logic; no W/GX simulation, timing,
or source-stop transfer.

## Task remarks

Nothing in the task was weakened. One judgment call: the MECHANISM template
asks for a "memory-changing step" where the family touches memory -- the
translation family itself never changes `HwMaschine` memory (A/D bits live
in tables outside it, same reason the paging lane's adapter refuses), so the
memory-changing leg is the reused accepted two-core TSO run conjoined in
`hwUebersetz_zeuge`, exactly as lane 1283 did. The mapping change in memory
(cleared leaf) is the translation-side state change, proved as differing
walk outcomes plus reached steps.
