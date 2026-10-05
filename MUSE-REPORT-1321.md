# MUSE-REPORT-1321

Lane 1321: Translation with large pages, per-access SMEP/SMAP, permission caching closed.

## What was done

New file `grammatik/Grammatik/X86/HwTranslateFull.lean` (~1080 lines), plus one
`import Grammatik.X86.HwTranslateFull` line appended to `grammatik/Grammatik.lean`.
Follow-up of lanes 1297 (`HwPagingLarge`) and 1299 (`HwTranslate`): the walk-or-TLB
join is instantiated with the FULL walk `seitenGangGross` (2 MiB / 1 GiB leaves,
per-access SMEP/SMAP+EFLAGS.AC), the flat-model bridge is proved for it, and the
lane-1299 stale exception is closed as an exact caching rule with reached witnesses.
Every accepted definition is reused unchanged (lifted, never redefined); no existing
file was edited except the one import line.

Core definition: `uebersetzeVoll gst tab tlb q` -- canonical first (`none` for
non-canonical `q.linear` before any cache look-up or walk), hit answers the cached
frame with NO rights re-check, miss runs the request's OWN full walk (this is what
puts large pages and per-access SMEP/SMAP inside the join; a read-probe walk as in
1299 would give wrong admissions for writes/fetches).

Step relation `HwUebersetzVollSchritt` over `VollZustand`
(machine + `GrossSteuerung` + tables + per-core TLBs) with events `VollEreignis`
(`alt`, `invlpg`, `cr3`, `zugriffOk`, `zugriffAlt`, `zugriffPf`, `zugriffGp`):
exact two-way `HwSchritt` embedding, canonical-first fresh/stale/fault steps, a #GP
step carrying only the walk equation, refusing adapter plug `adapterVoll`.

## Exact names of new definitions/theorems

Definitions: `uebersetzeVoll`, `FlachStimmtGross`, `adapterVoll`, `VollZustand`,
`VollEreignis`, `HwUebersetzVollSchritt`, `witVollTab1` (revoked mapping),
`witVollFlach` (frames 512..1023 + 262144), `witVollTlbs`, `witVollM`,
`witVollAdr`, `witVollM1` (post-write-back), `witVollMrev` (revoked tables).

Theorems. Agreement: `uebersetzeVoll_trifft`, `uebersetzeVoll_stal_unabhaengig`
(tables AND control), `uebersetzeVoll_frisch_ok`,
`uebersetzeVoll_frisch_braucht_gang`, `uebersetzeVoll_nichtkanonisch`,
`gangGross_nichtkanonisch_gp`, `seitenGangGross_nichtkanonisch_gp`,
`voll_walkLesen_gleich` (1299 probe correspondence via `seitenGangGross_gleich`).
Caching closure: `uebersetzeVoll_nach_invlpg`, `uebersetzeVoll_nach_invlpg_fehl`,
`uebersetzeVoll_cr3_leert`, `uebersetzeVoll_invlpg_lokal`; stale witnesses
`witVollTab1_pf`, `witVoll_stal_revoke`, `witVoll_stal_smap`, `witVoll_stal_smep`,
`witVoll_nach_invlpg_fehl`, `witVoll_nichtkanonisch_hit`. Flat bridge:
`gangGross_flach_schreibbar`, `gangGross_flach_lesbar`,
`flachGross_aus_flach_schreibbar`, `flachGross_aus_flach_lesbar` (transfer),
`uebersetzeVoll_frisch_flach_lesbar`, `uebersetzeVoll_frisch_flach_schreibbar`,
`flachStimmtGross_allwahr`, `witVoll_flach_liest`, `witVoll_flach_schreibt`,
`witVoll_flach_liest_1G`. Machine: `adapterVoll_verweigert`,
`hwVollSchritt_einbettung_vor`, `hwVollSchritt_alt_invert`,
`hwVollSchritt_einbettung_zurueck`, nine `vollZugriff*` inversions
(`voll` prefix: the plain `zugriff*` names are taken by lane 1299),
`hwVollSchritt_veraltet_still`, `hwVollSchritt_fehler_still`,
`hwVollSchritt_gp_still`, `hwVollSchritt_wf`, refusals `vollGp_verweigert`
(non-canonical admits only #GP), `vollGross_verweigert`, `vollSteuer_verweigert`,
`vollSchritt_frisch_braucht_miss`, `vollSchritt_veraltet_braucht_treffer`,
agreements `voll_invlpg_vereinbarung`, `voll_cr3_vereinbarung`. Witness:
`witVollTlbs_null`, `witVollM_wf`, `witVoll_veraltet_schritt`,
`witVollAdr_seite`, `witVoll_invlpg_schritt`, `witVoll_invlpg_lokal`,
`witVoll_schreib_ok`, `witVoll_frisch_schritt`, `witVoll_gp_schritt`,
`witVoll_pf_schritt` (core 1 faults the revoked page core 0 still admits),
`witVoll_cr3_schritt`, `witVoll_kette` (stale self-loop then INVLPG),
joint `voll_zeuge` (29 conjuncts: mappings, faults, stale admissions,
reached steps on two cores, write-back bits, flat permissions, TSO run).

## Last build result

`./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`, 688 jobs,
`Build completed successfully`. `./lean-probe` on the file: 0 errors.
`#print axioms` for every main theorem: `[propext, Quot.sound]` or a subset
(no `Classical.choice` needed, no `sorryAx`) -- within the standard goal set.

## What remains open (see CUTS)

No hardware correspondence beyond self-consistency; silicon bit positions,
INVLPG/CR3-flush semantics, canonical-first ordering and shootdown-as-user-duty
are named assumptions. No write-probe walk (by design: per-access miss walk).
`FlachStimmtGross` for a real OS is user logic; only pointwise large-page
instances are witnessed (a full instance quantifies over all requests and is not
`decide`-able). `steuerVerweigert` unreachability through the dispatcher is not
proved (unneeded: neither arm produces it; armed control is per-access).
No W/GX simulation, timing, or source stop-class transfer.

## Task feedback

Nothing in the task is wrong. Three notes for the merger: (1) the name
`HwVollSchritt` was already taken by the capstone union step, so the new
relation is `HwUebersetzVollSchritt`; likewise the nine inversion lemmas carry
the `voll` prefix (plain `zugriff*` names taken by 1299). (2) Rule-13
companions: the task has no `ZEUGE:` lines and no theorem quantifies over
program syntax; `voll_zeuge` is the MECHANISM joint witness (two cores, table
changes via accessed/dirty write-back, TSO drain 0 -> 42 with owner-only
forwarding reused). (3) "Poison probes" for this Lean lane are the planted
refusal theorems (`vollGp/vollGross/vollSteuer_verweigert`, the two
exclusions); there are no corpus files, consistent with both predecessors.
