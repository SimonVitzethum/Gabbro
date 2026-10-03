# MUSE-REPORT-830: Composition closing — spill-privacy closing

## Task
Close allocation spills to fresh private frame slots: token-threaded,
disjointness plus permissions checked, save/restore on all paths.
Compose already-accepted modules into one checked closing step without
re-proving their internals or duplicating an interpreter/executor.

## What was done
New file `grammatik/Grammatik/X86/ComposeSpillPrivacy.lean` (259 lines,
probe 0 errors) plus one import line in `grammatik/Grammatik.lean`.
It closes exactly one producer/consumer interface, reusing accepted
definitions by name:

- Producers: `SpillPrivate` (lane 343: `spillSlot`, `SpillFrisch`,
  `GetrenntK`, `spillPrivatOk`, `SpillZugelassen`, save/load equations,
  freshness/commutation facts), `Stapel` (lane 309: `Rahmen`,
  `sichereWort`, `ladeWort`, `sichere_lade_rundreise`, refusals,
  permission preservation), `TableLayout` (lane 345: `zeugenU`
  non-degenerate writer program) over canonical `Speicher`/`TSO`.
- Consumer: `spillPrivatSchritt`, which threads one `Option Speicher`
  token through checked save then checked reload, so a refusal on ANY
  path yields `none` loudly. A conjunction of checks is not execution:
  the closing theorem concludes reached save/reload equations, and the
  joint witness exhibits a reached memory-changing run (byte `0x00`
  becomes low byte of `42` at slot 0) plus three planted refusal cases.

## New definitions/theorems (exact names)
- `spillPrivatSchritt` (def): token-threaded save-then-reload step.
- `spillPrivatSchritt_erfolg`: reached save + reload compute the step.
- `spillPrivatSchritt_verweigert_speichern`: refused save threads `none`.
- `ComposeSpillPrivacy_verbindung` (TARGET): bound + validator admission
  + TSO freshness + disjointness + readability + reached save + reached
  reload imply `w = v`, threaded step success, `SpillZugelassen`,
  permission preservation, disjoint foreign `read64` stability, reload.
  Every premise is used (round-trip, joint admission, foreign stability,
  injection against the round-trip).
- `ComposeSpillPrivacy_verbindung_zeuge` (TARGET companion): all seven
  premises instantiated jointly on `speicherZeuge`/`spillZeuM1`/
  `spillRahmenW`/slot 0/`42`/`16`/`spillTSO0`, beside the writer program
  fact `zeugenU_schreibt` (table `konto` written by `setze`), the
  observable memory change and the threaded step equation.
- Planted refusals: `ComposeSpillPrivacy_verweigert_genommen`
  (address-taken never jointly admitted),
  `ComposeSpillPrivacy_verweigert_aussen` (out-of-frame: save AND step
  are `none`), `ComposeSpillPrivacy_verweigert_schutz`
  (write-protected: save AND step are `none`).
- Witness helpers: `spillZeuM1`, `spillZeu_schranke`, `spillZeu_lesbar`,
  `spillZeu_schreibbar`, `spillZeu_speichert`, `spillZeu_rundreise`,
  `spillZeu_wechselt`, `spillZeu_ok`.

## Verification
- `./lean-probe grammatik/Grammatik/X86/ComposeSpillPrivacy.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau` last line: `Build completed successfully (509 jobs).`
  Whole `grammatik/` green including the new module.
- `#print axioms`: every new theorem depends only on subsets of
  `[propext, Quot.sound]` (several on no axioms at all); no `sorry`,
  `admit`, `axiom`, `native_decide` or `unsafe` anywhere in the file.
  The goal proof does not reference this module, so `gabbro_ziel`
  axioms are unaffected (no new axiom introduced project-wide).
- No diagnostic/gift/example/CLI numbers, no MARKE_EMIT changes, no
  source/checker/Spec/goal/emitter edits, no friend-reserved optimiser
  files touched. Owned paths only.

## Open (CUTS, not claimed)
SCFG-side application waits for the accepted 287 interface (owner 287,
reviewer 303); W store/read bridges wait for accepted 567/570
interfaces (owners 573, 574); extended decoder path is lane 575's; no
aligned multi-byte atomicity beyond byte-extensional commutation; no
LOCK RMW; no source-to-target simulation; no `valX86_sound`; no cost,
fairness or timing claim.

## Task remarks
Nothing in the task statement appeared wrong. One elaboration note:
`spillSlot r idx` and `r.schlitzAddr idx` are definitionally equal but
not syntactically so after unfolding, which defeats `rw [if_pos]`
matching and `rw`-auto-`rfl`; the file converts via ascribed `have`s
plus a closing `rfl` at the one affected site (`spillZeu_speichert`).
