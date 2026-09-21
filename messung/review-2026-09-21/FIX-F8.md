# Fix lane F8 -- Lean witnesses and claims no bigger than proofs (2026-09-22)

Branch `review-0921-integration`, base `f05b7792` (F7). Findings: G01 F1-F4 (lanes 205, 206),
G02 F2/F4 (lane 203: Korpus125, Korpus07), G10 F3 (lane 231), SATZKARTE gaps.

**Commit:** `61bc218a` (code, Lean, docs). This report is committed separately.

## What was fixed

| # | Finding | Fix |
|---|---|---|
| 1 | G01 F1: `cform_nested_read_zeuge` degenerate (layout without a block, both sides `none`; decorative G conjunct) | `CFormNested.lean`: `nzL` maps `.glob 7` to a live `natLay 12 [uint32_t]` block, every cell holds its own byte offset. The witness now proves: nested read of `M[1][2]` = flat read of element 6, the flat read is `some (.int 24, _)`, the transposed `M[2][1]` is `some (.int 36, _)`, `flachIndex 4 1 2 = 6`. The unrelated `nv_lauf` conjunct is gone. |
| 2 | G01 F2: `simpruef_liefert` returned `sim124` whatever the certificate | `SimPruef.lean`: `pruefeSim` compares with `(List.range 13).map gOfA` etc. directly. New `R124c c` (the relation built from the certificate's tables via `tabG`/`tabH`), `r124c_eq` (check => `R124c c = R124`), and `simpruef_liefert` now builds `SimC` with `R := R124c c w` (field `rel` records it), discharging start and steps by transport to `r124_start`/`schrittA`/`schrittB`. `pruefeSim_falsch`: the integration's `gB[7] = 3` certificate is refused; `r124c_falsch_anders`: its relation names residue 3 where `R124` names 4. The witness `simpruef_124_zeuge` additionally relates the reached C configuration to a reachable G machine BY `R124c cert124_printed`. |
| 2b | G01 F3: Rust round trip literal against literal | `corrcert.rs` test reads `SimPruef.lean` with `include_str!` and extracts the `cert124_printed` body. **Planted defect measured:** changing only the Lean literal (`gB[7]` 4 -> 3) turns `sim124_lean_literal_stimmt_mit_simpruef_ueberein` red (left/right differ); restored. |
| 3 | G02 F2: Korpus125 reshape (`return 0`) not forced | Built `let r = 0; locks WACHE { let v = z; z = v; r = z; } return r;` (keeps the source's `let v = z; z = v`). Typechecks, `kP_akzeptiert` still `decide`s `true`, `KoerperGutS` re-proved (new helper `execStmtH_locks_blk` for a multi-statement lock body). Renamed `korpus125_nutzer_umgestaltet` -> `korpus125_nutzer`, `korpus125_ziel_umgestaltet` -> `korpus125_ziel`, `..._zeuge` -> `korpus125_nutzer_zeuge`. The witness gains a run of `lese_schreibe` from `z = 5` returning the value `5` (the reshaped body returned 0). `offen125` now names the EXPORTER gap (LG004), not a G gap; `tests/lean_g.rs` comments updated (assertions unchanged). |
| 4 | G10 F3: `KeinLogikHaltG` bridge narrower than claimed | Strengthened, `Divergenz.lean` §4/§8: `SpinKopf` (the three heads of the empty `forever a invariant true {}` spin), `spin_prueft` (every clause of `PrueftG` at such a head = per-thread `KeinLogikHaltG`), `ret_prueft` (bare `return` head). G-machine witness `ewig_spin_zeuge`: program `divPS` (divP reduced to the bare spin / `return 0`), a machine REACHED in two G steps (`endeEntf`, `dannForever`) with thread 0 at `.ewig () 1 .wahr .nil k`, `KeinLogikHaltG divO 1 M` for all threads, and thread 0's next step via `ewig_wahr_schreitet`. `nieZurueck_blatt_frei` renamed `bindAxiom_kein_blatt` with an honest docstring (vacuous discrimination). Header and CUTS narrowed: per head only, empty body + `.wahr` guard only, one reached machine. |
| 5 | SATZKARTE sections missing | Added §44 (205, CFormNested), §45 (206, SimPruef), §46 (231, Divergenz). 228 has §40, 233 has §42 (F5) -- not duplicated. |
| 6 | G02 F4: Korpus07 "proved blockage" | The CUTS note was already corrected (G02 `407e86c6`); the HEADER still said "the PROVED blockage" and the section title "The blockage, proved". Both now say the source side is a reading; the lemmas restate `Tab := Empty`. TODO's line already said "a reading of the source". |

`TODO.md`: rows for 203/125, 205, 206, 231 updated to what is proved.

## Measured (local, fisch unreachable)

`free -g` before each heavy run: 31 GB total, 20 GB available.

- **Lean:** `lake build` -- 281 jobs, completed successfully, 0 errors.
  `#print axioms gabbro_ziel` = `propext, Classical.choice, Quot.sound` (unchanged).
- **`#print axioms` of new/changed theorems:**
  - `cform_nested_read`, `cform_nested_read_zeuge`: propext, Classical.choice, Quot.sound
  - `simpruef_tab`, `erwartet_ist_r124`, `r124c_eq`, `simpruef_liefert`, `pruefeSim_falsch`,
    `simpruef_124_zeuge`: propext, Classical.choice, Quot.sound; `r124c_falsch_anders`: propext
  - `korpus125_nutzer`, `korpus125_ziel`, `korpus125_nutzer_zeuge`: propext, Classical.choice,
    Quot.sound; `kP_akzeptiert`, `offen125_ret_unter_locks`, `offen125_lese_aussen`: propext
  - `spin_prueft`, `ret_prueft`, `ewig_spin_zeuge`, `ewig_wahr_schreitet`,
    `bindAxiom_kein_blatt`: propext, Classical.choice, Quot.sound
- No `sorry`, `admit`, `axiom`, `native_decide` in the five touched Lean files (grep).
- **cargo test --no-fail-fast:** 72 collections, 1325 passed, 0 failed, 1 ignored (= baseline).
- **pruefe-emission.sh:** ALL PASS -- 37 durchgestochen, 288/288 compile, 2 reverse probes. ASan
  (stage 6b) not run on this machine. No `MARKE_EMIT` touched.
- **pruefe-saetze.py:** pass (0 invented). **pruefe-kennungen.py:** ALL PASS.
- **pruefe-todo.py:** 16 findings (= baseline). **pruefe-englisch.py:** red as on the base; diffed
  against the base: German counts unchanged (37 German prose pieces, 7965 German comment lines,
  774 German-stem identifiers), only totals grew.
- **Corpus:** no `beispiele/` file touched; no Rust checker/emitter code changed (only a unit test
  and test comments), so no verdict can move.

## What stays open, and why

- **206 / program #2:** the certificate decides the relation, not the proof. Segments
  (`gBlatt`, `gNimm`, `gSetze`, `gGib`, `gPruefe`) and `schrittA`/`schrittB` are hand-proved
  for `R124`; a checker that establishes `SegPasst` per C step from a certificate does not exist.
- **231:** the spin facts are per head; no theorem shows a thread stays in `SpinKopf` along its
  steps (that needs an inversion of `RufSchrittG` over ~90 rules), and only the empty body with
  guard `.wahr` is covered. `KeinLogikHaltG` is shown for one reached machine. The never-asm
  lemmas still describe the axiom's assumption, not the C lowering (G10 F2).
- **125:** the Rust exporter still refuses the source shape (LG004); it has no rule rewriting a
  return under a lock into the outer-local form. The witness runs are body runs, not machine
  runs from the declared starts (G02 F5).
- **205:** the model side of the nested read (`corrW` for a static C array) is still not stated;
  `pruefe-cformen.py` has no nested-array row.
- Not run: `abnahme.py`, `pruefe-zahlen.py`, `mutiere-pruefer.py`, `pruefe-beweise.sh`, ASan.
