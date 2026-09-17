# MUSE-REPORT-203 — Lane 203: hand models for 07/59/109/125 (TODO §1.3, Lean half)

Round 1 (reviewer-only verdict, committed as `c47539ee`) is superseded by this
round: per findings F-1–F-4 from reviewer lane 211, the models are now BUILT.

## 0. Response to the round-1 findings

- **F-1 (task compliance): accepted.** The reviewer instruction is right: the
  task SCOPE explicitly authorizes the new files plus the `Grammatik.lean`
  import, and HARD RULE 5's exception fires there. All four files exist now;
  `grammatik/Grammatik.lean` carries the four imports (the only existing file
  touched). 109 and 59 are delivered `kP`-style per `Korpus124.lean`
  (Einheit term, lock family, starts, premise groups stated AND proved). 07
  and 125 use the named-open-premise route, each with the attempted `Einheit`
  term beside the finding.
- **F-2 (build evidence): accepted.** `./lean-bau` was run after adding the
  files; last result line (§6).
- **F-3 (witnesses): accepted with one principled exception.** `korpus109_`
  `nutzer_zeuge`, `korpus59_nutzer_zeuge` and
  `korpus125_nutzer_umgestaltet_zeuge` are built (joint non-degenerate runs,
  §5). For 07 the witness is genuinely unbuildable and the contradiction is
  exhibited precisely (`offen07_kein_zeuge`: the rule-13 existential over
  `Q07.Tab` fails on every `t`), not asserted. The names `korpus07_nutzer`
  and `korpus125_nutzer` are deliberately NOT claimed anywhere: stating them
  over a degenerate/reshaped program would be the weakening rule 13 forbids.
- **F-4 (citation hygiene): accepted.** Every refusal cited below was
  re-verified against the merged tree's `crates/gabbro-check/src/lean_g.rs`
  (read-only); exact predicates are quoted, not line numbers.

## 1. What was built

| file | status | theorems |
|---|---|---|
| `grammatik/Grammatik/Korpus109.lean` (527 lines) | FULL model of `beispiele/109` | `kP_akzeptiert`, `korpus109_nutzer`, `korpus109_ziel`, `korpus109_nutzer_zeuge` |
| `grammatik/Grammatik/Korpus59.lean` (546 lines) | FULL model of `beispiele/59` (one documented annotation-weakening) | `kP_akzeptiert`, `korpus59_nutzer`, `korpus59_ziel`, `korpus59_nutzer_zeuge` |
| `grammatik/Grammatik/Korpus125.lean` (~380 lines) | RESHAPED model + PROVED blockage | `kP_akzeptiert`, `korpus125_nutzer_umgestaltet`, `korpus125_ziel_umgestaltet`, `korpus125_nutzer_umgestaltet_zeuge`, `offen125_ret_unter_locks`, `offen125_lese_aussen` |
| `grammatik/Grammatik/Korpus07.lean` (174 lines) | ATTEMPTED Einheit + PROVED blockage | `korpus07_nutzer_leer`, `kP_akzeptiert`, `offen07_kein_zeuge`, `offen07_kein_schreiber` |

New definitions per file mirror `Korpus124.lean`: declaration (`kD`),
bodies (`kRumpf*`), program (`kP`), lock family (`kSI`), starts inside the
Einheit (`kE`), empty oracle (`kO`). No existing theorem was deleted or
weakened; no new diagnostic codes, gift or example numbers.

## 2. Measure (deliverable 2)

Before: 2 of 6 (108 via exporter, 124 by hand). After: **4 of 6 with full
models** (108, 124, 109, 59) **plus 125 reshaped-with-proved-blockage**;
07 attempted with proved impossibility of a non-degenerate witness.

## 3. Per-program notes

- **109** (`K109`): tables `T`/`U` (count 4, `u32`), locks `L`/`M` (ranks
  0/1, disjoint), index-param leaves writing constants, distributors taking
  their lock around one call, starts = the two entry dispatch roots. No
  annotation dropped (109 has no `deadline`/`falsifier`; `costs`/`reads` are
  ignored form). Contracts `.wahr`, lock family trivially true (source
  declares neither). `Akzeptiert … = true` by `decide`.
- **59** (`K59`): tables `Takte`/`Auftraege` (counts 64/16, `u64`), locks
  `TAKT`/`RING` (both rank 0; `masks irqs` modelled as `D.maskiert TAKT =
  true` -- the file's one-word difference from gift 460 is a model bit).
  ONE DOCUMENTED ANNOTATION-WEAKENING: the source's `deadline <= … arch
  x86_64 falsifier …` on all four functions is dropped, because `check_fn`
  refuses exactly that: `refuse("LG001", format!("function {} carries a
  form with no G counterpart", f.name))` when `d.deadline.is_some() || … ||
  d.arch.is_some() || …` (re-verified at `check_fn`). Bodies, Held sets,
  locks, starts and effects are kept.
- **125** (`K125`): global `z : u32` with the declared initializer as `sp0`
  (`z = 0`), lock `WACHE`, `concurrent` starts, faithful `setze_null`.
  `lese_schreibe` is reshaped (writeback inside, `return 0` outside) and the
  reshape is proved necessary, twice: `offen125_ret_unter_locks` (a return
  inside needs `[held WACHE].Perm (vertragVon … lese).ende`, but `ende =
  haelt.map held ++ …` is `[]` -- uninhabited via `Perm.length_eq`) and
  `offen125_lese_aussen` (`gdarf z []` uninhabited -- the guarded read cannot
  move out either). This is the G-side face of exporter refusal LG004 for
  value readers under `locks` (same wall as the refused 108 root shape noted
  in `Export108.lean`). Named gap `offen125` (String): corpus moves the
  return out (lane 204's territory) or G gains the form.
- **07** (`K07`): faithful declaration is `Tab/Lock/Fn := Empty`, `starts :=
  []` -- exactly what the exporter refuses: `refuse("LG001", "a G
  declaration needs at least one table")` and `refuse("LG001", "a G program
  needs at least one function")` (both re-verified in the model's `check`
  function); the entry dispatches are `extern`, hence `refuse("LG001",
  "function {} is not `impl`")`. Vacuous group `korpus07_nutzer_leer`
  exhibited beside the blockage. Named gap `offen07`: G forms for
  entry/boot/walk/format.

## 4. Axioms

`#print axioms` at the end of every file; all main theorems depend only on
the standard three (`propext`, `Classical.choice`, `Quot.sound`), and several
only on subsets (`kP_akzeptiert`: `[propext, Quot.sound]` or `[propext]`;
both `offen125_*`: `[propext]`). No `sorry`/`admit`/`axiom`/`native_decide`
anywhere (a stray `sorry` placeholder during construction was replaced
before probing; the final `offen07_kein_zeuge` and `kP_akzeptiert` for 07 are
`[propext]`).

## 5. ZEUGE accounting (rule 13)

- `korpus109_nutzer_zeuge`, `korpus59_nutzer_zeuge`: premise group JOINTLY
  with a non-degenerate run -- the index leaf's body from the all-zero world
  returns with slot 0 = 1 while it started 0 (table a function writes;
  reached run with a memory-changing step; `rfl` throughout, valid for every
  handler `R`).
- `korpus125_nutzer_umgestaltet_zeuge`: same shape on the reshaped program
  (`setze_null` from the `z = 5` world returns with `z = 0`).
- 07: `offen07_kein_zeuge : ¬ ∃ _t : kD.Tab, True` (proved) plus
  `offen07_kein_schreiber` -- the joint instantiation is impossible on the
  faithful declaration, exhibited term-precisely.

## 6. Build state (F-2)

`./lean-bau` after adding all four files plus the four `Grammatik.lean`
imports:

> `Build completed successfully (272 jobs).`

(268 jobs before this lane + 4 new files.) Every file was additionally
checked incrementally with `./lean-probe` (first line `0 error(s)`) after
each construction step; all intermediate commits on branch `muse/203` are
green. `./cargo-pruef` was not run: no `.rs` file was touched (out of scope
for this task; lane 201 owns `lean_g.rs`).

## CUTS (lane-level)

- 109: none inside the file (covers the whole source except `costs`/entry
  hardware, as documented in the file's `CUTS`).
- 59: the `deadline`/`arch`/`falsifier` annotations (§3).
- 125: source-shape `lese_schreibe` open (`offen125`); no `korpus125_nutzer`
  claimed; no stage-(b) certificate.
- 07: no `korpus07_nutzer`/`korpus07_nutzer_zeuge` (impossible, proved).
- Not claimed anywhere: any link between a `.gab` text and its model (no
  exporter link -- lane 201), and no simulation certificate (stage b).
- Pre-existing linter warnings of the kind the tree already carries
  (`constructorNameAsVariable` for single-letter binders, unused-variable
  hints) were left in place; zero errors.
