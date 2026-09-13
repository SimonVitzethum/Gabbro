# MUSE-REPORT-133 (lane 133, docs lane — goal map over machine G)

## What I did

Added `## 11. The goal over machine G (2026-09-13)` to `dokumente/SATZKARTE.md`
(English), and marked §§7-10 as superseded by §11 in one line at the top of §7.
No Lean or Rust changes (docs lane); §§1-10 untouched except the one supersede line.

§11 contains, per the task:
1. The exact statement of `ziel_ort_geraet` (copied verbatim from
   `grammatik/Grammatik/ZielOrtGeraet.lean:1105-1112`), plus the conclusion gloss
   (`VertragAmOrtG`, `ZielOrt.lean:67`).
2. A table of EVERY premise with class (a) user / (b) hardware / (c) decidable /
   (d) other-or-DATA, each with the theorem justifying the classification:
   decidable checks via `programmImFragmentG_ok` / `fussOrtGB_ok`
   (`ZielOrtGeraetSem.lean:497/:469`, plus `kandB_kandP`, `fussOrtB_of_G`);
   `RegLokal` via `regLies_gleich`/`sichtbar_gleich`/`regLokal_orakelAus` and the
   exclusion `ziel_ort_register_ausgeschlossen`; `StartExklusiv` in the audit's
   corrected class — (d) start-configuration fact (`AuditZiel.lean:12-18`,
   `audit_startExklusiv_const`, `audit_same_lock_start_excluded`, consumed by
   `exklusivG`); `e0` as (d) declaration-shape datum
   (`audit_antwortWelt_uses_e0`); `hK`/`hStart` as (a) with the weakening chain
   `koerperGutG_of_V` / `koerperGutV_of_kOk` and the three joint witnesses.
3. Non-coverage collected from every CUTS block of the Ziel*/Ruf*/Rennfrei files:
   fragment limits (incl. `KandOk` indirect calls, unrepaired widening refuted by
   `ziel_ort_register_falsch`, missing `awaits` refutation); `e0`; locks-block-only
   guards (footprint and device); non-local oracles (incl. minimal visibility half,
   no async device step); costs/time — **no `KostenG.lean` exists in the tree,
   stated as missing**; converse adequacy limits (`ohneOrakel`, memory-only,
   first-pop cut, `TiefK` fragment, `rufRumpf`-vs-`rufAt` via `befund_vertrag`);
   lock-free sharing in race freedom (atomics/published excluded by design,
   unshared carriers checker duty); witness limits of all three Zeuge files.
4. `#print axioms` record via probe `.tmp/sonde133.lean` (`./lean-probe`,
   0 errors): `ziel_ort`, `ziel_ort_voll`, `ziel_ort_geraet`, `rennfrei_g` all
   depend only on `[propext, Classical.choice, Quot.sound]`.
5. An adversarial "distance to the goal" paragraph (§11.5): slogan nearly true on
   the covered fragment, with three premises outside it (`StartExklusiv`, `e0`,
   checker computations) and priced deductions (`KoerperGutG` quantifies over all
   local oracles — stability not assumable; `grund` carries no contract; adequacy
   is against `rufRumpf`, never `rufAt`).

## New definitions/theorems

None. No Lean file touched, no Rust touched. New mappings only (table rows in
§11.2, gap list in §11.3). Probe file `.tmp/sonde133.lean` is git-ignored and
not committed, per the task.

## Last `./lean-bau` result line

`== 0 error line(s) in the COMPLETE output` (86 jobs, "Build completed
successfully"). Ran before writing §11 to produce the `.olean` files the probe
needs; first `./lean-probe` run failed on missing oleans, re-ran green after
the build. No Lean sources were modified, so the build result is independent of
this lane's edit.

## What remains open

- The map asserts per-line readings (e.g. `RufUmkehrRufG` CUTS, `RufHaeltG` CUTS,
  `ZielOrt.lean` cost note); a second reader should spot-check the cited lines.
- `pruefe-englisch.py` exits 1 with and without my change (baseline verified via
  `git stash`); pre-existing, not caused by this lane. My section is English;
  working documents are explicitly out of that guardian's scope per its own text.
- The Opus lane extending `ziel_ort` to loops/axioms may add new CUTS after this
  map; §11 is current as of branch `muse/133` at commit time.

## Anything in the task I believe is wrong

One classification judgment call worth recording: the task's class list has no
DATA class, but `P/O/passes/fs/sp/init/hr` are pure binders — I marked them DATA
in the table (same convention as §2) rather than forcing them into (a)-(d).
`e0` is a borderline case (a datum with existential content); I put it in (d)
as a declaration-shape datum since it excludes a whole program class, which is
more informative than DATA. Nothing else contested: `KostenG.lean` is genuinely
absent (glob + grep over `grammatik/` and `dokumente/`), and the audit's
`StartExklusiv` class ("start-configuration fact", neither user/hardware nor
decidable-in-general) is used as instructed.
