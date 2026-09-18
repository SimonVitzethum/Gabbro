# MUSE-REPORT-231 — divergence lemmas for accepted never-bodies (Lean)

Lane 231 (TODO §-1 wave B, pure Lean). New file only:
`grammatik/Grammatik/Zielsatz/Divergenz.lean` (+ one import line in
`grammatik/Grammatik.lean`). No existing Lean file touched. No Rust, no
diagnostic codes, no gift/example numbers, no corpus changes.

## Read first (done)

- MUSE-REPORT-225: acceptance is sentences + probes with zero behavior
  change; N321 byte-identical. Honest never-shapes: `asm` with no `out`,
  un-leavable `forever` (`per_pass bounded`, diverging `on_exceeded`, no
  total `costs`), tail call to a `-> never` routine.
- `Lebendigkeit.lean`: divergence meets progress at the `ewigWeiter` step
  (my `ewig_wahr_schreitet` is the same pattern at one step).
- `Zielsatz/Spec.lean` `KeinLogikHaltG`/`FortschrittG`/`HaltArt.nieZurueck`;
  `ProbeD.lean` (the `forever` probe + `ewP` inhabitation pattern);
  `Zielsatz/NeverAsm.lean` (never-axiom model error, extended not edited).
- `TODO.md` §-1, `SATZKARTE.md` (never/`KeinLogikHaltG` rows).

## What was built

**§1 exit evidence.** `NoExit` (body answers only `ok`/`next` — the
model's "un-leavable") and `InvWahr` (guard holds everywhere).

**§2 `forever` divergence as declared.**
`foreverLauf_noexit` (syntax-free fuel induction — no witness owed),
`forever_noexit_divergiert` (ends in `hardware (fortschritt a)` at every
budget: the named `progress` assumption, i.e. the model's `on_exceeded`
exit), `forever_noexit_kein_logik`, `forever_noexit_kein_zurueck`,
`forever_leer_divergiert` (empty spin, no evidence premises).

**§3 `asm` divergence per declared effects.**
`asm_never_antwort_leer` (per-axiom answer emptiness — the asm exit
evidence), `asm_never_kein_ok` (a `bindAxiom` to `never` never answers
`ok`; outcome is `hardware (annahme a)` via `execBlock_bindAxiom_never`).

**§4 bridge to `KeinLogikHaltG` (extends, never weakens; `Spec.lean`
untouched).** `ewig_wahr_schreitet` (true-`forever` head takes its G step
`ewigWeiter` — the rule's `hw` premise IS the leg's loop clause, holding
by computation), `nieZurueck_blatt_frei` (a `bindAxiom` head passes both
`PrueftG` leaf clauses, restated — `.2.x` projection syntax cannot unfold
the def, so the clauses are restated verbatim).

**§§5–7 witness.** `divD` (table `konto`, lock `m`, writer `schreib`,
reader `lies`, one axiom with `aerg = some .never` — the accepted `asm`
shape), `divP` (`schreib` writes `konto[0] := 100` then diverges in the
accepted `forever` shape; all contracts `true`), `divO`, `divSp0`,
F-machine run `divB_erreicht` (lock + writing leaf) with
`divB_schreibt` (`konto[0]` `0 -> 100`, non-degenerate) and head at the
`forever` (`divM2kopf`), `divRest_divergiert`, and
**`divergent_body_zeuge`** instantiating `NoExit`/`InvWahr`, the
divergence (proved FROM the witnessed evidence), the reached run with the
memory move, `StelleOk (.inl ())`, and `AntwortLeer` — all JOINTLY.

Every premise of every theorem is used by its proof (checked by hand at
each step). No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.

## Verification

- `./lean-probe …/Divergenz.lean`: exit 0, **0 errors**. Axioms: all eleven
  `#print` lines are subsets of `[propext, Classical.choice, Quot.sound]`
  (two are smaller: `foreverLauf_noexit` `[propext]`,
  `asm_never_antwort_leer` `[propext, Quot.sound]`).
- `./lean-bau`: **Build completed successfully (278 jobs)** (full project).
- Planted defects (scratch `.tmp/defekt-231.lean`, git-ignored, NOT
  committed): a `forever` with FALSE invariant claimed divergent, and a
  LEAVABLE `forever` claimed divergent — both fail red (exit 1, 2 errors),
  pinning that `InvWahr`/`NoExit` are load-bearing.
- `CUTS:` block at end of file lists proved vs named-open (writer's logic
  stays premises; no checker acceptance claimed in Lean; F-machine run
  only; per-head bridges, not the leg itself).

## Where the task is wrong or ambiguous (stated plainly)

1. The wave-5 boilerplate ("independent reviewer, change no existing
   file") contradicts the task's own "Add the import to `Grammatik.lean`".
   I followed the task (one import line added).
2. "A `forever` with no exit argument must fail red": as lane 225 found,
   every parsed `forever` carries `on_exceeded`, so the literal shape is
   unparseable. I planted the two nearest FALSE claims instead (false
   invariant; leavable body) — both red.
3. "Witnesses built on `ReferenzB`": `refD` has `Ax := Empty`, so the
   asm/`-> never` half cannot live on it, and jointness demands ONE
   program. I built `divD`/`divP` mirroring `refD` (same table/lock shape,
   same F-run proof pattern) instead.
4. "A `-> never` function": in the model a `-> never` routine with an
   `asm` body IS an axiom (`Syntax.lean` §14), not a `Fn` — a `Fn` with
   `erg = some .never` cannot close its `Endblock` (no `ErgExpr` of
   `never`). The witness covers the axiom shape plus the `forever`-body
   `Fn` shape; this is the closest honest reading.
5. Deliberately uncovered: the tail-call-to-`never` shape (a plain call —
   its divergence is the callee's; no new lemma), and a G-machine reached
   run for `divP` (F-machine only, as in `ReferenzB`).

## Commits on `muse/231` (5)

Skeleton+§1, §2+§3 bridges, witness decl+run, witness+CUTS, this report.
Each committed green; `Grammatik.lean` import included.
