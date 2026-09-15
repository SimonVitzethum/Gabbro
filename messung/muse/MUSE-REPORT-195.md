# MUSE-REPORT-195 (lane 195, T3 round trip level 6, 2026-09-15)

## Task reconstruction (honest preamble)

The branch `muse/195` was fresh at the `master` tip with a clean tree;
no todo list survived the turn boundary, and no lane-195 assignment
exists anywhere in the repo (searched `TODO.md`, `DONE.md`, `README.md`,
`dokumente/PLAN.md`, all lane reports). So this lane picked its own
task: the next open item of MUSE-REPORT-172 "Open" that fits the
established one-green-commit-per-level pattern, and README §4 order of
work item 1 ("Finish the parser: generic, round-trip"):

> `alt` (`old`), `ergebnis`, `fnwert` (`&`-paths need segment acts),
> `grund` (`G::F` needs segment acts): single-constructor primaries,
> small, not started.

Statements (`SAnw`) are untouched -- NOT this lane.

## What I did

New file `grammatik/Grammatik/Parser/Rundlauf4.lean` (imported from
`grammatik/Grammatik.lean`), closing the expression round trip at
level 6: `gutPrim e = gutEmb e || primNeu e` with
`primNeu = altNeu || ergebnisNeu || fnwertNeu || grundNeu`, one new
layer over the previous predicate each, in the one-level pattern
(no nested list patterns -- MUSE-REPORT-172 finding 3):

- `altNeu`: `.alt x` over KERNEL places (`gutKernPlatz`, the
  `sizeof` precedent). `prim_alt_legs` mirrors lane 161's
  `prim_alt` with `R n` replaced by `ort_legs_kern` (no size
  bound needed anywhere), and `prim_emb1_legs` minus the
  type-word gate.
- `ergebnisNeu`: `.ergebnis`, no payload (lane 161's
  `prim_ergebnis` reused, fuel `X <= F+7` closed by `omega`
  against the Legs `X+1` bound).
- `fnwertNeu`: `.fnwert p`, no tree payload. `primFrei` is
  false, so there is no primary leg: `un_fnwert_legs` proves
  the `parseUnary` `&` arm directly (name, `sammleSeg_stop`
  under `ruhigSuff`, singleton intercalate back to the name).
- `grundNeu`: `.grund g f` with exactly `gut`'s side
  conditions (lane 161's `prim_grund` reused).

Two shared builders generalise lane 179's `embTower` (whose head
is always `wort`): `wortTurm` (`.wort` head: `old`, `result`)
and `identTurm` (`.ident` head: `grund`) -- each a `parseUnary`
fall-through plus `tower_up`. `fnwertLegs` towers from the
unary leg directly; its primary component is vacuous
(`simp [primFrei] at hpf`).

Goal `parse_druck_prim`, four layer bridges into `gut`
(`gut_of_gutPrim`), eight witnesses: `old(BESITZER)`
(`35-tausch`), `result` (`06-annahmen` ensures), `&hart_senden`
(`111-rufzulassung`), each as a `parse_druck_prim` instance
(`by decide`) plus a kernel-computed `match` check. No
two-segment `G::F` occurs in the corpus -- three-segment paths
lower to field chains via `grundKette` -- so the `grund`
witness `.grund "T" "x"` is neutrally named, and says so.

## New definitions/theorems

All in `grammatik/Grammatik/Parser/Rundlauf4.lean`
(`Gabbro.Grammatik.Parser`): `altNeu`, `ergebnisNeu`,
`fnwertNeu`, `grundNeu`, `primNeu`, `gutPrim`;
`prim_alt_legs`, `un_fnwert_legs`; `wortTurm`, `identTurm`;
`altLegs`, `ergebnisLegs`, `fnwertLegs`, `grundLegs`;
`legsAlt`, `legsErgebnis`, `legsFnwert`, `legsGrund`,
`legsPrimNeu`, `legsPrim`; `parse_druck_prim`;
`gut_of_altNeu`, `gut_of_ergebnisNeu`, `gut_of_fnwertNeu`,
`gut_of_grundNeu`, `gut_of_gutPrim`; `zeuge_alt[_rech]`,
`zeuge_ergebnis[_rech]`, `zeuge_fnwert[_rech]`,
`zeuge_grund[_rech]`.

`#print axioms` on `parse_druck_prim`, `gut_of_gutPrim`,
`legsPrim`: `[propext, Classical.choice, Quot.sound]` only.
No `sorry`/`admit`/`axiom` in the file (grep: zero hits).

## Gates and guardians

- Base measured first: `./lean-bau` exit 0, 230 jobs,
  "Build completed successfully" -- before any change.
- `./lean-probe` on the new file per piece: exit 0, 0 errors
  (four probe rounds; two failures seen and repaired -- see
  findings).
- Final `./lean-bau`: exit 0, 0 errors, "Build completed
  successfully" (231 jobs: 230 + `Grammatik.Parser.Rundlauf4`).
- `./cargo-pruef` NOT run, deliberately: zero Rust, corpus,
  gift, emitter, or instrument delta (`git status`: one new
  Lean file + one import line), so there is nothing it could
  measure that the base run did not. Same doctrine as lane 193
  (reviewer lane: Lean gate only). `./emission-pruef` not
  touched for the same reason, squared (emitter untouched).
- No guardian-visible number moves: no Rust sentences, no new
  diagnostics, no corpus/gift/mutation/instrument changes, no
  TODO/DONE/README edits. Nothing rebooked.

## Findings (Lean-specific, measured)

1. A flattened four-pattern `obtain ⟨a,b,c,d⟩` over a
   left-nested `((A∧B)∧C)∧D` MISFIRES when the last component
   carries `!` (`Bool.not`): `cases` attempts dependent
   elimination on `true = (!strEq g "Self")` and fails at
   `Eq.refl`. Stepwise `obtain` (`⟨hABC,hself⟩`, `⟨hAB,hzuk⟩`,
   `⟨hkp,hit⟩`) works. Seen in `legsGrund`, documented in
   `gut_of_grundNeu`. (MUSE-REPORT-172 finding 4 was the
   `obtain`-clears-target trap; this is its four-conjunct
   sibling.)
2. `apply wortTurm _ _ _ hd` mis-orders: with `{S}` implicit
   the explicit args are `(w) (e) (hd)`, so it is
   `apply wortTurm _ _ hd` -- the extra wildcard silently ate
   the primary-leg goal and left `⊢ String`.
3. `simp` alone closes the singleton intercalate
   (`"::".intercalate [p] = p`) after the `sammleSeg_stop`
   rewrite -- no lemma needed.

## What stays open (exact)

- `alt` covers KERNEL places only (`gutKernPlatz`; index
  payloads `gutKern`). Full `gutPlatz` payloads carry
  arbitrary `gut` index expressions.
- Arbitrary NESTING of new operators over each other (e.g.
  `==` over `&`) still needs the joint size induction over a
  recursive predicate (Rundlauf3 header: replay lane 172's
  architecture, ~500 lines). Unchanged by this lane.
- Statements (`SAnw`, task item 4): untouched.
- The five `gutPrim`-visible corollaries nobody has asked
  for yet: print/parse round trip at statement level, the
  generic lowering (`UebersetzeAllg2`) over primaries, and
  T2/T4/T5 follow-ons.
