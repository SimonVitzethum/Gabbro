# MUSE-REPORT-02: Contracts at their place (attempt B)

## What I did

New file `grammatik/Grammatik/VertragOrtB.lean`, wired via
`import Grammatik.VertragOrtB` at the end of `grammatik/Grammatik.lean`.
No existing file was modified except that one import line; no existing
definition or theorem was touched. `./lean-bau` is green
(`Build completed successfully (30 jobs)`).

## Design (why this shape)

- The task asks for call entry/return with the ACTUAL `rho`/`v`, evaluated
  at their place. `Extraktion.QRequires`/`QEnsures` quantify over all `rho`
  and all `v`, so parameter/result-mentioning contracts die as world
  predicates. The fix must carry the actual values in the EVENT, not in a
  world predicate.
- Import constraint discovered while working: `Extraktion.lean` imports
  `Maschine.lean`, so a new file importing both would cycle back into
  `Grammatik.lean`. `VertragOrtB.lean` therefore imports only
  `Grammatik.Semantik` (+ `Grammatik.Wettlauf` for `Faden`) and mirrors the
  two shapes it needs: `ContrAtom` (leaf/take/rel like `PCAtom`, plus
  `eintritt f` / `rueck f`) and `QEnsuresB` (same quantifiers as `QEnsures`).
- Hard-won Lean facts recorded here so the next attempt does not re-pay them:
  (a) `Faden` lives in `Wettlauf.lean`, not `Semantik.lean` (missing import
  gives "universe level metavariables" on the structure); (b) field name
  `nach` collides with `Syntax.nach`, so the step field is `nachW`;
  (c) `Deklaration.Fn` is opaque: `show miniContrD.Fn from true` works in
  TERMS, and `cases f` on `f : miniContrD.Fn` splits into `true/false`
  (used in `miniContrD_erg`/`miniContrD_params`); (d) `.eq` does not unify
  its two sides' ranges, so every `.weiter` target range must be annotated;
  (e) `.add` computes its result range (`0..5 + 1..1 = 1..6`), so the
  ensures compares in `.int 0 6` after widening both sides; (f) `▸`-casts
  inside `Expr` definitions block `rfl`-evaluation -- define expressions
  against contexts the elaborator accepts directly.

## New definitions / theorems (all in `Gabbro.Grammatik`)

- `ContrAtom D`: leaf/take/rel + `eintritt f` / `rueck f` (PC extension
  without modifying `PCAtom`).
- `ContrEvent D`: `eintritt f rho` (actual env); `rueck f rho v s0`
  (actual env, actual result, entry-side read world for `old(..)`).
- `ContrSchritt D` / `ContrLauf D`: wrapper steps (thread, pre/post worlds,
  optional event) over per-thread atom lists; `contrProjRegel`: event-free
  steps fire non-contract atoms.
- `ReqAmEintritt`, `EnsAmRueck`: requires/ensures evaluated with the actual
  `rho`/`v` at entry/return worlds.
- `QEnsuresB`: local restatement of the `QEnsures` quantifier shape.
- `VertragAmOrtB P L`: every entry event satisfies requires at its place,
  every return event satisfies ensures at its place.
- `vertragAmOrtB_leer`, `vertragAmOrtB_of_singleton`: empty/singleton runs.
- `ensAmRueck_gibt_qensures_pkt`: place-check equals the quantified check
  at the same values when `s0 = sigma`.
- Mini example (`miniContrD` over `Bool` fn ids, one `.int 0 5` param,
  `.int 0 5` result; `ensures := ret == param + 1` in `.int 0 6`):
  `mini_req_am_ort`, `mini_ens_am_ort`, `miniContrLauf` (one return step
  with param 2, result 3), `mini_vertrag_am_ort` (place contract holds),
  `mini_qensures_falsch` (`QEnsuresB` false, witness result 0).
- Bridge: `RufEnsCheck`, `rufAt_ok_of_gates` (derives the `rufAt ... = .ok`
  equation from the requires gate + body outcome + ensures check +
  invariant tail, by `simp only [rufAt, ...]` -- every premise is rewritten),
  `rueck_ohne_nachbedingung_iff` (return event with satisfied ensures ⟹
  `rufAt` never answers `Logik.nachbedingung f`).

## Last `./lean-bau` result line

`Build completed successfully (30 jobs).` Every `#print axioms` in the new
file reports only `[propext, Classical.choice, Quot.sound]` -- no `sorryAx`,
no axioms beyond the project baseline.

## What remains open (also listed as `CUTS:` in the file)

1. The bridge proves one direction (satisfied ensures + `.ok` equation ⟹
   no `nachbedingung`); the converse (from `rufAt ≠ .logik nachbedingung`
   to the ensures check) is not proved.
2. No `PCReach`/`GenErreichbar` wiring: the wrapper projects to plain atom
   lists, not to `PCSchritt` derivations (import cycle, see above). A
   follow-up in a file that MAY import `Maschine.lean` (i.e. placed after
   it, not before `Extraktion.lean`) could identify `ContrAtom`
   leaf/take/rel with `PCAtom` and route `contrProjRegel` into real steps.

## What I believe is wrong in the task

- Item 4 asks for "exactly the case where `rufAt` does NOT produce
  `Logik.nachbedingung f`" -- a genuine iff. The forward direction (event
  satisfies ensures ⟹ no nachbedingung) needs the `.ok` equation, which
  itself needs the requires gate, the body outcome, AND the invariant tail
  (`rufAt_ok_of_gates`). The backward direction additionally needs
  determinism/inversion of the `rufAt` branches. Stating it as a bare
  "return event ⟺ no nachbedingung" without the gate/body/invariant
  premises would be false (a failing requires also avoids nachbedingung
  via vorbedingung). My lemma keeps those premises explicit; dropping them
  to look like a cleaner iff would be exactly the kind of weaker-than-asked
  result the hard rules warn about.
- "Extend the PC machine WITHOUT modifying existing definitions (a new atom
  kind or a parallel wrapper structure is fine)": the parallel wrapper is
  the only option that keeps `./lean-bau` green, because `PCSchritt`'s
  constructors pin the three atom kinds and `Extraktion.lean` already
  imports `Maschine.lean`. A "new atom kind" inside the PC machine would
  require editing `PCAtom` itself.
