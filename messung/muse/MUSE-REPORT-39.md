# MUSE-REPORT-39: The rufAt postcondition equivalence (attempt B of 2)

Lane 39. New file `grammatik/Grammatik/RufAtNachB.lean`, wired via
`import Grammatik.RufAtNachB` at the end of `grammatik/Grammatik.lean`.
No existing file modified except that one import line; no existing
definition or theorem touched.

## What I did

- Read `dokumente/SATZKARTE.md`, `messung/muse/MUSE-REPORT-02.md`
  (lane 2 / VertragOrtB design, including its failed-iff analysis),
  `grammatik/Grammatik/VertragOrtB.lean` (the `rufAt_ok_of_gates` proof
  to mirror), and `grammatik/Grammatik/Semantik.lean` (`rufAt` at
  lines 768-786, `EndAusgang`/`RufAusgang`, `execEnd`).
- Committed in small pieces: skeleton (`rufAt_fall_nach` only), then the
  iff, then the corollary plus CUTS update, then the import wiring.
  Each piece checked with `./lean-probe` (0 errors) before proceeding.

## New definitions / theorems (all in `Gabbro.Grammatik`, file `RufAtNachB.lean`)

- `rufAt_fall_nach` (helper, proved by unfolding `rufAt` exactly as
  `rufAt_ok_of_gates` does, plus `if_neg` on the open requires gate):
  with the body outcome equation, requires gate open, and invariant tail
  passing, `rufAt ... (fuel+1) f σ ρ` equals the ensures `if` over the
  actual `v`.
- `rufAt_nachbedingung_iff_ensFalsch` (TARGET): with the same shapes as
  `rufAt_ok_of_gates` (`hread`/`hreq` requires gate, `hbody` body-outcome
  equation `execEnd ... = EndAusgang.zurueck σ1 v`, `hret` return read
  world, `hsinv`/`hinv` invariant tail),
  `rufAt P O passes (fuel+1) f σ ρ = .logik (.nachbedingung f)`
  iff `wahr? (eval sread (P.ensures f) sret (ergEnv (D.erg f) v ρ)) = false`.
  Forward: rewrite with `rufAt_fall_nach`, case on the check, close the
  `.ok`-against-`.logik` case by constructor discrimination. Backward:
  `if_pos`.
- `rufAt_nie_nachbedingung_iff_ens` (corollary): with the same shapes,
  `rufAt ... ≠ .logik (.nachbedingung f)` iff
  `RufEnsCheck P f sread sret ρ v` (imported from `VertragOrtB`, not
  duplicated). Proved from the iff by negation on both sides.
- Design notes: the body outcome is an EQUATION keeping the actual `v`
  (avoiding attempt A's mistake of recovering `v` from a `some` world);
  no contract parameter/result is quantified away (contracts hold at
  entry/return with the actual `ρ`/`v`); worlds come from `execEnd`
  (via `execStmt`, can change memory) and `World.lese`; every premise
  feeds the `rufAt_fall_nach` rewrite or the iff/corollary it builds on
  (no `intro _`, no unused `have`); no `sorry`/`admit`/`axiom`/
  `native_decide`/`unsafe`; no premise of type `Prop` itself.
- File ends with a `CUTS:` comment block and three `#print axioms` lines.

## Last `./lean-bau` result line

`Build completed successfully (34 jobs).`
All three `#print axioms` report only `[propext, Classical.choice,
Quot.sound]` -- project baseline, no `sorryAx`.

## What remains open (also listed as `CUTS:` in the file)

- Scope is the returned-body case only: `hbody` pins the `.zurueck`
  outcome. Non-returning bodies (`.grund`, `.logik`, `.hardware`) are
  excluded by that equation, not by an unused premise: `rufAt` forwards
  them unchanged past the postcondition gate, so no equivalence of this
  shape holds for them. This is a use-site obligation (callers must
  supply `hbody`), not a gap in the proof.

## Anything in the task I believe is wrong

- Nothing material. The task's warning about attempt A's failure mode
  (deriving `.zurueck σb v` from `.welt = some σb`) was accurate and
  avoidable by taking `hbody` as an equation -- which is what the target
  statement does. The "False-shaped" phrasing of the target was
  elaborated as `... = false` on the same `wahr? (eval ...)` term that
  `rufAt` itself tests (Semantik.lean:776), i.e. elaboration detail only,
  per rule 12.
