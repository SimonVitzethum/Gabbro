# MUSE-REPORT-101 (lane 101, D7: contract footprint containment by computation)

## What was done

New file `grammatik/Grammatik/VertragsFuss.lean` (registered in
`grammatik/Grammatik.lean`), closing the checker-computation half of D7:

- `fussDeckt (f : D.Fn) (o : D.Tab ⊕ D.Glob) : Bool` — one carrier covered
  by the write signature (`D.schreibt` / `D.gschreibt`).
- `vertragFussB (P : Programm D) (f : D.Fn) : Bool` — conjunction of
  `List.all (fussDeckt f)` over `(P.requires f).orte` and `(P.ensures f).orte`.
  Decidable for every declaration; needs no `DecidableEq` (no membership test).
- `vertragFussB_req` / `vertragFussB_ens` — the per-function legs (tables and
  globals jointly) from one positive check, via `List.all_eq_true`.
- Four target theorems with the exact `Ziel.lean:2359-2366` conclusion shapes:
  `hReqTAll_aus_B`, `hReqGAll_aus_B`, `hEnsTAll_aus_B`, `hEnsGAll_aus_B`, each of
  the form `(hB : ∀ f, vertragFussB P f = true) → <exact premise shape>` over an
  explicit `(Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)`.
  Every premise is used (single-use `hB (J.code g)`).
- Evidence facts on the reference fixture, both `by decide`:
  `vertragFussB_refEin : vertragFussB refP refEin = true`,
  `vertragFussB_refLies_falsch : vertragFussB refP refLies = false`.
- `CUTS` block + `#print axioms` for every definition/theorem (all
  `[propext, Classical.choice, Quot.sound]`, no `sorryAx`). No new
  diagnostic codes, probe numbers, or example numbers were added.

## Last `./lean-bau` result

`Build completed successfully (54 jobs).` — whole project green, including the
new file. `./lean-probe grammatik/Grammatik/VertragsFuss.lean` reports
`0 error(s)`.

## What remains open / the finding (rule 13)

There is NO `hReqTAll_aus_B_zeuge`, deliberately. The ZEUGE premise
`∀ f, vertragFussB refP f = true` is FALSE on `refP`, proved by computation:
`lies` (`false`) ensures `result = konto[0]` (`refEnsLies`, footprint
`[.inl ()]`) while its write signature is empty
(`refSigLies.schreibt = fun _ => false`). Hence `vertragFussB refP refLies`
evaluates to `false` and no joint witness exists. Per rule 13 this is reported
as a finding, not worked around: the witness was not weakened (e.g. to
`einzahlen` only) and no `_zeuge` companion is claimed.

Consequence for D7: write-signature containment as stated excludes ordinary
read contracts — a read-only function whose `ensures` names the table it reads
can never satisfy `hEnsTAll`. The four premises are jointly unsatisfiable on
the reference fixture itself (`refB_erreicht` runs `einzahlen`+`lies`). The
checker half built here is sound, but the rule it decides would reject `refP`.
The natural repair is containment in a read-or-write footprint rather than the
write signature alone; that changes the target statement, so it is proposed
here, not proved.

## Rust checker status (as tasked)

Not enforced. Measured by grep: `crates/gabbro-check/src/wirkungen.rs`
collects expression reads (`liest`, `liest_expr`) but never mentions
`requires`/`ensures` (zero hits); footprints (`bau.rs`, `fussAus`) are computed
from the declared `writes` effects only; `zeremonie.rs` checks `requires` only
for duplication/range-shape (`R2`/`R4`/`T3`-family), never for carrier
coverage. Smallest rule that would close it: refuse a function whose
`requires`/`ensures` reads a carrier outside its declared write effects
(unnumbered — this lane was assigned no code range and adds none).

## What I believe is wrong in the task

The witness hint (`refP`, `Bool by decide`) assumes the joint check passes on
the fixture; `decide` instead proves its negation for `lies`. The task is still
completable exactly as specified (all four soundness theorems proved
unmodified), but the ZEUGE line is uninhabitable — which is itself the most
informative output of this lane.
