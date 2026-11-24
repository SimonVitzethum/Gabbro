/-
  File:      Core/Beobachtung/Wahrscheinlichkeit/Unentscheidbar.lean
  Subject:   Undecidability of every probability remainder outside the checker
    fragment (owner rule 2026-11-24, B11(c)(d), M9P).

  The four checker forms (`ProbKlausel`/`pruefeProb` in `Form.lean`) decide their
  finite fragment by construction: a `Bool` function over finite clause data.
  Everything beyond the fragment — arbitrary run events over infinite state,
  arbitrary expected costs, a.s. termination/progress of arbitrary loops, and the
  two cryptographic forms in full — is a GabbroProve user duty, and no checker
  decides it. Each pinned `…UnentscheidbarAussage` below states the corresponding
  `¬ ComputablePred` over `Nat.Partrec.Code`, with a precise proof sketch.

  The sketches share one missing generic premise, `gabbroSimuliertPartrec`:
  every `Nat.Partrec.Code` is simulated by a Gabbro unit whose observable run
  behaviour (termination on input, reached event, step cost) coincides with the
  code's evaluation. Until that simulation statement is proved, the transfer from
  the partrec core (provable from `ComputablePred.halting_problem`, in places
  `ComputablePred.rice₂`) to "no checker decides the Gabbro remainder" is future
  work; the partrec cores themselves are stated in provable form.

  `planned.probability.draw` needs no such proof: it is decided by finite
  catalogue-row lookup (B11(d)), hence a checker rule by construction.
-/
module

import Mathlib.Computability.Halting
public import Mathlib.Computability.RE

@[expose] public section

namespace Gabbro.Core.Beobachtung

/-- `planned.probability.event` remainder (arbitrary run events over infinite
    state): no checker decides the exact bound.
    Difficulty: partrec core now, Gabbro transfer after the missing simulation.
    Sketch: embed `c` deterministically (`gabbroSimuliertPartrec`), so the run
    event "the embedded computation halts" has probability `1` if `c` halts on
    `0` and `0` otherwise; deciding `Pr ≥ 1 / 2` would decide halting. The
    partrec core is exactly `ComputablePred.halting_problem 0`. -/
def prEreignisUnentscheidbarAussage : Prop :=
  ¬ ComputablePred fun c : Nat.Partrec.Code => (Nat.Partrec.Code.eval c 0).Dom

/-- `planned.probability.cost` remainder (arbitrary expected costs): no checker
    decides the bound.
    Difficulty: partrec core now, Gabbro transfer after the missing simulation.
    Sketch: embed `c` with cost `0` if it halts on `0` and `⊤` otherwise
    (divergence is infinite cost); deciding `E ≤ 0` would decide halting. The
    partrec core is exactly `ComputablePred.halting_problem 0`. -/
def kostenErwartungUnentscheidbarAussage : Prop :=
  ¬ ComputablePred fun c : Nat.Partrec.Code => (Nat.Partrec.Code.eval c 0).Dom

/-- `planned.probability.termination` remainder (arbitrary loops): no checker
    decides a.s. termination.
    Difficulty: partrec core now, Gabbro transfer after the missing simulation.
    Sketch: embed `c` as the loop body over all inputs; the loop terminates a.s.
    on every input iff `c` is total. Totality is undecidable: if it were
    decidable, halting on `0` would be decidable (input-fixing construction on
    codes), contra `ComputablePred.halting_problem 0`. -/
def fastSicherAbschlussUnentscheidbarAussage : Prop :=
  ¬ ComputablePred fun c : Nat.Partrec.Code =>
    ∀ n, (Nat.Partrec.Code.eval c n).Dom

/-- `planned.probability.progress` remainder (arbitrary retries): no checker
    decides a.s. progress.
    Difficulty: partrec core now, Gabbro transfer after the missing simulation.
    Sketch: embed `c` so one retry succeeds iff `c` halts on `0`; deciding
    eventual success with probability `1` would decide halting. The partrec core
    is exactly `ComputablePred.halting_problem 0`. -/
def fastSicherFortschrittUnentscheidbarAussage : Prop :=
  ¬ ComputablePred fun c : Nat.Partrec.Code => (Nat.Partrec.Code.eval c 0).Dom

/-- `planned.probability.informationTheoretic` (whole form): no checker decides
    the bound over every adversary.
    Difficulty: partrec core now, Gabbro transfer after the missing simulation.
    Sketch: adversaries are arbitrary strategies, hence in particular the
    embedded codes; separate by a scheme whose advantage reaches the bound iff
    the embedded code halts on some input. Existential halting is undecidable
    (input-existentialization reduces halting on `0`), contra
    `ComputablePred.halting_problem 0` (equivalently via `ComputablePred.rice₂`:
    the range property is extensional and nontrivial). -/
def infoTheoretischUnentscheidbarAussage : Prop :=
  ¬ ComputablePred fun c : Nat.Partrec.Code =>
    ∃ n, (Nat.Partrec.Code.eval c n).Dom

/-- `planned.probability.reduction` remainder (arbitrary schemes/adversaries):
    no checker decides the inequality.
    Difficulty: partrec core now, Gabbro transfer after the missing simulation.
    Sketch: fix a separating scheme and reduction with vanishing primitive term
    whose scheme advantage is `1` iff the embedded adversary code halts on `0`;
    the inequality with suitable factor then holds iff `c` diverges. Deciding it
    would decide halting. The partrec core is exactly
    `ComputablePred.halting_problem 0`. The primitive's hardness stays a named
    assumption; the undecidable part is the inequality over arbitrary
    adversaries. -/
def reduktionUnentscheidbarAussage : Prop :=
  ¬ ComputablePred fun c : Nat.Partrec.Code => (Nat.Partrec.Code.eval c 0).Dom

end Gabbro.Core.Beobachtung
