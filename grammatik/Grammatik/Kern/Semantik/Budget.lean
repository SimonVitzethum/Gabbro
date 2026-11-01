/-
  File:       Grammatik/Budget.lean
  Subject:    Ops-budget accounting is sound: a declared per-pass bound is
              respected by execution.

  Claim (in one sentence):
    Steps whose total cost fits the declared per-pass bound execute and report
    the leftover; steps whose total cost exceeds the bound stop with an
    EXPLICIT budget outcome that names the pass -- never with a silent
    overrun.

  Mapping to the declared surface (`SYNTAX.md` §18, fourth version):
    `costs`          -- `Op.cost`: the declared cost of one primitive step.
                       A number the declaration trusts, not one measured here
                       (premise P1).
    `per_pass N ops` -- `Budget.perPass = N`: a FRESH bound of `N` ops for EACH
                       pass. `ops` is `totalCost`, the summed step costs on the
                       Gabbro side.
    stuck-with-name  -- `BudgetOut.budget name needed bound`: the explicit
                       outcome. For one pass the name is the syntactic form
                       `"per_pass.ops"`; over several passes it is the failing
                       pass's own name.

  Deliberately OUTSIDE (decision, not omission):
    Wall-clock time, cycles, and deadlines never enter this file. Per
    `Ziel.lean` the budget counts Gabbro-side steps only; a deadline is the
    hardware assumption `fortschritt` with its probe (`fristAlsAnnahme`),
    measured by the probe and never proved here. There is no `Time` type
    below, and that absence is the statement.

  Proven below (`#print axioms` at the end shows each rests on no axioms):
    `runOps_within`        -- within bound: execution reports the exact leftover.
    `runOps_exceeds`       -- over bound: execution reports the named budget outcome.
    `runOps_no_silent`     -- no silent overrun: `ok` implies within bound.
    `runOps_exhaustive`    -- no third outcome: every run is `ok` or `budget`.
    `runPass_within`       -- the same three through one fresh per-pass budget.
    `runPass_exceeds`
    `runPass_no_silent`
    `runPasses_all_within` -- `ok` over passes implies EVERY pass was within bound.
    `runPasses_complete`   -- every pass within bound implies `ok`.
    `runPasses_exceeds`    -- one pass over bound implies the named budget outcome.
    `per_pass_respected`   -- the umbrella: either all passes ran within bound,
                              or the run names the pass that did not.
    `held_respected_gilt`    -- the `held <= K` umbrella, through `per_pass_respected`.
    `bounded_respected_gilt` -- the `bounded N` umbrella, through `per_pass_respected`.
    `seqPasses_complete`   -- every sequence element within bound implies `ok`.
    `seqPasses_exceeds`    -- one element over bound implies the named outcome.
    `senkKosten_modell`      -- a modeled lowering head costs exactly one C-side op.
    `senkKosten_unter_schranke` -- that one op fits under the measured maximum.
    `modell_erhaltung`       -- preservation for the modeled ops: a valid print
                               elaborates (meaning, reused) AND fits the max
                               (count, new).
    `modell_lauf_erhalten`   -- over modeled runs the lowered count IS the source
                                count: one op in, one op out.
    `fremdOp_kosten`         -- a foreign edge costs declared plus one dispatch step.
    `fremd_kein_null`        -- no zero slip: a foreign edge costs at least one op.
    `fremd_totalCost`        -- a lone foreign edge totals to declared plus one.
    `runOps_fremd_within`    -- a foreign edge within bound reports the exact leftover.
    `runOps_fremd_exceeds`   -- a foreign edge over bound names the budget outcome.
    `budget_erhaltung_fremd` -- preservation over foreign calls, through `runPass_within`.

  Premises (trusted, not proved):
    P1  Declared costs are faithful: `Op.cost` is the cost the declaration
        attributes to the primitive. No measurement against the emitter.
    P2  Fresh budget per pass: each pass starts at the full `perPass` bound;
        leftover does not carry across passes, overrun does not accumulate.
    P3  Addition on `Nat` counts steps: `totalCost` sums the declared costs.

  Cuts (booked, not hidden):
    C1  The interpreter is abstract: `runOps`/`runPasses` range over op lists,
        not over an instrumentation of `Semantik.exec`. There is NO verified
        link from a `Stmt`/`Block` to its op list; threading a budget through
        `execStmt`/`execBlock` is cut, not faked.
    C2  `held <=` and `bounded` are budget forms, exhaustion outcomes, and
        run/umbrella shapes beside `per_pass` (defs reusing
        `runPass`/`runPasses_*`); the umbrellas are proved
        (`held_respected_gilt`, `bounded_respected_gilt` through
        `per_pass_respected`). No link to `Semantik.exec`.
    C3  No preservation claim across lowering: nothing about C forms,
        quantitative CompCert, or the probe. Same boundary as `Ziel.lean`.
        NARROWED 2026-09-11 for the seven modeled heads (CUT-1/2): the
        appendix `Lowering preservation for the modeled ops` below proves
        the count leg beside the reused `zeugnis_sound` meaning leg, over
        the measured maximum; the remainder named there stays cut.
    C4  Not wired into `Grammatik.lean`: lane scope forbids the index edit;
        check this file directly with `lake env lean Grammatik/Budget.lean`.
    C5  Statement threading is shapes only (`SeqElem`/`seqPasses` below): the
        op list of an element is a DECLARED assignment (P1 lifted to
        statements), resource threading (`Λ` into `Λ'`) between elements is
        not tracked, and there is NO link to `Semantik.execStmt`/`execBlock`.
        Closing that link needs `Semantik` changes and stays booked here, not
        faked.

  No `mathlib`, no `sorry`, no `axiom`.
-/
module

public import Grammatik.Kern.Semantik.Budget.Teil1
public import Grammatik.Kern.Semantik.Budget.Teil2
