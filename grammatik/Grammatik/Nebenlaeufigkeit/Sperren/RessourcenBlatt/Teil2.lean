module

public import Grammatik.Kern.Semantik.Maschine
public import Grammatik.Kern.Syntax.Extraktion
public import Grammatik.Nebenlaeufigkeit.Sperren.RessourcenBlatt.Teil2Slots

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}


/-! ## 5. The main theorem: CUT -- the target is false for `axiomCall`

    The fixed target `csl_ressourceninvarianteC` is recorded in
    `MUSE-REPORT-54.md`, not proved here. Finding: `Stmt.axiomCall`
    (Semantik.lean:617) answers with the oracle world `O.wirkt a σ ρ`,
    which may change `t`'s slots while recording NO access event (the
    trace may even be unchanged); `GutO` enforces only the declared
    frame, not the guard. The leaf branch of the `PCReach` induction
    owes `hax` (non-oracle shape) for the fired statement, underivable
    for `axiomCall` -- and slot preservation is genuinely false there.
    Per rule 12, a variant with an added no-oracle premise is future
    work; per rule 13 no `_zeuge` is owed for a cut theorem. -/
/- Target cut: fixed statement and model finding recorded in MUSE-REPORT-54.md. -/

end Gabbro.Grammatik
