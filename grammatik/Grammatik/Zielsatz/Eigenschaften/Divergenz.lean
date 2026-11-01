/-
  File:    Grammatik/Zielsatz/Divergenz.lean -- divergence of accepted never-bodies.

  SCOPE (lane 231, TODO §-1 wave B, pure Lean). Lane 225 pinned the CHECKER
  acceptance of `-> never` bodies (asm with no `out`, un-leavable `forever`
  with `per_pass bounded` + diverging `on_exceeded`, tail calls) with zero
  behavior change. This file is the MODEL half for exactly those shapes,
  nothing wider: divergence PROVED from the declaration, never asserted.

  * §1 `forever`: a loop whose body cannot leave or return (`NoExit`) and
    whose invariant holds everywhere (`InvWahr`) ends in
    `hardware (fortschritt a)` at every budget -- the named `progress`
    assumption `a` the writer declared (the model's `on_exceeded` exit).
    Never `logik`, never a return value: it terminates-or-diverges as
    declared, and the divergence leg is proved.
  * §2 `asm`: a `-> never` foreign body (an axiom with `aerg = some .never`,
    Syntax.lean §14) has an empty answer class (`antwortLeer_never`), so no
    oracle answer fits and the call never continues: `hardware (annahme a)`
    with the oracle's declared-effects world. Never `logik`, never `ok`.
  * §3 `KeinLogikHaltG` at the spin (review G10 F3 of 2026-09-21, fix lane
    F8): a thread whose head is any state of the spin of
    `forever a invariant true {}` (`SpinKopf`: the `.ewig` head, the
    unfolded empty body, the `ewigRest`) passes EVERY clause of `PrueftG`
    (`spin_prueft`), i.e. the per-thread content of `KeinLogikHaltG`; plus
    the one-step fact `ewig_wahr_schreitet` (the `.ewig` head at budget
    `n + 1` takes its G step). `bindAxiom_kein_blatt` is a discrimination
    fact only (a call head is no leaf head), nothing about never-axioms.
    The leg's statement (`Spec.lean`) is untouched.
  * §4 witness: `divD`/`divP` (one table `konto`, one lock, a writer that
    writes then diverges in `forever`, a reader, a `-> never` axiom) with a
    reached F-machine run that changes memory and stands at the `forever`,
    and `divergent_body_zeuge` instantiating every premise JOINTLY.
    Non-degenerate: `konto[0]` goes `0 -> 100` on the run.

  No `sorry`, no `axiom`, no `native_decide`, no `unsafe`. No premise whose
  type is `Prop` itself. Every premise is used by its proof.
-/
module

public import Grammatik.Zielsatz.Eigenschaften.Divergenz.Teil1
public import Grammatik.Zielsatz.Eigenschaften.Divergenz.Teil2
