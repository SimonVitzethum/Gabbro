/-
  File:      Grammatik/RufOhneHardware.lean
  Subject:   WHEN A CALL CANNOT END IN A HARDWARE OUTCOME -- the syntactic
             check `hardwareFrei` and its soundness, and the consequence for
             `rufAt` at every depth.

  The model knows exactly two error outcomes (`Semantik.lean`): the writer's
  logic (`Logik`) and an assumption about the machine (`Hardware`). The
  second one has FIVE sources, and every one of them is a syntactic form:

  * `Stmt.axiomCall` / `Block.bindAxiom` -- the axiom's raw answer does not
    fit its declared result type (`Hardware.annahme`);
  * `Block.regLies` -- the register's raw answer does not fit its declared
    type (`Hardware.register`) or breaks its declared promise
    (`Hardware.geraet`); `Block.regLiesElse` -- the type half of the same;
  * `Block.awaits` -- the memory model did not show the publication
    (`Hardware.sichtbarkeit`, A10);
  * `Stmt.forever` -- the environment's budget ran out
    (`Hardware.fortschritt`, H2).

  `Hardware.ieee` is no longer produced at all (verdict F1, 2026-09-15: an
  out-of-range float result is `Logik.bereich`).

  A body that carries none of those five forms therefore cannot end in a
  `hardware` outcome, against any handler that answers none either
  (`Endblock.hardwareFrei_ok`, the twin of `Endblock.logikFrei_ok` in
  `ZielOrtGanz.lean`). Since `rufAt`'s own error branches are all `logik`
  (`vorbedingung`, `nachbedingung`, `invariante`, `abstieg`), the handler
  premise carries itself by induction on the DEPTH: for a program all of
  whose bodies pass the check, `rufAt` never ends in `hardware`, at any
  depth, from any world, with any arguments (`rufAt_ohneHardware`).

  WHY IT MATTERS. A statement about a call that carries the condition "the Gabbro call ends
  in no model error" (the closing theorem of the deleted C chain did) meets this. Neither
  the checker's Bool nor the user's duty says anything about the `hardware`
  half: `HardwareAnnahmen` (Zielsatz/Spec.lean (c)) is CONDITIONAL -- it
  constrains the oracle only *where* the raw answer fits the declared type --
  and `KoerperGutS` speaks about `logik` outcomes only. So the `hardware`
  half of the condition is not discharged by the goal theorem's premises,
  and it is discharged HERE, syntactically, for every program whose bodies
  carry no oracle form (the check `hardwareFrei`).
-/
module

public import Grammatik.Logik.Ruf.Ohne.RufOhneHardware.Teil1
public import Grammatik.Logik.Ruf.Ohne.RufOhneHardware.Teil2
