/-
  File:      Grammatik/Gen/Text/Invers/Ausdruck.lean
  Subject:   THE ELABORATOR INVERTS THE DELABORATOR ON EXPRESSIONS (Tier 2.1, step 1), generically: for every
             expression `e` of the generator's declaration that the delaborator prints as `s`, the elaborator's
             readers give back the plain data `uOfS`/`uOfB`/`uOfIdx` computes from `e` itself --
             `uSeite ctx s` and `uWertBody ctx s` the side `uOfS e` (a number), `uSichert ctx s` the predicate
             `uOfB e` (a truth value), `uIndex` the index `uOfIdx e`.

  The context `ctx` is described by `EInv` against the accessors of the declaration (`D.count`, `D.typ`,
  `D.gtyp`, `darf`), not against how the generator builds it: the variable printed for depth `d` is found at
  a position whose kind is `art d`, every body name is a `v{k}` or a `p{k}`, the tables and statics are found
  under their printed names with the declared counts and types, and every table the expression may read
  (`darf`) has its guards held.

  `uOfS`/`uOfB` are partial (`none`) exactly where the elaborator has no reading of the printed form: a literal
  index outside the table, an index variable of another table, a `bool` result inside an `ensures` (the
  elaborator reads `result` only as a number), and every form the delaborator does not print.
-/
module

public import Grammatik.Gen.Text.Invers.Ausdruck.Teil1
public import Grammatik.Gen.Text.Invers.Ausdruck.Teil2
public import Grammatik.Gen.Text.Invers.Ausdruck.Teil3
