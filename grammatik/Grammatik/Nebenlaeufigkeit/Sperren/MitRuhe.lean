/-
  File:      Grammatik/MitRuhe.lean
  Subject:   THE RUNTIME'S IDLE ROOT, GENERICALLY -- `D.mitRuhe` is `D`
             plus one function `none` (the runtime's idle function: body
             `return`, empty signature, no locks, no reasons, writes
             nothing), and `P.mitRuhe` is `P` over it. DEFINITIONS only
             (part of the review package of `Zielsatz/Spec.lean`).

  Why: machine G starts EVERY thread of `Faden = Nat` in some function.
  A program without an idle function (the export of `beispiele/104`,
  probes B/C) has no admissible start at all, and a goal statement over
  its machine says nothing. The runtime supplies the idle root; `GabbroZiel`
  runs the machine of `P.mitRuhe` (assumption A4).

  THE ENCODING. `Fn := Option D.Fn`; `some f` is `f`, `none` is the root.
  Signature numbers shift by one: `some f` has number `D.sig f + 1`, the
  root has `0`, and `sigNr (n + 1)` is `D.sigNr n` with its types shifted
  (`sigR`). Function-pointer types shift with them (`tyR`: `fnptr n` ↦
  `fnptr (n + 1)`, every other type unchanged), so a value of a shifted type
  is a value of the original type (`valR`/`valZ`, inverse to each other: the
  root has number `0`, which no shifted type names -- no value of `P.mitRuhe`
  ever points to the root). Every other field of `D` is kept; field, global,
  axiom and register types are shifted. Resources, events, worlds,
  environments and memories carry over (`resR`, `evR`, `worldR`, `envR`,
  `speicherR`, with inverses), and so do oracles (`Orakel.mitRuhe`) and lock
  invariant families (`SperrInv.mitRuhe`).

  THE PROGRAM. `P.mitRuhe` translates every body, `requires`, `ensures`
  and invariant of `P` constructor by constructor (`ruE`, `ruS`, `ruB`,
  `ruEnd`, ...): `f ↦ some f`, `fnptr n ↦ fnptr (n + 1)`, everything else
  the same constructor. Where a typing index is equal only propositionally
  (the holdings after a call, `nach`; after `advances`/`retires`; the
  holdings at entry and at return), the term is transported along the
  equation (`Stmt.nachΛ`, `Block.vorΛ`, `Endblock.umΛ`, `Expr.umΛ`,
  `Expr.umΓ`). The root's `requires`/`ensures` are `true`, its body is
  `return`.

  What it would mean if it were wrong: a translation that changed a body
  would make every conjunct of `GabbroZiel` speak about another program.
  The transfer theorems (`MitRuheStatisch.lean`, `MitRuheSemantik.lean`)
  state that it does not: every checker fact of `P` holds of `P.mitRuhe` at
  `some f`, and every function behaves in `P.mitRuhe` as in `P`.
-/
module

public import Grammatik.Nebenlaeufigkeit.Sperren.MitRuhe.Teil1
public import Grammatik.Nebenlaeufigkeit.Sperren.MitRuhe.Teil2
