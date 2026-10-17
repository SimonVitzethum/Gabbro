/-
  File:      Grammatik/Schlusssatz104.lean
  Subject:   THE CLOSING THEOREM, STAGE (a), FOR `beispiele/104-referenz.gab`
             (plan `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` §3 item 2 and
             §6): `schlusssatz_104`. Chain count 1.

  ONE program: `gP` over `gD` (`G104_referenz`), the program the LEAN PARSER
  produces from the source text (`Parser/Uebersetze.lean`). Before this
  file the chain talked about three programs -- `gP` (parser), `r4P` over
  `r4D` (goal theorem, hand translation) and `refP` over `refD` (C
  correspondence, the index-fixed one-parameter model) -- related by data
  agreement only. Every part is re-anchored at `gP` here:

  * section 1, parse: the source text lexes, parses, elaborates and lowers
    to `(gP, gFs)`; every stage a PROPOSITIONAL equation (the `Bool` pins
    `u104parse`/`u104elab` become `rfl` equations), `uebersetze104_ok`;
  * section 2, C: the emitted C bodies of `einzahlen` and `lies` (quoted in
    `CFormenZeuge.lean`) correspond to `gP`'s bodies (`liesG_fn`,
    `einG_fn`); the correspondence certificate carries the printer's rows
    and layout verbatim and `gP`'s locals map (`certG104`, `certOkG`,
    `corrCertG_sound`); from any related start the Gabbro call ends `ok`
    and EVERY C run ends related to it (`c104_einzahlen`, `c104_lies`);
  * section 3, model certificates: the Lean-side print of `gP`'s bodies IS
    the pasted printer output of `ZeugnisStmt104b.lean` (`print104_*`),
    and the Lean checker accepts it;
  * section 4, model judgement: every function of `gP` meets the
    per-function obligations of the goal theorem (`gP_koerperS`,
    `gP_invGutS`);
  * section 5, the machine: G starts EVERY thread in some function, and
    every function of `gD` holds `M` by signature, so no G theorem applies
    to a machine of `gP` alone (`gP_kein_ruhig`, `gP_kein_exklusiv`,
    proved). The runtime supplies the idle root: `gDB`/`gPB` = `gD`/`gP`
    plus exactly that root. `gPB`'s source part IS `gP` under a structural
    renaming (`gPB_ist_gP_umbenannt`, kernel-checked) and BEHAVES as `gP`
    through the same emitted C (`gPB_wie_gP_einzahlen`, `gPB_wie_gP_lies`);
    the goal theorem holds on the machine of `gPB` from every start memory,
    at every `forever` budget, for every start of the runtime's shape
    (`LaufzeitStart`, assumption A4 as a hypothesis), with the root
    function's `ensures` at its completion (`gPB_ziel`);
  * section 6, the theorem -- with A1 (+A2, A3) and A4 as HYPOTHESES
    (2026-09-14) --, its witnesses (rule 13) and its CUTS.
-/

import Grammatik.Korrespondenz.Kette.Schlusssatz104.T1
import Grammatik.Korrespondenz.Kette.Schlusssatz104.T2
import Grammatik.Korrespondenz.Kette.Schlusssatz104.T3
import Grammatik.Korrespondenz.Kette.Schlusssatz104.T4
