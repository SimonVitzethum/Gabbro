/-
  File:      Grammatik/Zielsatz/Verbund.lean
  Subject:   LINKING SEPARATELY COMPILED UNITS, PROVED (Opus agent E, 2026-09-26):
             `gabbro_ziel_verbund : GabbroZielVerbund` (the statement is Spec.lean's), and the
             link check as ONE Bool, `schnittstelleB`, decided exactly (`schnittstelleB_iff`).

  THE ROUTE. The linked unit `verbinde e E₁ E₂` is an ordinary `Einheit`; the proof shows that
  it meets every premise of `GabbroZiel` and applies `gabbro_ziel` (with the concrete checker
  `akzeptiert_pruefer`). Nothing below the goal theorem is re-proved.
  * (a) `akzeptiertSpec_verbinde`: the per-body components of `AkzeptiertSpec` (fragment,
    lock floors, answer sites, lock-invariant places, roots) are each OWNER's verdict -- a
    body's footprint, fragment and features depend on its own text and the shared contracts
    only (`fussOrteG_teil`, `kandB_teil`, `verbindeP_rumpf`; the congruence of the footprint
    under other bodies, `endblockOrteP_mitRumpf`, is a structural induction over the syntax).
    The closed-graph component comes from each unit's closure and the placeholders being
    leaves (`abg_verbinde`: every edge of an owner's view is an edge of the linked program,
    `kante_teil`, and the linked graph is closed, `reachB_ruft` -- the fixpoint of
    `erreichB` is reached within `fs.length` rounds, `erreichB_stabil`, a counting argument).
    The three whole-program components (thread-locality, write separation, pool safety) are
    the link check's, over the COMPOSED hulls: the linked graph of a root lies in its composed
    hull (`huelle_of_reach`, from `KeinRueckruf`).
  * (b) `nutzerPflicht_verbinde`: the linked user duty is the two units' duties over the bodies
    they own (`koerper_mitRumpf2` and its two siblings: a body triple depends on its own body
    and the contracts only), the start obligation per unit over the shared initial memory.
  * (c) the hardware premise of the linked unit IS unit 1's; `E₂.Q = E₁.Q` makes it unit 2's.
  * (d) is the linked runtime's, a premise.

  What the proof does NOT use: the units' own footprint, race and pool components
  (`fuss`, `renn`, `einzeln` of `AkzeptiertSpec`) -- the link re-decides those three over the
  composed hulls, because a unit alone cannot see the other unit's threads nor the reads
  hidden behind an imported head.

  Witnesses: Zielsatz/VerbundZeuge.lean.
-/

import Grammatik.Zielsatz.Faeden.Verbund.T1
import Grammatik.Zielsatz.Faeden.Verbund.T2
import Grammatik.Zielsatz.Faeden.Verbund.T3
