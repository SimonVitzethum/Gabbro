/-
  File:      Grammatik/ZielOrtVollSem.lean
  Subject:   THE SEQUENTIAL SIDE OF `ziel_ort_voll` -- the frame semantics of
             EVERY residue of G (loops, their shims, the exits `leave`/`next`,
             the waiting residues), the covered fragment `vOk`, and the
             one-sided comparison of frame results.

  `ziel_ort` (`ZielOrtBeweis.lean`) replays each frame of G by the
  sequential semantics of its body, for bodies in the fragment `kOk` (no
  loops, no exits, no error channel, no oracle form). Here the frame
  semantics is extended to the whole residue type `GRest`:

  * `weiterZ r o` -- how the residue `r` continues from the outcome `o` of
    the code before it. A plain `ok` outcome runs `r`; `zurueck`, `grund`,
    `logik`, `hardware` pass through every residue; `leave`/`next` pass
    through `dann`/`schrumpf`/`frei` (they skip the rest of a loop body)
    and are consumed by the loop shims `travRest`/`wiederRest`/`ewigRest`
    exactly as `traverseLauf`/`retryLauf`/`foreverLauf` consume them. The
    loop residues `trav`/`wieder`/`ewig` run the remaining loop by the
    sequential loop functions themselves, with the remaining indices, tries
    or `forever` budget. `semZ' r σ ρ := weiterZ r (.ok σ ρ)`.
  * The waiting residues (`wartet`, `wartetSonst`) never run as a head
    (`rufG_nie_wartend`); they give `sonst` on `ok` and pass every other
    outcome through.
  * `ZErg.folgt a b`: the frame result `a` of the body is predicted by `b`
    -- `b` is `sonst` (no prediction) or `a` agrees with `b`. Some steps of
    G replace a residue by an end block (`narrow`/`pruefung`/float `else`
    blocks, the `else` block of `let … else` on a reason): if that end
    block ends in `leave`/`next` inside a loop, G is stuck there, and the
    new residue predicts nothing (`sonst`). A preorder with `sonst` on top.
  * `vOk K`: the covered fragment -- every form but the register and
    visibility forms (`regLies`, `regLiesElse`, `awaits`); an indirect call
    through a pointer of signature `n` where `K n` holds (every function of
    that signature has its contract carriers in the footprint, `KandOk`;
    decided over the complete member list, `kandB`); and `GRest.okV`,
    residues in it that read inside a footprint.
-/

import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollSem.T1
import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollSem.T2
import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollSem.T3
import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollSem.T4
