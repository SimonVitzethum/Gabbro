/-
  File:      Grammatik/ZielOrtVollBeweis.lean
  Subject:   `ziel_ort_voll` -- contracts hold at their place on every machine
             of the repaired concurrent call machine G, for programs whose
             bodies use loops (`traverse`, `retry`, `forever` with its
             budget), the exits `leave`/`next`, the error channel
             (`return` of a reason, `let … else`) and axiom calls.

  The proof is the replay of `ZielOrtBeweis.lean`, widened in four places.

  * The frame semantics is `semV` (`ZielOrtVollSem.lean`): every residue of
    G has a meaning, the loop residues by the sequential loop functions.
  * The body's frame result is PREDICTED by the residue (`ZErg.folgt`),
    not equal to it: G replaces a residue by an end block in some steps,
    and where that end block leaves a loop, G is stuck and predicts nothing.
  * The record of a frame's calls keeps REASON answers too (`EintragV`):
    a callee that returns a reason pops into its caller's `else` block, and
    the caller's replay continues there with the reason bound.
  * Axiom calls are recorded like calls (`AxEintrag`): the sequential run
    uses an oracle that repeats the machine's answers (`orakelAus`) at
    fresh keys. The recorded answer world takes the axiom's declared
    carriers from the machine and everything else from the sequential key
    world, so the recorded oracle respects every axiom's declared frame
    (`RahmenO`). The user obligation for a body that calls an axiom is its
    Hoare triple for EVERY oracle that respects the declared frames
    (`KoerperGutV`): the axiom's answer and its effect inside its frame are
    hardware, the triple may assume nothing else about them.

  What contracts say about reason returns: nothing (`RespektiertVertraege`
  and `EnsAmRueck` are about normal returns). The statement for reasons is
  the machine's own: the logged `grund` event carries the reason the callee
  returned and the caller's `else` block runs with that reason bound
  (`rufG_grund_treu`, `ZielOrtVoll.lean`). The theorem `ziel_ort_voll` is
  in `ZielOrtVoll.lean`, its witness `ziel_ort_voll_zeuge` in
  `ZielOrtVollZeuge.lean`.
-/
module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollBeweis.Teil1
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollBeweis.Teil2
