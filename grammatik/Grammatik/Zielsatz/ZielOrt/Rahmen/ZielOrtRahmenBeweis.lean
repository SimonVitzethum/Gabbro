/-
  File:      Grammatik/ZielOrtRahmenBeweis.lean
  Subject:   The replay of `ziel_ort_geraet` (`ZielOrtGeraetBeweis.lean`)
             against FRAME-RESPECTING call handlers: the user obligation is
             `KoerperGutR` (`ZielOrtRahmenSem.lean`), so every recorded normal
             call answer must lie in the callee's declared frame around its
             key world.

  The invariants `KopfR`/`WarteR`/`StapelR`/`FadenR`/`ZielInvR` are those of
  `ZielOrtGeraetBeweis.lean` with three changes.
  * The records carry the frame (`VertraegeOkR = VertraegeOkV ∧ RahmenV`),
    so the record handler `rufAusV H` respects contracts AND frames
    (`rufAusV_rahmen`) and the user obligation applies to it.
  * A suspended frame also keeps: its callee's contract carriers lie in its
    footprint, and its key world agrees with the callee's machine entry
    world on the WHOLE footprint (not only on the callee's contract).
  * A call answer is recorded with the answer world `rahmenWelt` (the
    callee's declared write carriers from the machine's return world, the
    rest from the key world, a lock-neutral fresh trace position) instead of
    `antwortWelt` (the whole machine return world): it lies in the callee's
    frame by construction, and agrees with the machine on the caller's
    footprint because the machine kept that footprint outside the callee's
    writes during the call (`rufG_rahmen`, passed to `popR_kopf` as `hRah`).
-/
module

public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtRahmenBeweis.Teil1
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtRahmenBeweis.Teil2
