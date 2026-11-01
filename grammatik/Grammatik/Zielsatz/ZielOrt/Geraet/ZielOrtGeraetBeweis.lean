/-
  File:      Grammatik/ZielOrtGeraetBeweis.lean
  Subject:   The replay of `ziel_ort_voll` (`ZielOrtVollBeweis.lean`) for the
             widened fragment: the sequential oracles of the replay give the
             machine's register and visibility answers (`GleichRS`), the
             footprint is the widened one (`fussOrteG`), the residues are in
             the widened fragment (`GRest.okG`), and the user obligation is
             `KoerperGutG` (every frame-respecting, register-local oracle).

  The invariants `KopfG`/`WarteG`/`StapelG`/`FadenG`/`ZielInvG` are those of
  `ZielOrtVollBeweis.lean` with three changes: the machine oracle `O` is a
  parameter, the replayed sequential oracles `O'` are those with `O`'s
  register and visibility answers (`GleichRS O O'`), and footprint and
  fragment are the widened ones. The steps are the same; the record oracle
  `orakelAus O HA` has `O`'s register and visibility answers by
  construction, and is register-local when `O` is (`regLokal_orakelAus`).
-/
module

public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraetBeweis.Teil1
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraetBeweis.Teil2
