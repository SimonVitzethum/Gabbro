/-
  File:      Grammatik/ZielOrtAxBeweis.lean
  Subject:   THE REPLAY FOR `ziel_ort_voll_ax` -- the replay of
             `ZielOrtVollBeweis.lean` (records of call and axiom answers, the
             invariants `KopfV`/`WarteV`/`FadenV` and the steps that keep
             them), with ONE more conjunct: every recorded axiom answer meets
             the axioms' declared ensures `Q` (`VertragA O.zeiger Q HA`). The record
             oracle `orakelAus O HA` then meets `Q` (`orakelAus_vertrag`), so
             the strengthened user obligation `KoerperGutA` can be applied to
             it where `KoerperGutV` was.

  The copy is literal except for: the parameter `Q`, the conjunct
  `VertragA O.zeiger Q HA` (kept by every step; the axiom step proves it for its new
  record from the machine's oracle meeting `Q`, `AxVertragO Q O`, and the
  locality of `Q` to the declared carriers, `AxEnsLokal Q`, through
  `axWelt_vertrag`), and the hypotheses `hQ`/`hlok` where the obligation is
  applied or an axiom answer is recorded. The records, `FortV`,
  `fortV_mono`, `logOk_grund` and the leaf lemmas are reused.
-/
module

public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtAxBeweis.Teil1
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtAxBeweis.Teil2
