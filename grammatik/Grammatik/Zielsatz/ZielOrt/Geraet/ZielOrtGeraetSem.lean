/-
  File:      Grammatik/ZielOrtGeraetSem.lean
  Subject:   THE DEVICE FORMS FOR `ziel_ort_geraet` -- the hardware class of
             register locality (`RegLokal`), the widened fragment (`gOk`:
             register reads, `let … else` register reads and `awaits`
             admitted), the footprint widened by the device carriers of every
             register a body reads (`fussOrteG`), its check (`fussOrtGB`), the
             user obligation against local oracles (`KoerperGutG`), and the
             frame semantics of the three device forms.

  Register reads are not in the fragment of `ziel_ort_voll`: a register
  answer is `O.regLies r σ`, a function of the WHOLE world, and on G another
  thread changes the world between two reads outside the reader's footprint.
  (Until 2026-10-25 a two-thread counterexample refuted the plain widening; it
  relied on two reads in one world answering alike, which no longer holds since
  every read is a trace event, `Ereignis.fremd`.) The repair has two halves.

  * HARDWARE (`RegLokal`): the declaration attributes to every register the
    carriers that hold its device's state (`D.rtraeger r`, a declaration
    field, default none); the answer of a read depends on those carriers
    only. The same for the visibility answer of `awaits g`: it depends on the
    awaited global `g` only. Two reads MAY answer differently exactly when
    those carriers changed in between; a device whose state changes by
    itself writes those carriers, through a declared write (an axiom whose
    frame names them), and that write is recorded like every axiom write
    (`fadenV_ax`/`fadenG_ax`).
  * PROGRAM FACT (`fussOrteG`, `fussOrtGB`): the footprint of a function
    contains the device carriers of every register its body reads, and the
    footprint check covers them (guarded by a lock the function holds by
    signature, or written by no function).

  Together: the reader's sequential world agrees with the machine world on
  the footprint, hence on the device carriers, hence the sequential answer
  of a local oracle is the machine's answer.
-/
module

public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraetSem.Teil1
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraetSem.Teil2
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraetSem.Teil2a
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraetSem.Teil3
