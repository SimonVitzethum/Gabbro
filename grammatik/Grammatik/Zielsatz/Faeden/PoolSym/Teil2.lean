module

public import Grammatik.Logik.Ruf.Maschine.RufMaschineD
public import Grammatik.Logik.Ruf.Maschine.RufMaschineF
public import Grammatik.Zielsatz.Kern.Akzeptiert
public import Grammatik.Zielsatz.Faeden.PoolSym.Teil1
public import Grammatik.Korpus.Referenz.ReferenzB

@[expose] public section

namespace Gabbro.Grammatik
open Zielsatz
variable {D : Deklaration}

/-- **The refusal witness**: on the reference fixture itself, `PoolSicher`
    is uninhabited -- both functions hold the lock by signature. This is
    why the joint witness lives on the lock-free variant, and why the
    checker refuses the fixture's writer on two threads (`N304`). -/
theorem poolSicher_refD_unmoeglich (K : refD.Fn → Bool) (w : refD.Fn) :
    ¬ PoolSicher refD K w := by
  intro h
  cases w with
  | true => exact absurd h.1 (by decide)
  | false => exact absurd h.1 (by decide)

/-! CUTS: what is not proved.
  * Per-core writes are not covered model-side: the surface exempts
    `accumulates … per cpu`, the model has no notion for it (OFFEN O17); the
    exporter refuses such units.
  * The goal legs over pool starts are NOT in this file any more: since fix
    lane F10 they are `gabbro_ziel` itself (the only proof changes are
    `getrenntK_of`/`schreibGetrenntK_of`, Zielsatz/Akzeptiert.lean), witnessed
    on a two-worker pool in Zielsatz/PoolZeuge.lean. `pool_schreibt_nicht_lauf`
    stays as the run-level form of the write leg. -/

#print axioms Gabbro.Grammatik.pool_schreibt_nicht
#print axioms Gabbro.Grammatik.pool_schreibt_zeigt
#print axioms Gabbro.Grammatik.poolSicher_refD_unmoeglich
#print axioms Gabbro.Grammatik.poolSicherWB_iff
#print axioms Gabbro.Grammatik.einzelnPoolB_iff
#print axioms Gabbro.Grammatik.einzelnPoolB_of_einzelnB
#print axioms Gabbro.Grammatik.einzelnPool_paar
#print axioms Gabbro.Grammatik.einzelnPool_of_nodup
#print axioms Gabbro.Grammatik.getrenntW_nodup
#print axioms Gabbro.Grammatik.akzeptiert_nodup_gleich
#print axioms Gabbro.Grammatik.akzeptiertVor_nodup
#print axioms Gabbro.Grammatik.akzeptiert_vor_neu
#print axioms Gabbro.Grammatik.akzeptiertSpecVor_neu
#print axioms Gabbro.Grammatik.pruefer_vor_neu
#print axioms Gabbro.Grammatik.laufzeit_vor_neu
#print axioms Gabbro.Grammatik.pool_schreibt_nicht_lauf
#print axioms Gabbro.Grammatik.pool_startExklusiv
#print axioms Gabbro.Grammatik.Zielsatz.PoolSicher
#print axioms Gabbro.Grammatik.Zielsatz.EinzelnPool
