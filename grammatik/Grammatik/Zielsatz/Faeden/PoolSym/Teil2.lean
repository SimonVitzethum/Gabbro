module

public import Grammatik.Zielsatz.Kern.Akzeptiert
public import Grammatik.Korpus.Referenz.ReferenzB
public import Grammatik.Zielsatz.Faeden.PoolSym.Teil1

@[expose] public section

namespace Gabbro.Grammatik
open Zielsatz
variable {D : Deklaration}

/-- **The joint witness for `pool_schreibt_nicht`**: every premise
    instantiated jointly on the lock-free fixture -- the empty member list
    (the graph is then definitionally `{einzahlen}`, so no body is ever
    unfolded), the unguarded, non-atomic, never-written global `frei` as
    the carrier, thread 0 running `einzahlen` with argument 7. -/
theorem pool_schreibt_nicht_zeuge :
    ∃ (D : Deklaration) (_ : DecidableEq D.Fn) (P : Programm D) (fs : List D.Fn)
      (w : D.Fn)
      (init : Faden → Σ f : D.Fn, Env D (D.params f)) (t : Faden)
      (c : D.Tab ⊕ D.Glob) (g : D.Fn),
      (init t).1 = w ∧ PoolSicher D (reachB P fs w) w ∧
      (∀ L, ¬ Bewacht c L) ∧ ¬ AtomarAusgenommen c ∧
      kVon P fs init t g = true := by
  refine ⟨poolD, inferInstance, poolP, [], true, fun _ => ⟨true, poolRho⟩, 0,
    .inr (), true, rfl, ?_, ?_, ?_, ?_⟩
  · refine ⟨rfl, rfl, fun f hf c hc => ?_⟩
    cases f with
    | false => exact absurd hf (by decide)
    | true =>
        cases c with
        | inl _ => exact Or.inl ⟨(), List.mem_cons_self⟩
        | inr x => cases x; exact absurd hc (by decide)
  · intro L h
    cases h
  · intro hA
    obtain ⟨g, _, hg2⟩ := hA
    cases g
    exact absurd hg2 (by decide)
  · unfold kVon
    exact reachB_wurzel _ _ _

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
#print axioms Gabbro.Grammatik.pool_schreibt_nicht_zeuge
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
