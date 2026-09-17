/-
  File:      Grammatik/Zielsatz/PoolSym.lean
  Subject:   The symmetric worker pool (lane 245): one routine on N threads.

  The checker admits `concurrent { f, f }` (the same routine twice) IFF the
  routine is pool-safe: it holds no lock by signature, declares no reasons,
  and every carrier its thread graphs may write is guarded by a lock or
  atomic (`fusswache2.rs`, narrowed `N304`). This file is the model side of
  that condition: `PoolSicher` over the computed thread graphs, and the
  separation lemma for two threads running one pool-safe routine. It is
  ADDITIVE: `Spec.lean` (`Laufzeit.einmal`, `einzeln`) is untouched; the
  exact Spec diff that would lift them is specified in MUSE-REPORT-245.md.
-/
import Grammatik.Zielsatz.Akzeptiert
import Grammatik.ReferenzB

namespace Gabbro.Grammatik

open Zielsatz

variable {D : Deklaration}

/-- **Pool-safe**: routine `w` may run on any number of threads. It starts
    like any admitted start (no signature-held lock, no reasons), and every
    carrier some function of the thread graph `K` may write is guarded by a
    lock or atomic. Reads need nothing: with no unguarded writer, two
    threads reading one carrier do not race. Per-core cells are NOT covered
    model-side (the model has no notion for them; see CUTS). -/
def PoolSicher (D : Deklaration) (K : D.Fn → Bool) (w : D.Fn) : Prop :=
  D.haelt w = [] ∧ D.gruende w = 0 ∧
    ∀ f, K f = true → ∀ c, TraegerSchreibt f c = true →
      (∃ L, Bewacht c L) ∨ AtomarAusgenommen c

/-! ## The separation lemma for a symmetric pair -/

/-- **No unguarded writes on a pool-safe thread.** If thread `t` starts the
    pool-safe routine `w`, no function of its computed graph writes an
    unguarded, non-atomic carrier. Applied to both threads of a symmetric
    pair, no write-write and no write-read race on unguarded carriers
    exists -- the model half of the narrowed `N304`. The footprint half of
    `SchreibGetrenntK` is NOT claimed: a pool-safe routine may read
    unguarded carriers it never writes. -/
theorem pool_schreibt_nicht {P : Programm D} {fs : List D.Fn} {w : D.Fn}
    [DecidableEq D.Fn]
    {init : Faden → Σ f : D.Fn, Env D (D.params f)}
    {t : Faden} (ht : (init t).1 = w)
    (hpool : PoolSicher D (reachB P fs w) w)
    {c : D.Tab ⊕ D.Glob} (hB : ∀ L, ¬ Bewacht c L) (hAt : ¬ AtomarAusgenommen c)
    {g : D.Fn} (hg : kVon P fs init t g = true) :
    TraegerSchreibt g c = false := by
  have hg' : reachB P fs w g = true := by
    unfold kVon at hg
    rw [ht] at hg
    exact hg
  cases hc : TraegerSchreibt g c with
  | true =>
      rcases hpool.2.2 g hg' c hc with ⟨L, hL⟩ | hA
      · exact absurd hL (hB L)
      · exact absurd hA hAt
  | false => rfl

/-! CUTS (lemma): the lock-free fixture variant and both witnesses are not
  yet proved. -/

#print axioms Gabbro.Grammatik.pool_schreibt_nicht
