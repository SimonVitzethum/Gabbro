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

/-! CUTS (skeleton): the separation lemma, the lock-free fixture variant,
  and both witnesses are not yet proved. -/

#print axioms Gabbro.Grammatik.PoolSicher
