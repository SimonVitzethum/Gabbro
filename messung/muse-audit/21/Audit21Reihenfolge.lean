/-
  Lane-21 audit probe 6: `pc_discharge_unshared` reorders its premises.

  Claim under test (pattern (a), representation change): the file documents
  that in `pc_discharge_unshared` "the shared-side hypothesis comes before
  the access equations ... so the match must precede them to keep the
  `Gesittet` shape". Demonstrated: the reordered signature is inter-derivable
  with the `Gesittet.ungeteilt` field order by pure permutation — no
  elaboration obstacle remains once stated; the call site in `pc_gesittet`
  re-permutes with a lambda. The audit point is narrow: the reorder is
  presentation, and the discharge itself still replaces the declaration-side
  premise `hungeteilt` with a new program-text premise `PCUnsharedSep`.
-/
import Grammatik.Maschine

open Gabbro.Grammatik

variable {D : Deklaration}

/-- `Gesittet.ungeteilt` order implies the `pc_discharge_unshared` order.
    Note: the `match` must come before hypotheses mentioning `o`, else Lean
    elaborates extra discriminants (this is the real content of the in-file
    comment — confirmed by the error when ordered the other way). -/
theorem audit21_unshared_reorder_fwd
    (U : ∀ (i j : Nat) (f g : Faden) (o : D.Tab ⊕ D.Glob)
      (ei ej : Ereignis D),
      (M : GenMaschine D) →
      M.lauf[i]? = some (Schritt.mk f ei) → M.lauf[j]? = some (Schritt.mk g ej) →
      ei.traeger = some o → ej.traeger = some o →
      (match o with
        | .inl t => D.geteilt t = false
        | .inr x => D.ggeteilt x = false) → f = g)
    (M : GenMaschine D)
    (i j : Nat) (f g : Faden) (o : D.Tab ⊕ D.Glob)
    (ei ej : Ereignis D)
    (hi : M.lauf[i]? = some (Schritt.mk f ei))
    (hj : M.lauf[j]? = some (Schritt.mk g ej))
    (hsh : match o with
      | .inl t => D.geteilt t = false
      | .inr x => D.ggeteilt x = false)
    (hti : ei.traeger = some o) (htj : ej.traeger = some o) :
    f = g := by
  cases o with
  | inl t => exact U i j f g (.inl t) ei ej M hi hj hti htj hsh
  | inr x => exact U i j f g (.inr x) ei ej M hi hj hti htj hsh

/-- And back: the discharge order implies the `Gesittet` field order. -/
theorem audit21_unshared_reorder_bwd
    (U : (M : GenMaschine D) →
      ∀ (i j : Nat) (f g : Faden) (o : D.Tab ⊕ D.Glob)
      (ei ej : Ereignis D),
      M.lauf[i]? = some (Schritt.mk f ei) → M.lauf[j]? = some (Schritt.mk g ej) →
      (match o with
        | .inl t => D.geteilt t = false
        | .inr x => D.ggeteilt x = false) →
      ei.traeger = some o → ej.traeger = some o → f = g)
    (M : GenMaschine D)
    (i j : Nat) (f g : Faden) (o : D.Tab ⊕ D.Glob)
    (ei ej : Ereignis D)
    (hi : M.lauf[i]? = some (Schritt.mk f ei))
    (hj : M.lauf[j]? = some (Schritt.mk g ej))
    (hti : ei.traeger = some o) (htj : ej.traeger = some o)
    (hsh : match o with
      | .inl t => D.geteilt t = false
      | .inr x => D.ggeteilt x = false) :
    f = g := by
  cases o with
  | inl t => exact U M i j f g (.inl t) ei ej hi hj hsh hti htj
  | inr x => exact U M i j f g (.inr x) ei ej hi hj hsh hti htj

/- 
CUTS:
- This probe demonstrates premise-permutation only. The reorder needs a
  `cases o` (the `match`-elaboration anecdote in-file is REAL: the naive
  application fails, see probe history). It does NOT challenge the discharge
  content (`PCCarrierInv` + `PCUnsharedSep` replacing `hungeteilt`); that
  replacement is genuine new structure, booked honestly in §12, and outside
  patterns (a)-(e). Severity below reflects this: informational.
-/
#print axioms audit21_unshared_reorder_fwd
#print axioms audit21_unshared_reorder_bwd
