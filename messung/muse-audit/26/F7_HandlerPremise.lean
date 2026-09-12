/-
  Audit 26, finding F7 -- Unterbrechung.lean: `handler_wettlauf_frei`
  (line 103) and `handler_wettlauf_frei_global` (line 120) take premises
  `(K : Korngrenze ...)` and `(hH : H f ∨ H g)` that the proof reads only
  to DISCARD: `K` is bound with `have _ := ...` (never used) and `hH` is
  eliminated with `rcases ... <;> exact kein_wettlauf ...` where the
  handler fact goes nowhere -- `kein_wettlauf` never excluded handlers.
  Pattern (b): premises that play no role. This demo shows the handler
  disjunct is irrelevant: the conclusion follows from `kein_wettlauf`
  alone, for handler and non-handler threads alike.
-/
import Grammatik.Unterbrechung

open Gabbro.Grammatik

/-- F7: the handler premise is discarded -- plain threads suffice. -/
theorem audit26_handler_premise_discarded {D : Deklaration} (l : Lauf D)
    (hg : Gesittet l) (H : Handler)
    (i j : Nat) (hij : i < j) (f g : Faden) (hfg : f ≠ g)
    (t : D.Tab) (w w' : Bool)
    (lam lam' : List (Res D)) (h h' : List D.Lock)
    (hi : l[i]? = some (Schritt.mk f (.zugriff t w lam h)))
    (hj : l[j]? = some (Schritt.mk g (.zugriff t w' lam' h'))) :
    HB l i j := by
  -- NOTE: neither `H`/`hH` nor `Korngrenze` is needed; this is exactly
  -- what the filed proof does after discarding both.
  exact kein_wettlauf l hg i j hij f g hfg t w w' lam lam' h h' hi hj

#print axioms audit26_handler_premise_discarded

/-
CUTS:
  (C1) Whether handler-ness SHOULD constrain the race sentence (e.g. via
       masking) is the job of `handler_nach_freigabe` /
       `maske_schliesst_handler_aus`; this demo only shows THESE two
       theorems add nothing over `kein_wettlauf`.
-/
