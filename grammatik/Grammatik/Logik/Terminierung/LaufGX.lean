/-
  File:      Grammatik/Logik/Terminierung/LaufGX.lean
  Subject:   INFINITE RUNS OF MACHINE GX, DEFINITIONS (2026-10-22): the runs the termination statement speaks about
             (Zielsatz/Kern/Spec.lean, `GabbroZielTerminierung`; the theorems in Rekursion.lean and Entscheidung.lean).
-/
import Grammatik.Speichermodell.Atomar.AtomarLauf

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **An infinite run of GX**: at every index thread `u` takes a GX step (`akt n = some u`) or nothing moves. -/
structure LaufGX (P : Programm D) (O : Orakel D) (passes : Nat) (Tg : D.Tab ⊕ D.Glob → Prop) where
  M : Nat → RufMaschineG D
  akt : Nat → Option Faden
  schritt : ∀ n u, akt n = some u → RufSchrittGX P O passes Tg (M n) u (M (n + 1))
  stotter : ∀ n, akt n = none → M (n + 1) = M n

theorem LaufGX.erreichbar {P : Programm D} {O : Orakel D} {passes : Nat} {Tg : D.Tab ⊕ D.Glob → Prop}
    (R : LaufGX P O passes Tg) {M0 : RufMaschineG D} (h0 : R.M 0 = M0) :
    ∀ n, RufErreichbarGX P O passes Tg M0 (R.M n)
  | 0 => h0 ▸ .start
  | n + 1 => by
      cases h : R.akt n with
      | none => rw [R.stotter n h]; exact R.erreichbar h0 n
      | some u => exact .schritt _ _ u (R.erreichbar h0 n) (R.schritt n u h)

end Gabbro.Grammatik
