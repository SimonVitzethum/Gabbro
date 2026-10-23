/-
  File:      Grammatik/Logik/Terminierung/LaufGX.lean
  Subject:   INFINITE RUNS OF MACHINE GX AND OF THE THREAD MACHINE OVER GX, DEFINITIONS (2026-10-22): the runs the termination statement speaks about
             (Zielsatz/Kern/Spec.lean, `GabbroZielTerminierung`; the theorems in Rekursion.lean and Entscheidung.lean).
-/
import Grammatik.Speichermodell.Atomar.AtomarLauf
import Grammatik.Speichermodell.Maschine.GXMaschine

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

/-- **An infinite run of the thread machine over GX**: at every index thread `u` takes a step of machine GX (a `lauf`
    step, `akt n = some u`), or a thread is started, spawned or joined, or nothing moves; those leave the machine-G
    state alone. A dormant slot keeps its start frame until it is started, and runs from there. -/
structure FadenLaufX (P : Programm D) (O : Orakel D) (passes : Nat) (Tg : D.Tab ⊕ D.Glob → Prop) where
  K : Nat → FadenMaschine D
  akt : Nat → Option Faden
  lauf : ∀ n u, akt n = some u →
    (K n).lebt u = true ∧ (K n).wartet u = [] ∧ RufSchrittGX P O passes Tg (K n).m u (K (n + 1)).m ∧
      K (n + 1) = ⟨(K (n + 1)).m, (K n).lebt, (K n).wartet, (K n).rang, (K n).uhr⟩
  sonst : ∀ n, akt n = none →
    (FadenSchrittX P O passes Tg (K n) (K (n + 1)) ∨ K (n + 1) = K n) ∧ (K (n + 1)).m = (K n).m

/-- The machine-G states of a thread-machine run form a run of GX. -/
def FadenLaufX.alsGX {P : Programm D} {O : Orakel D} {passes : Nat} {Tg : D.Tab ⊕ D.Glob → Prop}
    (R : FadenLaufX P O passes Tg) : LaufGX P O passes Tg where
  M n := (R.K n).m
  akt := R.akt
  schritt n u h := (R.lauf n u h).2.2.1
  stotter n h := (R.sonst n h).2

/-- Every machine of a thread-machine run is a reachable thread machine. -/
theorem FadenLaufX.erreichbar {P : Programm D} {O : Orakel D} {passes : Nat} {Tg : D.Tab ⊕ D.Glob → Prop}
    (R : FadenLaufX P O passes Tg) : ∀ n, FadenErreichbarX P O passes Tg (R.K 0) (R.K n)
  | 0 => .start
  | n + 1 => by
      cases h : R.akt n with
      | none =>
          rcases (R.sonst n h).1 with hs | he
          · exact .schritt _ _ (R.erreichbar n) hs
          · rw [he]; exact R.erreichbar n
      | some u =>
          obtain ⟨hl, hw, hs, he⟩ := R.lauf n u h
          rw [he]
          exact .schritt _ _ (R.erreichbar n) (.lauf _ u _ hl hw hs)

end Gabbro.Grammatik
