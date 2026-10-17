/-
  Explicit continuation storage for the LLVM loop dispatcher.

  This uses the actual G call frames (including stored environments, error
  continuations and held-lock releases). It changes their storage, not the
  source call/return rules. It does NOT prove the Rust emitter or final bytes.
  Allocation failure is explicit; no finite store promises unlimited memory.
-/
import Grammatik.Logik.Ruf.RufMaschineG
import Grammatik.Bausteine.Schablonen.SchablonenFaden

namespace Gabbro.Grammatik.Stapel

/-- The current G frame followed by suspended callers, in execution order. -/
def frames {D : Deklaration} (z : RufFadenG D) : List (RufRahmenG D) :=
  z.kopf :: z.stapel

/-- A lossless heap representation of a source thread's continuation frames. -/
structure Stored (D : Deklaration) where
  head : RufRahmenG D
  callers : List (RufRahmenG D)
  trace : List (Ereignis D)
  log : List (RufEreignisF D)

def store {D : Deklaration} (z : RufFadenG D) : Stored D :=
  ⟨z.kopf, z.stapel, z.spur, z.log⟩

def restore {D : Deklaration} (z : Stored D) : RufFadenG D :=
  ⟨z.callers, z.head, z.trace, z.log⟩

theorem restore_store {D : Deklaration} (z : RufFadenG D) : restore (store z) = z := by
  cases z; rfl

/-- A dispatcher iteration projects to the SAME G step, for every program,
    oracle and thread schedule. This is the semantic obligation of lowering;
    the emitted control flow is tested separately, not certified by this type. -/
def DispatcherStep {D : Deklaration} (P : Programm D) (O : Orakel D) (passes : Nat)
    (M : RufMaschineG D) (f : Faden) (N : RufMaschineG D) : Prop := RufSchrittG P O passes M f N

theorem dispatcher_source {D : Deklaration} {P : Programm D} {O : Orakel D}
    {passes : Nat} {M N : RufMaschineG D} {f : Faden}
    (h : DispatcherStep P O passes M f N) : RufSchrittG P O passes M f N := h

/-- Bounded byte reservation, before writing ANY frame or allocator header. -/
def reserve (used bytes capacity : Nat) : Option Nat :=
  if used + bytes ≤ capacity then some (used + bytes) else none

theorem reserve_bound {u n cap v : Nat} (h : reserve u n cap = some v) : v ≤ cap := by
  unfold reserve at h
  split at h <;> simp_all

theorem reserve_restore {u n cap : Nat} (h : u + n ≤ cap) :
    reserve u n cap = some (u + n) ∧ (u + n) - n = u := by
  simp [reserve, h]

theorem reserve_failure {u n cap : Nat} (h : cap < u + n) : reserve u n cap = none := by
  simp [reserve, Nat.not_le.mpr h]

/-- All suspended G frames remain present, regardless of how many source
    calls are represented; the dispatcher itself needs only one invocation. -/
theorem stored_frames {D : Deklaration} (z : RufFadenG D) :
    frames (restore (store z)) = z.kopf :: z.stapel := by rfl

/-- A real G caller suspended beneath a callee, including its environment/log. -/
theorem restore_store_zeuge :
    (M1G.faeden 0).stapel.length = 1 ∧
    restore (store (M1G.faeden 0)) = M1G.faeden 0 :=
  ⟨rfl, restore_store _⟩

theorem stored_frames_zeuge :
    (frames (restore (store (M1G.faeden 0)))).length = 2 := rfl

/-- The original machine's nonempty call step, not an invented call calculus. -/
theorem dispatcher_source_zeuge :
    DispatcherStep gP rufOF 0 M0G 0 M1G ∧
    (frames (M1G.faeden 0)).length = (frames (M0G.faeden 0)).length + 1 :=
  ⟨schritt1G, rfl⟩

theorem reserve_zeuge : reserve 48 144 256 = some 192 ∧ reserve 192 144 256 = none := by
  decide

/-- Stack release uses the existing join contract: the word is set before
    cloning, and cleared only after the child has ended. An early userspace
    "done" store would NOT meet this premise and must not release the stack. -/
theorem release_after_exit (steps initial n : Nat) (hn : 1 ≤ n)
    (h0 : FadenLaufzeit.wort initial ((FadenLaufzeit.vertragsSpur 1 steps).take n) = 0) :
    FadenLaufzeit.Ereignis.endet ∈ (FadenLaufzeit.vertragsSpur 1 steps).take n :=
  FadenLaufzeit.faden_warte_korrekt 1 steps initial n (by decide) hn h0

theorem release_after_exit_zeuge :
    FadenLaufzeit.Ereignis.endet ∈ (FadenLaufzeit.vertragsSpur 1 3).take 6 :=
  release_after_exit 3 7 6 (by decide) (by decide)

end Gabbro.Grammatik.Stapel
