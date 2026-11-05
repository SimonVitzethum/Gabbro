module

public import Grammatik.Zielsatz.Kern.Akzeptiert.Teil2
public import Grammatik.Zielsatz.Atomar.AtomarZiel
public import Grammatik.Logik.Ruf.Guest.Service

@[expose] public section

namespace Gabbro.Grammatik

open Zielsatz

variable {D : Deklaration}

section Bool

variable [DecidableEq D.Fn] [DecidableEq D.Ax]

/-- Guest admission is the final component, after all established program
    checks. Removing it recovers precisely the checker of the same program,
    accumulator queries and check declarations, with no guest descriptor. -/
theorem akzeptiert_guest_eq (P : Programm D) (S : SperrInv D)
    (fs : List D.Fn) (ls : List D.Lock) (cs : List (D.Tab ⊕ D.Glob))
    (ws : List D.Fn) (aks : List (Kernzelle.AccumulatorDecl D))
    (checks : List (CheckDecl D)) (qs : List D.Ax) (guests : List (GuestBoundary D)) :
    Akzeptiert P S fs ls cs ws aks checks qs guests =
      (Akzeptiert P S fs ls cs ws aks checks qs && GuestBoundary.admissionB guests) := by
  simp only [Akzeptiert, GuestBoundary.admissionB_nil, Bool.and_true]

theorem akzeptiert_guest_sound {P : Programm D} {S : SperrInv D}
    {fs : List D.Fn} {ls : List D.Lock} {cs : List (D.Tab ⊕ D.Glob)}
    {ws : List D.Fn} {aks : List (Kernzelle.AccumulatorDecl D)}
    {checks : List (CheckDecl D)} {qs : List D.Ax} {guests : List (GuestBoundary D)}
    (h : Akzeptiert P S fs ls cs ws aks checks qs guests = true) :
    Akzeptiert P S fs ls cs ws aks checks qs = true ∧
      ∀ g ∈ guests, g.admittedB = true := by
  rw [akzeptiert_guest_eq] at h
  obtain ⟨hprogram, hguests⟩ := Bool.and_eq_true_iff.mp h
  exact ⟨hprogram, fun g hg => GuestBoundary.admissionB_each hguests g hg⟩

/-- The identical extra component survives the atomic-rely adapter. -/
theorem akzeptiertX_guest_eq (P : Programm D) (S : SperrInv D)
    (fs : List D.Fn) (ls : List D.Lock) (cs : List (D.Tab ⊕ D.Glob))
    (ws : List D.Fn) (aks : List (Kernzelle.AccumulatorDecl D))
    (checks : List (CheckDecl D)) (qs : List D.Ax) (guests : List (GuestBoundary D)) :
    AkzeptiertX P S fs ls cs ws aks checks qs guests =
      (AkzeptiertX P S fs ls cs ws aks checks qs && GuestBoundary.admissionB guests) := by
  simp only [AkzeptiertX, GuestBoundary.admissionB_nil, Bool.and_true]

end Bool

/-- Attach source-derived guest descriptors to any sound checker. This keeps
    the unit interface and goal statement unchanged. The descriptor extractor
    must be the one certified by the source frontend; it is not an isolation
    proof, which remains GuestServicePflicht on the user-logic side. -/
def Zielsatz.Pruefer.withGuests (C : Pruefer)
    (guests : ∀ {D : Deklaration}, Einheit D → List (GuestBoundary D)) : Pruefer where
  akzeptiert := fun E fs ls cs => C.akzeptiert E fs ls cs && GuestBoundary.admissionB (guests E)
  korrekt := fun E fs ls cs hardware h => C.korrekt E fs ls cs hardware (Bool.and_eq_true_iff.mp h).1

/-- Every descriptor is retained by the checker adapter, even though the
    unchanged goal theorem consumes just its existing program-safety facts. -/
theorem Zielsatz.Pruefer.withGuests_admitted (C : Pruefer)
    (guests : ∀ {D : Deklaration}, Einheit D → List (GuestBoundary D))
    [DecidableEq D.Fn] (E : Einheit D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob))
    (h : (C.withGuests guests).akzeptiert E fs ls cs = true)
    (g : GuestBoundary D) (hg : g ∈ guests E) : g.admittedB = true :=
  GuestBoundary.admissionB_each (Bool.and_eq_true_iff.mp h).2 g hg

/-- The stronger checker of GX keeps start ownership and accumulator-start
    admission as well as the guest component; it delegates every established
    correctness field to the same underlying checker. -/
def Zielsatz.PrueferX.withGuests (C : PrueferX)
    (guests : ∀ {D : Deklaration}, Einheit D → List (GuestBoundary D)) : PrueferX where
  akzeptiert := fun E fs ls cs => C.akzeptiert E fs ls cs && GuestBoundary.admissionB (guests E)
  korrekt := fun E fs ls cs hardware h => C.korrekt E fs ls cs hardware (Bool.and_eq_true_iff.mp h).1

theorem Zielsatz.PrueferX.withGuests_admitted (C : PrueferX)
    (guests : ∀ {D : Deklaration}, Einheit D → List (GuestBoundary D))
    [DecidableEq D.Fn] (E : Einheit D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob))
    (h : (C.withGuests guests).akzeptiert E fs ls cs = true)
    (g : GuestBoundary D) (hg : g ∈ guests E) : g.admittedB = true :=
  GuestBoundary.admissionB_each (Bool.and_eq_true_iff.mp h).2 g hg

/-- A unit with no guest keeps exactly its previous checker verdict. The
    adapter cannot introduce or discharge a hardware or user-logic duty. -/
theorem Zielsatz.Pruefer.withGuests_empty (C : Pruefer)
    [DecidableEq D.Fn] (E : Einheit D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) :
    (C.withGuests (fun _ => [])).akzeptiert E fs ls cs = C.akzeptiert E fs ls cs := by
  simp only [Pruefer.withGuests, GuestBoundary.admissionB_nil, Bool.and_true]

/-- The same exact verdict preservation includes all atomic and start checks. -/
theorem Zielsatz.PrueferX.withGuests_empty (C : PrueferX)
    [DecidableEq D.Fn] (E : Einheit D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) :
    (C.withGuests (fun _ => [])).akzeptiert E fs ls cs = C.akzeptiert E fs ls cs := by
  simp only [PrueferX.withGuests, GuestBoundary.admissionB_nil, Bool.and_true]

end Gabbro.Grammatik
