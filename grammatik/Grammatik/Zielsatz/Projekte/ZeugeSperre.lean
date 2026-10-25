import Grammatik.Zielsatz.Projekte.Ziel
import Grammatik.Zielsatz.Atomar.TerminierungZeuge

/-!
  File:      Grammatik/Zielsatz/Projekte/ZeugeSperre.lean
  Subject:   A WITNESS of `gabbro_ziel_projekte`: CALLS, CONTRACTS, A LOCK HELD ACROSS THE CALL, A
             GUARDED TABLE and A TABLE INVARIANT across a project boundary.

  The two-thread program `mE` (MehrfadenZeuge.lean), cut into two projects: the library owns
  `setze` (requires `konto` consistent, writes the lock-guarded table `konto`, ensures the value
  written) and the helpers; the application owns the two thread roots `hauptA` and `hauptB`, each
  of which takes the lock and calls `setze` inside `locks { … }`. So a call crosses the boundary
  with its contract, the caller's lock is held across it, the guarded carrier is written on the
  other side, and the table invariant is owed by the library's body to the application's threads.
  Each project proves its own bodies once (open-world rely; `mD` has no atomic global); the goal's
  concrete checker accepts the composed program; `gabbro_ziel_projekte` gives every leg.
-/

namespace Gabbro.Grammatik.ProjekteSperreZeuge

open Gabbro.Grammatik Zielsatz

/-- The application owns the thread roots. -/
def eigenApp : mD.Fn → Bool
  | .hauptA => true
  | .hauptB => true
  | _ => false

def pApp : Projekt mD :=
  ⟨eigenApp, ⟨mP, mSI, axWahr mD, [⟨mHauptA, .nil⟩, ⟨mHauptB, .nil⟩], mSp, [], []⟩⟩

def pLib : Projekt mD :=
  ⟨fun f => !eigenApp f, ⟨mP, mSI, axWahr mD, [], mSp, [], []⟩⟩

def ps : List (Projekt mD) := [pApp, pLib]

def B : Einheit mD := Zielsatz.mE

theorem verbindbar : ∀ p ∈ ps, Verbindbar B p.E := by
  intro p hp
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem deckend : Deckend ps := by
  intro f
  cases f
  all_goals first
    | exact ⟨pApp, List.mem_cons_self, rfl⟩
    | exact ⟨pLib, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩

theorem komp_eq : komponiere B ps = Zielsatz.mE := by
  have hP : koerperVon mP ps = mP.rumpf := by
    funext f
    cases f <;> rfl
  have hQ : qAlle ps = axWahr mD := by
    funext a
    exact nomatch a
  show (⟨mitRumpf mP (koerperVon mP ps), mSI, qAlle ps, _, mSp, _, _⟩ : Einheit mD) = Zielsatz.mE
  rw [hP, hQ]
  rfl

theorem akzeptiert : akzeptiertX_pruefer.akzeptiert (komponiere B ps) mFs [()] mCs = true := by
  rw [komp_eq]
  exact mX_akzeptiert

/-- `mD` has no global, so no atomic: the open-world rely is empty and the sequential logic is
    the logic with the rely. -/
theorem logikO : LogikPflichtA mP mSI (axWahr mD) OffenA :=
  logikPflichtA_of_frei (fun _ _ _ hc => by
    obtain ⟨g, _, _⟩ := hc.1
    exact nomatch g) mE_nutzerPflicht.logik

theorem nutzer : ∀ p ∈ ps, NutzerTeilO p := by
  intro p hp
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨⟨fun passes f _ => logikO.1 passes f, logikO.2⟩, mE_nutzerPflicht.start⟩
  · refine ⟨⟨fun passes f _ => logikO.1 passes f, logikO.2⟩, ⟨mE_nutzerPflicht.start.sperren, ?_⟩⟩
    intro a ha
    simp [pLib] at ha

theorem hardware : HardwareAnnahmen mO (komponiere B ps).Q := by
  rw [komp_eq]
  exact ⟨mO_gut, mO_lokal, axVertragO_wahr mO⟩

/-- **The witness**: every leg of `ZielFX` on every reachable thread machine over GX of the program
    linked from the two projects. -/
theorem projekte_sperre_zeuge (passes : Nat) (lebt0 : Faden → Bool) (K : FadenMaschine mD.mitRuhe)
    (hK : FadenErreichbarX (komponiere B ps).P.mitRuhe mO.mitRuhe passes
      (GeteiltV (D := mD) (komponiere B ps).P (komponiere B ps).ws)
      (FadenStart (komponiere B ps).P.mitRuhe (speicherR (komponiere B ps).sp0)
        (initRuhe (komponiere B ps).starts) lebt0) K) :
    ZielFX (komponiere B ps).P.mitRuhe (komponiere B ps).S.mitRuhe mO.mitRuhe passes
      (GeteiltV (D := mD) (komponiere B ps).P (komponiere B ps).ws)
      (RufStartG (komponiere B ps).P.mitRuhe (speicherR (komponiere B ps).sp0)
        (initRuhe (komponiere B ps).starts))
      ((komponiere B ps).arenen.map (·.mitRuhe)) K :=
  gabbro_ziel_projekte akzeptiertX_pruefer mD B ps ⟨mFs, mFs_voll⟩ ⟨[()], mLocks_voll⟩
    ⟨mCs, mCs_voll⟩ verbindbar (by simp [ps]) deckend akzeptiert nutzer mO hardware passes _ _
    (laufzeit_voll _) lebt0 K hK

/-- **Non-degenerate: the boundary is crossed.** The application's `hauptA` calls the library's
    `setze` (a call edge across the boundary), `setze` has a non-trivial contract and the program
    a table invariant. -/
theorem grenze : pApp.eigen MFn.hauptA = true ∧ pLib.eigen MFn.setze = true ∧
    ruftB (komponiere B ps).P MFn.hauptA MFn.setze = true := by
  refine ⟨rfl, rfl, ?_⟩
  rw [komp_eq]
  decide

#print axioms projekte_sperre_zeuge
#print axioms grenze

end Gabbro.Grammatik.ProjekteSperreZeuge
