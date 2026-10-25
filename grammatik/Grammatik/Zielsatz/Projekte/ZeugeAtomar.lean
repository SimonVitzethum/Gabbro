import Grammatik.Zielsatz.Projekte.Ziel
import Grammatik.Zielsatz.Atomar.AtomarAkzeptiertZeuge

/-!
  File:      Grammatik/Zielsatz/Projekte/ZeugeAtomar.lean
  Subject:   A WITNESS of `gabbro_ziel_projekte`: a SHARED ATOMIC across a project boundary.

  Configuration 1 of the noninterference fixture, cut into two projects: the library project owns
  `kern`, which publishes the atomic `konfig`, and the helpers; the application project owns
  `hauptA` and `hauptB`, which read `konfig` with no lock. Each project proves its own bodies once,
  against the OPEN-WORLD rely (`n1_logikA` holds for every rely); the goal's concrete checker
  accepts the composed program; `gabbro_ziel_projekte` gives every leg of `ZielFX` on every
  reachable thread machine over GX. Non-degenerate: `konfig` IS an admitted shared atomic of the
  composed program, written in one project and read in the other (`grenze`).
-/

namespace Gabbro.Grammatik.ProjekteZeuge

open Gabbro.Grammatik Speichermodell Zielsatz NIZeuge AtomarXZeuge

/-- The application owns the two readers. -/
def eigenApp : nD.Fn → Bool
  | .hauptA => true
  | .hauptB => true
  | _ => false

/-- **The application project**: its starts are the readers. -/
def pApp : Projekt nD :=
  ⟨eigenApp, ⟨nP, SchwachZeuge.nS, axWahr nD, [⟨NFn.hauptA, .nil⟩, ⟨NFn.hauptB, .nil⟩], sp0, [], []⟩⟩

/-- **The library project**: it owns `kern` (the writer of `konfig`) and the rest. -/
def pLib : Projekt nD :=
  ⟨fun f => !eigenApp f, ⟨nP, SchwachZeuge.nS, axWahr nD, [⟨NFn.kern, .nil⟩], sp0, [], []⟩⟩

def ps : List (Projekt nD) := [pApp, pLib]

/-- The link declaration: configuration 1's contracts, lock family and memory. -/
def B : Einheit nD := n1E

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

/-- The composed program IS configuration 1's. -/
theorem komp_P : (komponiere B ps).P = nP := by
  have h : koerperVon nP ps = nP.rumpf := by
    funext f
    cases f <;> rfl
  show mitRumpf nP (koerperVon nP ps) = nP
  rw [h]
  rfl

theorem komp_eq : komponiere B ps = n1E := by
  have hQ : qAlle ps = axWahr nD := by
    funext a
    exact nomatch a
  show (⟨komponiereP nP ps, SchwachZeuge.nS, qAlle ps, _, sp0, _, _⟩ : Einheit nD) = n1E
  rw [hQ]
  have h := komp_P
  change komponiereP nP ps = nP at h
  rw [h]
  rfl

/-- (a) The goal's concrete checker accepts the composed program. -/
theorem akzeptiert : akzeptiertX_pruefer.akzeptiert (komponiere B ps) nFs [] nCs = true := by
  rw [komp_eq]
  show (AkzeptiertX nP SchwachZeuge.nS nFs [] nCs n1ws && besitzB n1E nFs) = true
  rw [n1_akzeptiertX]
  rfl

/-- (b) Each project's own obligation, against the open-world rely. -/
theorem nutzer : ∀ p ∈ ps, NutzerTeilO p := by
  intro p hp
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨⟨fun passes f _ => (n1_logikA OffenA).1 passes f, (n1_logikA OffenA).2⟩,
      ⟨(fun L => nomatch L), fun _ _ => rfl⟩⟩
  · exact ⟨⟨fun passes f _ => (n1_logikA OffenA).1 passes f, (n1_logikA OffenA).2⟩,
      ⟨(fun L => nomatch L), fun _ _ => rfl⟩⟩

/-- (c) The oracle meets the composed program's hardware assumptions. -/
theorem hardware : HardwareAnnahmen nO (komponiere B ps).Q := by
  rw [komp_eq]
  exact ⟨nO_gut, nO_lokal, axVertragO_wahr nO⟩

/-- **The witness**: every leg of `ZielFX` on every reachable thread machine over GX of the program
    linked from the two projects. -/
theorem projekte_zeuge (passes : Nat) (lebt0 : Faden → Bool) (K : FadenMaschine nD.mitRuhe)
    (hK : FadenErreichbarX (komponiere B ps).P.mitRuhe nO.mitRuhe passes
      (GeteiltV (D := nD) (komponiere B ps).P (komponiere B ps).ws)
      (FadenStart (komponiere B ps).P.mitRuhe (speicherR (komponiere B ps).sp0)
        (initRuhe (komponiere B ps).starts) lebt0) K) :
    ZielFX (komponiere B ps).P.mitRuhe (komponiere B ps).S.mitRuhe nO.mitRuhe passes
      (GeteiltV (D := nD) (komponiere B ps).P (komponiere B ps).ws)
      (RufStartG (komponiere B ps).P.mitRuhe (speicherR (komponiere B ps).sp0)
        (initRuhe (komponiere B ps).starts))
      ((komponiere B ps).arenen.map (·.mitRuhe)) K :=
  gabbro_ziel_projekte akzeptiertX_pruefer nD B ps ⟨nFs, nFs_voll⟩ ⟨[], fun L => nomatch L⟩
    ⟨nCs, nCs_voll⟩ verbindbar (by simp [ps]) deckend akzeptiert nutzer nO hardware passes _ _
    (laufzeit_voll _) lebt0 K hK

/-- **Non-degenerate: the atomic crosses the boundary.** `kern` (library) writes `konfig`,
    `hauptA` (application) reads it, and `konfig` is an admitted shared atomic of the composed
    program. -/
theorem grenze : pLib.eigen NFn.kern = true ∧ pApp.eigen NFn.hauptA = true ∧
    GeteiltV (komponiere B ps).P (komponiere B ps).ws (.inr NGlob.konfig) := by
  refine ⟨rfl, rfl, ?_⟩
  rw [komp_eq]
  exact n1_konfig_geteilt

#print axioms projekte_zeuge
#print axioms grenze

end Gabbro.Grammatik.ProjekteZeuge
