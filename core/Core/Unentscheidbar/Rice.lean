module

public import Core.Unentscheidbar.Modell
public import Mathlib.Computability.Halting

@[expose] public section

namespace Gabbro.Core.Unentscheidbar

open Ast.Semantik
open Nat.Partrec.Code

/-- Gleiches Laufverhalten zweier Programme: ab dem kanonischen Startrahmen
    halten beide bei jeder Eingabe mit denselben Ausgaben. Dies ist die
    Extensionlität, die der Rice-Satz für Gabbro-Programme verlangt — über
    Maschinenläufe formuliert, nicht über Codes. -/
def GleichVerhalten (s : SimulationsSubstrat) (p₁ p₂ : List Befehl) : Prop :=
  ∀ n a, (HaeltMit p₁ (s.startVon n) a ↔ HaeltMit p₂ (s.startVon n) a)

/-- Rice-Transfer auf Gabbro-Programme: eine Eigenschaft `Q` der
    Befehlsprogramme, die nur vom Laufverhalten abhängt (gleiches Verhalten
    → gleiche Antwort), ist — sobald sie auf dem Bild der Simulation weder
    leer noch voll ist — unentscheidbar. Das Prädikat steht über `ℕ`
    (Programmnummern, per `dekodiere` gelesen). Der Beweis zieht die
    Eigenschaft auf Codes zurück und wendet `rice₂` an; die Zurückführung
    auf Nummern gelingt per Linksinverse wie in der Reduktion. -/
theorem substrat_rice (s : SimulationsSubstrat) (Q : List Befehl → Prop)
    (hext : ∀ p₁ p₂, GleichVerhalten s p₁ p₂ → (Q p₁ ↔ Q p₂))
    (hn : (∃ c, Q (s.programm c)) ∧ (∃ c, ¬ Q (s.programm c))) :
    ¬ ComputablePred (fun i => ∃ p, s.dekodiere i = some p ∧ Q p) := by
  have hbeh : ∀ c₁ c₂, eval c₁ = eval c₂ →
      GleichVerhalten s (s.programm c₁) (s.programm c₂) := by
    intro c₁ c₂ h n a
    rw [← s.treue c₁ n a, ← s.treue c₂ n a, h]
  let C : Set Nat.Partrec.Code := {c | Q (s.programm c)}
  have hCext : ∀ cf cg, eval cf = eval cg → (cf ∈ C ↔ cg ∈ C) :=
    fun c₁ c₂ h => hext _ _ (hbeh c₁ c₂ h)
  have hCode : ¬ ComputablePred (fun c => Q (s.programm c)) := by
    intro hC
    have htri := (ComputablePred.rice₂ C hCext).mp hC
    rcases htri with hE | hU
    · obtain ⟨c, hc⟩ := hn.1
      have hmem : c ∈ C := hc
      rw [hE] at hmem
      exact absurd hmem (Set.notMem_empty c)
    · obtain ⟨c, hc⟩ := hn.2
      apply hc
      have hmem : c ∈ C := by
        rw [hU]
        exact Set.mem_univ c
      exact hmem
  have r2 : (fun c => Q (s.programm c)) ≤₀
      (fun i => ∃ p, s.dekodiere i = some p ∧ Q p) :=
    ⟨_, s.komposition_berechenbar, fun c => by
      show Q (s.programm c) ↔ _
      constructor
      · intro hQ
        exact ⟨s.programm c, s.dekodiere_links _, hQ⟩
      · rintro ⟨p, hp, hQ⟩
        have h2 : some (s.programm c) = some p := by
          rw [← s.dekodiere_links (s.programm c)]
          exact hp
        have hpeq : p = s.programm c := (Option.some_inj.mp h2).symm
        subst hpeq
        exact hQ⟩
  intro hQ
  exact hCode (ComputablePred.computable_of_manyOneReducible r2 hQ)

/-- Die pinnierte Aussage: extensionale, auf dem Simulationsbild nichttriviale
    Programmeigenschaften sind — als Prädikate über Programmnummern —
    unentscheidbar. Insbesondere ist keine nichttriviale semantische
    Eigenschaft eines simulierten Programms vom Checker entscheidbar — sie
    gehört zur Nutzerpflicht (GabbroProve). -/
def RiceAussage : Prop :=
  ∀ s (Q : List Befehl → Prop),
    (∀ p₁ p₂, GleichVerhalten s p₁ p₂ → (Q p₁ ↔ Q p₂)) →
    ((∃ c, Q (s.programm c)) ∧ (∃ c, ¬ Q (s.programm c))) →
    ¬ ComputablePred (fun i => ∃ p, s.dekodiere i = some p ∧ Q p)

end Gabbro.Core.Unentscheidbar
