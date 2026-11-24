module

public import Core.Unentscheidbar.Modell
public import Mathlib.Computability.Halting

@[expose] public section

namespace Gabbro.Core.Unentscheidbar

open Nat.Partrec.Code

/-- Rice-Transfer auf simulierte Programme: eine Eigenschaft `Q` der
    Befehlsprogramme, die nur von der berechneten partiellen Funktion abhängt
    (gleiche `eval`-Funktion → gleiche Antwort), ist — sobald sie auf dem Bild
    der Simulation weder leer noch voll ist — unentscheidbar. Der Beweis zieht
    die Eigenschaft auf Codes zurück und wendet `rice₂` an. -/
theorem gabbro_rice (programm : Nat.Partrec.Code → List Befehl)
    (Q : List Befehl → Prop)
    (hext : ∀ c₁ c₂, eval c₁ = eval c₂ → (Q (programm c₁) ↔ Q (programm c₂)))
    (hn : (∃ c, Q (programm c)) ∧ (∃ c, ¬ Q (programm c))) :
    ¬ ComputablePred (fun c => Q (programm c)) := by
  intro hQ
  -- Rein code-seitig: weder Treue noch Offenheit werden gebraucht; die Aussage
  -- hält sie als Fragment-Einordnung fest.
  let C : Set Nat.Partrec.Code := {c | Q (programm c)}
  have hCext : ∀ cf cg, eval cf = eval cg → (cf ∈ C ↔ cg ∈ C) := hext
  have hC : ComputablePred (fun c => c ∈ C) := hQ
  have htri := (ComputablePred.rice₂ C hCext).mp hC
  rcases htri with hE | hU
  · obtain ⟨c, hc⟩ := hn.1
    have : c ∈ C := hc
    rw [hE] at this
    exact absurd this (Set.notMem_empty c)
  · obtain ⟨c, hc⟩ := hn.2
    apply hc
    have : c ∈ C := by
      rw [hU]
      exact Set.mem_univ c
    exact this

/-- Die pinnierte Aussage: extensionale, nichttriviale Programmeigenschaften
    sind im offenen Fragment unentscheidbar. Insbesondere ist keine
    nichttriviale semantische Eigenschaft eines simulierten Programms vom
    Checker entscheidbar — sie gehört zur Nutzerpflicht (GabbroProve). -/
def RiceAussage : Prop :=
  ∀ programm start (Q : List Befehl → Prop), SimulationsTreue programm start →
    (∀ c n, OffenesFragment (start c n)) →
    (∀ c₁ c₂, eval c₁ = eval c₂ → (Q (programm c₁) ↔ Q (programm c₂))) →
    (∃ c, Q (programm c)) ∧ (∃ c, ¬ Q (programm c)) →
    ¬ ComputablePred (fun c => Q (programm c))

end Gabbro.Core.Unentscheidbar
