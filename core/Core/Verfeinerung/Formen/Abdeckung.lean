module

public import Core.Verfeinerung.Formen.Familie

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog

/-- The current runtime instruction set obtains its simulation obligations from the two class
    packets: every instruction is in one class. -/
theorem sim_formen (lokal : LokalSimAussage) (ruf : RufSimAussage) (p : Fragment)
    (platform : Plattform) : ∀ b, I.RegelSimulation (p.einheit platform) b := by
  intro b
  cases klasse : b.klasse with
  | lokal => exact lokal p platform b klasse
  | ruf => exact ruf p platform b klasse

theorem Fragment.simBasis (p : Fragment) (platform : Plattform) :
    I.SimBasisPflichten (p.einheit platform) := by
  apply I.SimBasisPflichten.aus_gleichen_regeln rfl
  · intro h s hardware zul
    have image : bild.gueltig h.ziel := hardware.ziel.symm ▸ zul.1
    have loaded := hardware.lader bild image
    have entry : (h.lade bild).starts 0 = some 0 := lader_start loaded 0
    have byte : (h.lade bild).bytes 0 = some 0 := (loaded.2.1 0 0 rfl).2
    change laden p.eingang p.eintritte p.speicher platform s (h.lade bild) = some _
    unfold laden
    rw [ite_eq_left ⟨entry, byte⟩]
    rfl
  · exact fun _ _ _ _ _ _ rule => rule
  · intro b c s w stepPlan u rule
    have same : [stepPlan] = [plan] := rule.1
    cases (List.cons.inj same).1
    exact ⟨fun _ empty => (List.not_mem_nil empty).elim, fun _ empty => (List.not_mem_nil empty).elim⟩

/-- Connect the form packets to the ordinary elaboration and run interfaces. -/
theorem sim_elaborierter_lauf (lokal : LokalSimAussage) (ruf : RufSimAussage)
    {platform : Plattform} {category : Category} {tree : category.Tree} {E : Einheit}
    (elaboriert : Elaboriert platform tree E) (akzeptiert : Akzeptiert E)
    {h : Katalog.Umgebung} {ρ : Maschine.Lauf E} (lauf : Maschine.Laeufe E h ρ) :
    ∃ η : I.Lauf E, I.Laeufe E η ∧ I.Sim E ρ η := by
  have same := elab_vollstaendig elaboriert
  subst E
  exact I.sim_akzeptierter_lauf akzeptiert (fun _ => (fragment category tree).simBasis platform)
    (fun _ => sim_formen lokal ruf _ platform) lauf

end Gabbro.Core.Ast.Semantik
