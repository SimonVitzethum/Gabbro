module

public import Core.Ast.Semantik.Elaborierung
public import Core.Annahme
public import Core.Ideal.Komposition
public import Core.Verfeinerung.Maschine
public import Core.Maschine.Einheit

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog
open Ideal (RegelBestimmt RegelFortschritt)

theorem Befehl.lokal (E : Einheit) (b : Befehl) (rule : E.system.regel b = b.regel)
    (h : b.Privat := by first | exact Or.inl rfl | exact Or.inr rfl | exact Quellform.privat _ _) : RegelLokal E b := by
  intro c s u w p step
  rw [rule] at step
  have same : [p] = [Semantik.plan] := ((b.ideal_privat h c s w [p] u).1 step).1
  cases (List.cons.inj same).1
  exact ⟨fun _ empty => (List.not_mem_nil empty).elim, fun _ empty => (List.not_mem_nil empty).elim⟩

theorem Befehl.bestimmt (b : Befehl)
    (h : b.Privat := by first | exact Or.inl rfl | exact Or.inr rfl | exact Quellform.privat _ _) : RegelBestimmt b.regel :=
  fun c s w es es' s1 s2 left right =>
    let l := (b.ideal_privat h c s w es s1).1 left
    let r := (b.ideal_privat h c s w es' s2).1 right
    ⟨l.1.trans r.1.symm, l.2.trans r.2.symm⟩

theorem Befehl.fortschritt (p : Fragment) (b : Befehl)
    (h : b.Privat := by first | exact Or.inl rfl | exact Or.inr rfl | exact Quellform.privat _ _) :
    RegelFortschritt (system p.code) b :=
  fun s c _ => Or.inl ⟨(), [Semantik.plan], b.nach c s, (b.ideal_privat h c s () [Semantik.plan] (b.nach c s)).2 ⟨rfl, rfl⟩⟩

theorem Befehl.vollzug (e : Einrichtung Nat Zelle Int Nat Rahmen PUnit PUnit)
    (b : Befehl) (t : Nat) (c : Kontext) (s : Zustand) :
    FuehrtSchrittAus e t c s (b.nach c s) Semantik.plan ⟨[], []⟩ (b.nach c s) :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    fun _ empty => (List.not_mem_nil empty).elim, [], _, .intern, .nil _, rfl⟩

theorem Befehl.komponierbar (p : Fragment) (platform : Plattform) (b : Befehl)
    (h : b.Privat := by first | exact Or.inl rfl | exact Or.inr rfl | exact Quellform.privat _ _) :
    I.RegelKomponierbar (p.einheit platform).einrichtung (p.einheit platform).system b := by
  intro t s c w plans u _ _ step
  obtain ⟨same, after⟩ : plans = [Semantik.plan] ∧ u = b.nach c s := (b.ideal_privat h c s w plans u).1 step
  subst u
  exact ⟨Semantik.plan, ⟨[], []⟩, b.nach c s, same, b.vollzug _ t c s⟩

theorem Befehl.vollzug_genau (b : Befehl) {e t c s u w p spur s'}
    (rule : b.impl c s w [p] u) (execute : FuehrtSchrittAus e t c s u p spur s')
    (h : b.Privat := by first | exact Or.inl rfl | exact Or.inr rfl | exact Quellform.privat _ _) :
    spur = ⟨[], []⟩ ∧ s' = b.nach c s := by
  have transfer := (b.impl_privat h c s w [p] u).1 rule
  have same : [p] = [Semantik.plan] := transfer.1
  have after : u = b.nach c s := transfer.2
  subst u
  cases (List.cons.inj same).1
  obtain ⟨_, _, _, _, action, memory, next⟩ := execute
  cases spur with
  | mk events outside =>
    cases action
    simp only [Semantik.plan, List.nil_append, schreibEreignisse, List.map_nil, List.filter_nil,
      List.append_nil] at memory
    have unchanged : ∀ {recorded graph},
        Speicherfolge s.initial (.kontext c) s.graph [] recorded graph →
          recorded = [] ∧ graph = s.graph := by
      intro _ _ run
      cases run
      exact ⟨rfl, rfl⟩
    have hmem := unchanged memory
    rw [hmem.1]
    rw [hmem.2] at next
    exact ⟨rfl, next⟩

theorem Befehl.abgleich (p : Fragment) (platform : Plattform) (b : Befehl) :
    I.RegelAbgleich (p.einheit platform) b := by
  intro hw t c w s u s' i stepPlan spur related normal ready head impl execute
  obtain ⟨protocol, frames⟩ := related
  change s.lokal = i.lokal at frames
  change { s with lokal := i.lokal } = i at protocol
  rw [← frames] at protocol
  subst i
  exact Or.inl ⟨s', .kontext normal ready ⟨b, head, impl⟩ execute, I.ProtokollBezug.refl _, rfl⟩

/-- Every instruction is its unit's single linearisation point. The mover relations
    concern steps strictly before and after that point, so both are empty. -/
def Befehl.vor (_ : Befehl) : Zustand → Zustand → Prop := fun _ _ => False

def Befehl.danach (_ : Befehl) : Zustand → Zustand → Prop := fun _ _ => False

theorem Befehl.kommutation (b : Befehl) (andere : Zustand → Zustand → Prop) :
    Kommutation b.vor b.danach andere :=
  ⟨fun _ _ _ h _ => h.elim, fun _ _ _ _ h => h.elim⟩

theorem Fragment.fertig (p : Fragment) (platform : Plattform) :
    ∀ s c, (p.einheit platform).system.kopf s c = none → (p.einheit platform).system.fertig s c :=
  fun _ _ finished => finished

theorem Fragment.bereit_eindeutig (p : Fragment) (platform : Plattform)
    (step : (p.einheit platform).system.ISchritt c s w plans u) :
    ¬ (p.einheit platform).system.fertig s c ∧ ∀ reason, ¬ (p.einheit platform).system.blockiert s c reason := by
  obtain ⟨b, head, _⟩ := step
  exact ⟨fun finished => (Option.some_ne_none b) (head.symm.trans finished), fun _ blocked => blocked⟩

end Gabbro.Core.Ast.Semantik
