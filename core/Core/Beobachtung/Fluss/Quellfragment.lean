module

public import Core.Beobachtung.Fluss.Quellregel
public import Core.Ast.Semantik.Elaborierung

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Ast.Semantik (Fragment)

/-- The fragment reads its public region grants at boot. Its forms change only
    the current frame, using the declared local and region-authority inputs. -/
theorem fragment_fluss_lokal (p : Fragment) (plattform : Plattform) :
    FlussLokal (p.einheit plattform) := by
  constructor
  · intro s₁ s₂ gleich
    have regionen : s₁.regions = s₂.regions := congrArg (fun proj => proj.2.2.1) gleich
    refine ⟨?_, fun _ => rfl, fun _ => rfl, ?_, rfl, fun _ => rfl⟩
    · intro c _ _
      simp only [I.start, Ast.Semantik.Fragment.einheit, Ast.Semantik.startdaten, Zustand.start, regionen]
    · simp only [I.start, Ast.Semantik.Fragment.einheit, Ast.Semantik.startdaten, Zustand.start, regionen]
  · intro f
    constructor
    · intro c v w plan u _
      refine ⟨⟨rfl, fun _ _ _ mem => (List.not_mem_nil mem).elim⟩, fun privat => ?_⟩
      exact (Bool.false_ne_true privat.symm).elim
    · intro _ c v₁ w₁ p₁ u₁ v₂ w₂ p₂ u₂ gleich links rechts
      have transfer₁ : [p₁] = [Ast.Semantik.plan] ∧ u₁ = f.nach c v₁ := links.2
      have transfer₂ : [p₂] = [Ast.Semantik.plan] ∧ u₂ = f.nach c v₂ := rechts.2
      rw [(List.cons.inj transfer₁.1).1, (List.cons.inj transfer₂.1).1, transfer₁.2, transfer₂.2]
      obtain ⟨lokale, ende, initial, rechte, leihen, antwort⟩ := gleich
      refine ⟨⟨?_, ende, initial, rechte, leihen, antwort⟩, rfl, rfl⟩
      have lokal : v₁.lokal = v₂.lokal :=
        funext fun d => lokale d ⟨0, Nat.zero_lt_succ _⟩ rfl
      have region : Ast.Semantik.Zustand.regionLive v₁ c = Ast.Semantik.Zustand.regionLive v₂ c := by
        funext slot
        simp only [Ast.Semantik.Zustand.regionLive, rechte, leihen]
      intro d _ _
      change Function.update v₁.lokal c (f.auswerten (v₁.lokal c) (Ast.Semantik.Zustand.regionLive v₁ c)) d =
        Function.update v₂.lokal c (f.auswerten (v₂.lokal c) (Ast.Semantik.Zustand.regionLive v₂ c)) d
      rw [lokal, region]

end Gabbro.Core.Beobachtung
