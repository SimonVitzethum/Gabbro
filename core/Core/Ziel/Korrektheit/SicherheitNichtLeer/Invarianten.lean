/-
  File:      core/Core/Ziel/Korrektheit/SicherheitNichtLeer/Invarianten.lean
  Subject:   THE INVARIANT FALSIFICATION of `SicherheitNichtLeerInstanzAussage` at the exact frame type:
             an `Ast.Semantik.Einheit` that declares an invariant false everywhere and has an admitted
             stuck run. At the initial cut nobody writes the invariant's index, so
             `InvariantenAmSchnitt` demands the false invariant and fails.
 -/
module

public import Core.Ziel.Korrektheit.SicherheitNichtLeer.Modell

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit.SicherheitNichtLeer

open Gabbro.Core
open Maschine Katalog
open Gabbro.Core.Sicherheit

/-- A loaded unit whose only declared invariant is false and whose rules offer no step. -/
theorem invarianten_nichtLeerInstanz :
    ∃ (E : Modell) (H : Umgebung) (ρ : Lauf E),
      Maschine.Laeufe E H ρ ∧ ¬ InvariantenErhalten (sicherheitVon E) H ρ := by
  let inv : Zustand → Prop := fun _ => False
  let qt : Quelltabellen Zustand := ⟨⟨[], [], [inv]⟩, fun _ _ _ => False⟩
  let E : Modell := einheit start (fun _ _ _ _ => False) qt
  let H : Umgebung := umgebung leer
  let hw : HwLauf := ⟨fun _ => ⟨none, fun _ => false, [], fun _ => false, false, false, 0⟩, H.politik⟩
  have conform : hw.konform katalog H := by
    refine ⟨rfl, fun _ => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · exact fun _ h => nomatch h
    · exact fun _ h => nomatch h
    · exact fun _ h => (List.not_mem_nil h).elim
    · exact fun _ h => nomatch h
    · exact fun h => h.elim (fun h => nomatch h) (fun h => nomatch h)
  have stuck (t : Nat) : KeinSchritt (Lauffolge E hw) t (some start) := by
    intro lab next step
    cases step with
    | schritt step =>
      cases step with
      | kontext _ _ regel _ =>
        obtain ⟨_, _, neg⟩ := regel
        exact neg.elim
      | antwort _ arrived =>
        have delivery := arrived.1.2.1.1
        cases delivery
      | interrupt _ enters =>
        obtain ⟨_, _, _, _, offered, _⟩ := enters
        cases offered
      | absturz crash => exact Bool.false_ne_true crash.1.2
  obtain ⟨a, zul⟩ := zulStart_erfuellbar (erlaubt leer) bild_gueltig
  let ρ : Lauf E := ⟨a, hw, ⟨fun _ => some start, fun _ => none, fun t => .wartet rfl rfl (stuck t)⟩⟩
  have run : Maschine.Laeufe E H ρ :=
    ⟨erlaubt leer, conform, zul, rfl,
      SchedulerFair_aus_stillstand_ab E.maschine ρ 0 (fun t _ s hs ev next step => by
        have hss : s = start := (Option.some.inj hs).symm
        rw [hss] at step
        exact stuck t ev next step)⟩
  refine ⟨E, H, ρ, run, fun safe => ?_⟩
  have cut : Maschine.Schnitt E ρ := ⟨0, Or.inl rfl⟩
  have amSchnitt := safe.1 cut start rfl
  exact amSchnitt.2 0 (⟨none, inv⟩ : Invariante Nat Zustand) rfl
    (fun c hc hschreibt => hschreibt)

end Gabbro.Core.Ziel.Korrektheit.SicherheitNichtLeer
