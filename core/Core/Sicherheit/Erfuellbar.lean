module

public import Core.Sicherheit.SpeicherNichtLeer
public import Core.Sicherheit.InvariantenNichtLeer
public import Core.Sicherheit.AussenNichtLeer

@[expose] public section

namespace Gabbro.Core.Sicherheit

open Maschine Katalog Laufkonstruktion

/-- The four refutations at their concrete implementation types. -/
theorem sicherheit_nichtLeer :
    (∃ (E : Modell) (H : Umgebung) (ρ : Lauf E), Maschine.Laeufe E.maschine H ρ ∧ ¬ Speichersicher E H ρ) ∧
    (∃ (E : Modell) (H : Umgebung) (ρ : Lauf E), Maschine.Laeufe E.maschine H ρ ∧ ¬ InvariantenErhalten E H ρ) ∧
    (∃ (E : Modell) (H : Umgebung) (ρ : Lauf E), Maschine.Laeufe E.maschine H ρ ∧ ¬ Rennfrei E H ρ) ∧
    (∃ (E : Modell) (H : Umgebung) (ρ : Lauf E), Maschine.Laeufe E.maschine H ρ ∧ ¬ ToctouFrei E H ρ) :=
  ⟨speichersicher_nichtLeer, invarianten_nichtLeer, rennfrei_nichtLeer, toctoufrei_nichtLeer⟩

/-- A loaded unit with a true declaration and no offered steps satisfies all four predicates. -/
theorem sicherheit_erfuellbar :
    ∃ (E : Modell) (H : Umgebung) (ρ : Lauf E), Maschine.Laeufe E.maschine H ρ ∧
      Speichersicher E H ρ ∧ InvariantenErhalten E H ρ ∧ Rennfrei E H ρ ∧ ToctouFrei E H ρ := by
  let d : Invariante Unit Laufkonstruktion.Zustand := ⟨none, fun _ => True⟩
  let E := einheit start (fun _ _ _ _ => False) [d]
  let H := umgebung leer
  let hw : HwLauf := ⟨fun _ => ⟨none, fun _ => false, [], fun _ => false, false, false, 0⟩, H.politik⟩
  have conform : hw.konform katalog H := by
    refine ⟨rfl, fun _ => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · exact fun _ h => nomatch h
    · exact fun _ h => nomatch h
    · exact fun _ h => (List.not_mem_nil h).elim
    · exact fun _ h => nomatch h
    · exact fun h => h.elim (fun h => nomatch h) (fun h => nomatch h)
  have stuck (t : Nat) : KeinSchritt (Lauffolge E.maschine hw) t (some start) := by
    intro lab next step
    cases step with
    | schritt step =>
      cases step with
      | kontext _ ready _ _ =>
        obtain ⟨k, h, _⟩ := ready
        cases h
      | antwort _ arrived =>
        have delivery := arrived.1.2.1.1
        cases delivery
      | interrupt _ interrupt =>
        obtain ⟨k, _, _, _, offered, _⟩ := interrupt
        cases offered
      | absturz offered =>
        have no := offered.1.2
        cases no
  obtain ⟨a, zul⟩ := zulStart_erfuellbar (erlaubt leer) bild_gueltig
  let ρ : Lauf E := ⟨a, hw, ⟨fun _ => some start, fun _ => none, fun t => .wartet rfl rfl (stuck t)⟩⟩
  have keine (t vor spur nach) : ¬ Uebergang E ρ t vor spur nach := by
    rintro ⟨_, ⟨_, lab⟩, _⟩
    cases lab
  have init (t : Nat) (s : Laufkonstruktion.Zustand) (hs : ρ.zeit.zustand t = some s) : start = s :=
    Option.some.inj hs
  have fair : SchedulerFair E.maschine ρ :=
    SchedulerFair_aus_stillstand_ab E.maschine ρ 0 (fun t _ s hs ev next step => by
      have hss : s = start := (Option.some.inj hs).symm
      rw [hss] at step
      exact stuck t ev next step)
  refine ⟨E, H, ρ, ⟨erlaubt leer, conform, zul, rfl, fair⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun s h => ?_, fun t vor spur nach h => (keine t vor spur nach h).elim⟩
    rw [← init 0 s h]
    exact ⟨rfl, rfl⟩
  · refine ⟨fun t s h => ?_, fun t vor spur nach h => (keine t vor spur nach h).elim⟩
    rw [← init t.val s h]
    refine ⟨fun _ _ => trivial, fun i invariant hi _ => ?_⟩
    cases i with
    | zero => have same : d = invariant := Option.some.inj hi; subst invariant; trivial
    | succ i =>
      have bad : ([] : List (Invariante Unit Laufkonstruktion.Zustand))[i]? = some invariant := hi
      rw [List.getElem?_nil] at bad
      cases bad
  · refine ⟨fun t s h => ?_, fun t vor spur nach h => (keine t vor spur nach h).elim⟩
    rw [← init t.val s h]
    exact fun i _ _ => (Speicher.Zustand.leer_elim i).elim
  · refine ⟨fun s h => ?_, fun t vor spur nach h => (keine t vor spur nach h).elim⟩
    rw [← init 0 s h]
    rfl

end Gabbro.Core.Sicherheit
