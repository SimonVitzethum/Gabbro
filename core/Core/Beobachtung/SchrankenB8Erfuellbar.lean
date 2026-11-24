module

public import Core.Beobachtung.SchrankenB8
public import Core.Annahme.HostedLauf

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine Annahme
open Annahme.Hosted

/-- The hosted unit carries no declarations: every bound is open and no mark is ever visible,
    so the B8 prefix holds at every cut of every admitted run. -/
private theorem hosted_prefix {bytes : List UInt8} {ρ : Lauf einheit}
    (lauf : Laeufe einheit (umgebung bytes) ρ) (t : Nat) : B8Prefix einheit ρ t := by
  refine ⟨?_, ?_, ?_⟩
  · intro n h
    cases h
  · intro l c a n _ _
    have e : einheit.schranken.halten l = none := rfl
    intro m h
    rw [e] at h
    cases h
  · intro t' s _ _ c m hmem
    have leer : einheit.schranken.zeitstand (s.lokal c) = [] := rfl
    rw [leer] at hmem
    exact (List.not_mem_nil hmem).elim

/-- The start bundle holds jointly: an admitted run whose initial cut satisfies the B8 prefix. -/
theorem b8_start_erfuellbar :
    ∃ (E : Einheit Unit Unit Unit Unit (Option Handle) Unit Unit Unit Unit)
      (h : Umgebung) (ρ : Lauf E),
      Laeufe E h ρ ∧ B8Prefix E ρ 0 := by
  obtain ⟨s, zul⟩ := zulStart_erfuellbar (erlaubt []) Sicherheit.Laufkonstruktion.bild_gueltig
  obtain ⟨ρ, _, _, lauf, _, _, _, _, _, _, _, _, _, _⟩ := konkreter_lauf zul []
  exact ⟨_, _, _, lauf, hosted_prefix lauf 0⟩

/-- The rule bundle holds jointly: an admitted run with a form step at cut `0` (the hosted
    `binde` step of the single form `()`) and the B8 prefix below it. -/
theorem b8_regel_erfuellbar :
    ∃ (E : Einheit Unit Unit Unit Unit (Option Handle) Unit Unit Unit Unit)
      (h : Umgebung) (ρ : Lauf E) (t : Nat) (c : Kontext)
      (w : Unit) (spur : Spur) (vor nach : Zustand) (f : Unit),
      Laeufe E h ρ ∧ B8Prefix E ρ t ∧ ρ.zeit.zustand t = some vor ∧
      E.system.kopf vor c = some f ∧ ρ.zeit.spur t = some (.kontext c w, spur) ∧
      ρ.zeit.zustand (t + 1) = some nach := by
  obtain ⟨s, zul⟩ := zulStart_erfuellbar (erlaubt []) Sicherheit.Laufkonstruktion.bild_gueltig
  obtain ⟨ρ, _, _, lauf, _, _, za0, za1, _, _, ea0, _, _, _⟩ := konkreter_lauf zul []
  exact ⟨_, _, _, _, _, _, _, _, _, _, lauf, hosted_prefix lauf 0, za0, rfl, ea0, za1⟩

/-- The protocol bundle holds jointly: an admitted run with an answer transition at cut `2`
    and the B8 prefix below it. -/
theorem b8_protokoll_erfuellbar :
    ∃ (E : Einheit Unit Unit Unit Unit (Option Handle) Unit Unit Unit Unit)
      (h : Umgebung) (ρ : Lauf E) (t : Nat)
      (w : SchrittWahl Unit) (spur : SchrittSpur Unit Unit) (vor nach : Zustand),
      Laeufe E h ρ ∧ B8Prefix E ρ t ∧ ρ.zeit.zustand t = some vor ∧
      ρ.zeit.spur t = some (.antwort w, spur) ∧ ProtokollB8Wahl (.antwort w) ∧
      ρ.zeit.zustand (t + 1) = some nach := by
  obtain ⟨s, zul⟩ := zulStart_erfuellbar (erlaubt []) Sicherheit.Laufkonstruktion.bild_gueltig
  obtain ⟨ρ, g, g', lauf, _, _, _, _, za2, za3, _, _, ea2, _⟩ := konkreter_lauf zul []
  exact ⟨einheit, umgebung [], ρ, 2, SchrittWahl.antwort (angekommen s []), antwortSpur s [],
    fragend s g, fertig s [] g g', lauf, hosted_prefix lauf 2, za2, ea2, trivial, za3⟩

end Gabbro.Core.Beobachtung
