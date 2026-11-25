module

public import Core.Beobachtung.Fluss.Beweise.Geraet.LockstepHilfe

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Gabbro.Core.Ast.LowLevel.Device
open Gabbro.Core.Ast

variable {k : Katalog} {scope : Scope} {locals : Umgebung scope}
variable {d : Denotation k scope}

/-- An outside event always admits a memory continuation on a consistent complete graph. -/
theorem geraete_aussen_schritt {s : State} {f : SpeicherAkteur Nat} {event : Ereignis}
    (gut : s.SpeicherGut) :
    ∃ g', Speicherfolge s.initial f s.graph [aussenEtikett (d.unit locals).einrichtung event]
      [(.aussen, aussenEtikett (d.unit locals).einrichtung event)] g' := by
  let l : Speicher.Etikett Nat UInt8 := aussenEtikett (d.unit locals).einrichtung event
  have hliest : ¬ l.art.liest := by
    simp [l, aussenEtikett, Speicher.Art.liest]
  obtain ⟨g', hs⟩ := Speicher.Zustand.schritt_ohne_lesen gut.1 gut.2 f l hliest
  refine ⟨g', ?_⟩
  exact Speicherfolge.cons (Initialisierung.ohne (Or.inl (by dsimp only [l, aussenEtikett])))
    (by simpa only [l] using hs) (Speicherfolge.nil g')

/-- An offered answer on the left is offered on the right at the same cut with the ledgers
    and epoch that the coupling equates. -/
private theorem geraete_angeboten_aus_kopplung {h₁ h₂ : Umgebung} {ρ₁ ρ₂ : Lauf (d.unit locals)}
    (vergleich : Vergleich (d.unit locals) h₁ h₂ ρ₁ ρ₂) {predictor : Praediktor} {t : Nat}
    (hkopp : GeraeteKopplungAussage (d.unit locals) ρ₁ ρ₂ predictor t t)
    {s₁ s₂ : State} {a : AntwortEreignis}
    (hz₁ : ρ₁.zeit.zustand t = some s₁) (hz₂ : ρ₂.zeit.zustand t = some s₂)
    (offered : s₁.AntwortAngeboten (d.unit locals).katalog ρ₁.hw t a) :
    s₂.AntwortAngeboten (d.unit locals).katalog ρ₂.hw t a := by
  obtain ⟨hfragen, hverlauf, hantworten, _, _⟩ := geraeteKopplung_ledger hkopp hz₁ hz₂
  have hepoche : s₁.epoche = s₂.epoche :=
    (((geraeteKopplung_kopplung hkopp).2.1 s₁ s₂ hz₁ hz₂).2).1
  exact geraete_angeboten_transport vergleich offered hfragen hverlauf hantworten hepoche

/-- Transport an answer step from the left run to the right at the same cut. -/
theorem geraete_antwort_transport {h₁ h₂ : Umgebung} {ρ₁ ρ₂ : Lauf (d.unit locals)}
    (vergleich : Vergleich (d.unit locals) h₁ h₂ ρ₁ ρ₂) {predictor : Praediktor} {t : Nat}
    {a : AntwortEreignis} {s₁ s₂ n₁ : State} {spur₁ : SchrittSpur Nat UInt8}
    (hkopp : GeraeteKopplungAussage (d.unit locals) ρ₁ ρ₂ predictor t t)
    (hz₁ : ρ₁.zeit.zustand t = some s₁) (hz₂ : ρ₂.zeit.zustand t = some s₂)
    (gut₂ : s₂.SpeicherGut)
    (step₁ : AntwortSchritt (d.unit locals).einrichtung (d.unit locals).katalog ρ₁.hw t a s₁ spur₁ n₁) :
    ∃ spur₂ n₂, AntwortSchritt (d.unit locals).einrichtung (d.unit locals).katalog ρ₂.hw t a s₂ spur₂ n₂ ∧
      spur₂.aussen = [.antwort a] := by
  obtain ⟨offered₁, spurEq₁, _, _⟩ := step₁
  obtain ⟨g₂, folge₂⟩ :=
    geraete_aussen_schritt (s := s₂) (f := .aussen) (event := .antwort a) gut₂
  let spur₂ : SchrittSpur Nat UInt8 := ⟨[.aussen, aussenEtikett (d.unit locals).einrichtung (.antwort a)], [.antwort a]⟩
  refine ⟨spur₂, { s₂.antwort a with graph := g₂ }, ?_, rfl⟩
  exact ⟨geraete_angeboten_aus_kopplung vergleich hkopp hz₁ hz₂ offered₁, rfl, folge₂, rfl⟩

end Gabbro.Core.Beobachtung
