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
theorem geraete_aussen_schritt {s : State} {event : Ereignis}
    (gut : s.SpeicherGut) :
    ∃ g', Speicherfolge s.initial .aussen s.graph
      [aussenEtikett (d.unit locals).einrichtung event]
      [(.aussen, aussenEtikett (d.unit locals).einrichtung event)] g' := by
  have hliest : ¬ (aussenEtikett (d.unit locals).einrichtung event).art.liest := by
    simp [aussenEtikett, Speicher.Art.liest]
  obtain ⟨g', hs⟩ := Speicher.Zustand.schritt_ohne_lesen gut.1 gut.2 .aussen
    (aussenEtikett (d.unit locals).einrichtung event) hliest
  refine ⟨g', ?_⟩
  exact Speicherfolge.cons (Initialisierung.ohne (Or.inl rfl)) hs (Speicherfolge.nil g')

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
    geraete_aussen_schritt (s := s₂) (event := .antwort a) gut₂
  let spur₂ : SchrittSpur Nat UInt8 :=
    ⟨[(SpeicherAkteur.aussen, aussenEtikett (d.unit locals).einrichtung (.antwort a))], [.antwort a]⟩
  refine ⟨spur₂, { s₂.antwort a with graph := g₂ }, ?_, rfl⟩
  exact ⟨geraete_angeboten_aus_kopplung vergleich hkopp hz₁ hz₂ offered₁, rfl, folge₂, rfl⟩

/-- Transport an interrupt entry from the left run to the right at the same cut. -/
theorem geraete_interrupt_transport {h₁ h₂ : Umgebung} {ρ₁ ρ₂ : Lauf (d.unit locals)}
    (vergleich : Vergleich (d.unit locals) h₁ h₂ ρ₁ ρ₂) {predictor : Praediktor} {t : Nat}
    {id : Nat × Nat} {s₁ s₂ n₁ : State} {spur₁ : SchrittSpur Nat UInt8}
    (hkopp : GeraeteKopplungAussage (d.unit locals) ρ₁ ρ₂ predictor t t)
    (hz₁ : ρ₁.zeit.zustand t = some s₁) (hz₂ : ρ₂.zeit.zustand t = some s₂)
    (gut₂ : s₂.SpeicherGut)
    (step₁ : UnterbrechungsSchritt (d.unit locals).einrichtung ρ₁.hw t id s₁ spur₁ n₁) :
    ∃ spur₂ n₂, UnterbrechungsSchritt (d.unit locals).einrichtung ρ₂.hw t id s₂ spur₂ n₂ ∧
      spur₂.aussen = spur₁.aussen := by
  obtain ⟨k, irq, c, nmi, offer₁, pending₁, nimmt₁, ruht₁, spurEq₁, _, nextEq₁⟩ := step₁
  have hang := geraete_angebot_gleich vergleich t
  have hangId := geraete_angebot_gleich vergleich id.1
  have hstate := (geraeteKopplung_kopplung hkopp).2.1 s₁ s₂ hz₁ hz₂
  have hepoche := hstate.2.1
  have hgeliefert := hstate.2.2.1
  have hkerne := hstate.2.2.2.1
  have hstatus := hstate.2.2.2.2
  obtain ⟨g₂, folge₂⟩ :=
    geraete_aussen_schritt (s := s₂) (event := .interrupt k irq .handler) gut₂
  let n₂ : State := { Zustandseintritt s₂ k id c nmi with graph := g₂ }
  let spur₂ : SchrittSpur Nat UInt8 :=
    ⟨[(SpeicherAkteur.aussen, aussenEtikett (d.unit locals).einrichtung (.interrupt k irq .handler))],
      [.interrupt k irq .handler]⟩
  refine ⟨spur₂, n₂, ?_, ?_⟩
  · refine ⟨k, irq, c, nmi, ?_, ?_, ?_, ?_, rfl, ?_, rfl⟩
    · rw [← hang]
      exact offer₁
    · refine ⟨?_, pending₁.2.1, ?_, ?_, ?_⟩
      · rw [← hepoche]
        exact pending₁.1
      · rw [← congrArg (fun a => a.interrupts) hangId]
        exact pending₁.2.2.1
      · rw [← hgeliefert]
        exact pending₁.2.2.2.1
      · rw [← congrArg (fun a => a.interruptAuswahl) hang]
        exact pending₁.2.2.2.2
    · rw [← hkerne]
      exact nimmt₁
    · rw [← hstatus]
      exact ruht₁
    · exact folge₂
  · rw [spurEq₁]

end Gabbro.Core.Beobachtung
