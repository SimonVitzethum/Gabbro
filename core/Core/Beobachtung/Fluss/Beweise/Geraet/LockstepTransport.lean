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

/-- Transport a device issue step from the left run to the right at the same cut.
    The outside memory continuation is rebuilt with `schritt_ohne_lesen`; the ledger
    and machine-field post-equalities come from `geraete_issue_tick` on both sides. -/
theorem geraete_issue_transport {h₁ h₂ : Umgebung} {ρ₁ ρ₂ : Lauf (d.unit locals)}
    (vergleich : Vergleich (d.unit locals) h₁ h₂ ρ₁ ρ₂) {predictor : Praediktor} {t : Nat}
    {binding : Binding k} {access : RegisterAccess}
    {required : GeraetePhase} {target : Option GeraetePhase} {c : Kontext} {w : PUnit}
    {s₁ s₂ u₁ n₁ : State} {spur₁ : SchrittSpur Nat UInt8} {plan : Plan}
    (hkopp : GeraeteKopplungAussage (d.unit locals) ρ₁ ρ₂ predictor t t)
    (hz₁ : ρ₁.zeit.zustand t = some s₁) (hz₂ : ρ₂.zeit.zustand t = some s₂)
    (gut₂ : s₂.SpeicherGut)
    (quell : QuellzustandGleich (d.unit locals) s₁ s₂)
    (regel₁ : (d.unit locals).system.ImplSchritt c s₁ w [plan] u₁)
    (ruleEq : d.rule locals = Rule.machine binding access required target)
    (aus₁ : FuehrtSchrittAus (d.unit locals).einrichtung t c s₁ u₁ plan spur₁ n₁)
    (hplans : [plan] = [{ internal with aktion := .frage (binding.question access) }])
    (hu : u₁ = setFrame s₁ c { s₁.lokal c with pending := some (binding.question access) })
    (owned : Befugt binding required access s₁ c)
    (idle : (s₁.lokal c).pending = none) :
    ∃ spur₂ u₂ n₂,
      (d.unit locals).system.ImplSchritt c s₂ w [plan] u₂ ∧
      FuehrtSchrittAus (d.unit locals).einrichtung t c s₂ u₂ plan spur₂ n₂ ∧
      spur₂.aussen = spur₁.aussen ∧
      GeraeteLedgerGleichAussage n₁ n₂ ∧ n₁.buchung = n₂.buchung ∧
      n₁.epoche = n₂.epoche ∧ n₁.geliefert = n₂.geliefert ∧
      n₁.kerne = n₂.kerne ∧ n₁.status = n₂.status ∧
      QuellzustandGleich (d.unit locals) n₁ n₂ := by
  obtain ⟨kopf₁, impl₁⟩ := geraete_kontext_regel ruleEq regel₁
  have hbuch := geraeteKopplung_buchung hkopp hz₁ hz₂
  have hlokal := geraete_lokal_gleich quell
  have hledger := geraeteKopplung_ledger hkopp hz₁ hz₂
  obtain ⟨hfragen, hverlauf, hantworten, hverbraucht, hverworfen⟩ := hledger
  have hstate := (geraeteKopplung_kopplung hkopp).2.1 s₁ s₂ hz₁ hz₂
  have hepoche := hstate.2.1
  have hgeliefert := hstate.2.2.1
  have hkerne := hstate.2.2.2.1
  have hstatus := hstate.2.2.2.2
  have owned₂ : Befugt binding required access s₂ c :=
    geraete_befugt_transport owned hbuch hlokal
  have idle₂ : (s₂.lokal c).pending = none := by
    rw [← geraete_kopplung_pending hkopp hz₁ hz₂ c]
    exact idle
  have kopf₂ : (d.unit locals).system.kopf s₂ c = some () :=
    geraeteKopfGleich locals d quell hstatus kopf₁
  let u₂ : State := setFrame s₂ c { s₂.lokal c with pending := some (binding.question access) }
  have impl₂ : ((d.unit locals).system.regel ()).impl c s₂ w [plan] u₂ := by
    dsimp only [Denotation.unit, Gabbro.Core.Ast.LowLevel.Device.unit]
    rw [ruleEq]
    dsimp only [Rule.machine]
    exact ⟨plan, rfl, Rule.issue owned₂ idle₂⟩
  have regel₂ : (d.unit locals).system.ImplSchritt c s₂ w [plan] u₂ := ⟨(), kopf₂, impl₂⟩
  let e₂ : FrageEreignis := s₂.stelleFrage t c (binding.question access)
  obtain ⟨g₂, folge₂⟩ := geraete_aussen_schritt (s := s₂)
    (event := .frage e₂) gut₂
  let spur₂ : SchrittSpur Nat UInt8 :=
    ⟨[(SpeicherAkteur.kontext c, aussenEtikett (d.unit locals).einrichtung (.frage e₂))],
      [.frage e₂]⟩
  let n₂ : State := { u₂.frage e₂ with graph := g₂ }
  have aus₂ : FuehrtSchrittAus (d.unit locals).einrichtung t c s₂ u₂ plan spur₂ n₂ := by
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · intro l hl
      simp only [hplans] at hl
      exact False.elim (by simpa only [List.mem_singleton] using hl)
    · refine ⟨[], u₂.frage e₂, ?_, ?_, rfl⟩
      · exact FuehrtAus.frage (binding.question access)
      · simpa only [hplans, internal, schreibEreignisse, List.filter_nil, List.map_nil,
          List.nil_append, List.append_nil, List.map_cons] using folge₂
  obtain ⟨spurEq₁, hfragen₁, hverlauf₁, hantworten₁, hverbraucht₁, hverworfen₁, hbuchung₁,
    hepoche₁, hgeliefert₁, hkerne₁, hstatus₁, hlokal₁, hpending₁, hinitial₁, hrechte₁,
    hleihen₁, hpersistenz₁, heinst₁, hectx₁, hecut₁, heq₁⟩ :=
    geraete_issue_tick (target := target) aus₁ hplans rfl owned idle
  have hplans₂ : [plan] = [{ internal with aktion := .frage (binding.question access) }] := hplans
  obtain ⟨spurEq₂, hfragen₂, hverlauf₂, hantworten₂, hverbraucht₂, hverworfen₂, hbuchung₂,
    hepoche₂, hgeliefert₂, hkerne₂, hstatus₂, hlokal₂, hpending₂, hinitial₂, hrechte₂,
    hleihen₂, hpersistenz₂, heinst₂, hectx₂, hecut₂, heq₂⟩ :=
    geraete_issue_tick (target := target) aus₂ hplans₂ rfl owned₂ idle₂
  have heq : (s₁.stelleFrage t c (binding.question access)) =
      (s₂.stelleFrage t c (binding.question access)) := by
    simp only [Zustand.stelleFrage, hfragen]
  have hquell : QuellzustandGleich (d.unit locals) n₁ n₂ := by
    have hform₁ : FormSchritt (d.unit locals) () c s₁ () plan u₁ := ⟨kopf₁, impl₁⟩
    have hform₂ : FormSchritt (d.unit locals) () c s₂ () plan u₂ := ⟨kopf₂, impl₂⟩
    have hq := (geraeteSchrittNI locals d c s₁ s₂ () plan plan u₁ u₂ quell hform₁ hform₂).1
    simpa only [Zustand.frage] using hq
  refine ⟨spur₂, u₂, n₂, regel₂, aus₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hquell⟩
  · rw [spurEq₁, spurEq₂, heq]
  · exact ⟨by rw [hfragen₁, hfragen₂, heq], by rw [hverlauf₁, hverlauf₂, hfragen, heq],
      by rw [hantworten₁, hantworten₂, hantworten],
      by rw [hverbraucht₁, hverbraucht₂, hverbraucht],
      by rw [hverworfen₁, hverworfen₂, hverworfen]⟩
  · rw [hbuchung₁, hbuchung₂, hbuch]
  · rw [hepoche₁, hepoche₂, hepoche]
  · rw [hgeliefert₁, hgeliefert₂, hgeliefert]
  · rw [hkerne₁, hkerne₂, hkerne]
  · rw [hstatus₁, hstatus₂, hstatus]

end Gabbro.Core.Beobachtung
