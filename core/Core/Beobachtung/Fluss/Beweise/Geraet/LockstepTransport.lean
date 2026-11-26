module

public import Core.Beobachtung.Fluss.Beweise.Geraet.LockstepHilfe
public import Core.Beobachtung.Fluss.Beweise.GeraetSchritt

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Gabbro.Core.Ast.LowLevel.Device
open Gabbro.Core.Ast.LowLevel (entryContext)
open Gabbro.Core.Ast

variable {k : Katalog} {scope : Scope} {locals : Umgebung scope}
variable {d : Denotation k scope}

/-- An outside event always admits a memory continuation on a consistent complete graph. -/
theorem geraete_aussen_schritt {s : State} {f : SpeicherAkteur Nat} {event : Ereignis}
    (gut : s.SpeicherGut) :
    ∃ g', Speicherfolge s.initial f s.graph
      [aussenEtikett (d.unit locals).einrichtung event]
      [(f, aussenEtikett (d.unit locals).einrichtung event)] g' := by
  have hliest : ¬ (aussenEtikett (d.unit locals).einrichtung event).art.liest := by
    simp only [aussenEtikett, Speicher.Art.liest, not_false_eq_true]
  obtain ⟨g', hs⟩ := Speicher.Zustand.schritt_ohne_lesen gut.1 gut.2 f
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
    geraete_aussen_schritt (s := s₂) (f := .aussen) (event := .antwort a) gut₂
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
    geraete_aussen_schritt (s := s₂) (f := .aussen) (event := .interrupt k irq .handler) gut₂
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
  have hplanF : plan = { internal with aktion := .frage (binding.question access) } :=
    (List.cons.inj hplans).1
  obtain ⟨kopf₁, plan', hplans', rule₁⟩ := geraete_kontext_regel ruleEq regel₁
  have hbuch := geraeteKopplung_buchung hkopp hz₁ hz₂
  have hlokal := geraete_lokal_gleich quell
  obtain ⟨hfragen, hverlauf, hantworten, hverbraucht, hverworfen⟩ :=
    geraeteKopplung_ledger hkopp hz₁ hz₂
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
    refine ⟨{ internal with aktion := .frage (binding.question access) }, hplans, ?_⟩
    exact Rule.issue owned₂ idle₂
  have regel₂ : (d.unit locals).system.ImplSchritt c s₂ w [plan] u₂ := ⟨(), kopf₂, impl₂⟩
  let e₂ : FrageEreignis := s₂.stelleFrage t c (binding.question access)
  obtain ⟨g₂, folge₂⟩ := geraete_aussen_schritt (s := s₂) (f := .kontext c)
    (event := .frage e₂) gut₂
  let spur₂ : SchrittSpur Nat UInt8 :=
    ⟨[(SpeicherAkteur.kontext c, aussenEtikett (d.unit locals).einrichtung (.frage e₂))],
      [.frage e₂]⟩
  let n₂ : State := { u₂.frage e₂ with graph := g₂ }
  have aus₂ : FuehrtSchrittAus (d.unit locals).einrichtung t c s₂ u₂ plan spur₂ n₂ := by
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · intro l hl
      rw [hplanF] at hl
      cases hl
    · refine ⟨[], u₂.frage e₂, ?_, ?_, rfl⟩
      · rw [hplanF]
        exact FuehrtAus.frage (binding.question access)
      · rw [hplanF]
        dsimp only [spur₂, n₂]
        simpa only [internal, schreibEreignisse, List.filter_nil, List.map_nil,
          List.nil_append, List.append_nil, List.map_cons] using folge₂
  obtain ⟨spurEq₁, hfragen₁, hverlauf₁, hantworten₁, hverbraucht₁, hverworfen₁, hbuchung₁,
    hepoche₁, hgeliefert₁, hkerne₁, hstatus₁, hlokal₁, hpending₁, hinitial₁, hrechte₁,
    hleihen₁, hpersistenz₁, heinst₁, hectx₁, hecut₁, heq₁⟩ :=
    geraete_issue_tick (target := target) aus₁ hplans hu owned idle
  obtain ⟨spurEq₂, hfragen₂, hverlauf₂, hantworten₂, hverbraucht₂, hverworfen₂, hbuchung₂,
    hepoche₂, hgeliefert₂, hkerne₂, hstatus₂, hlokal₂, hpending₂, hinitial₂, hrechte₂,
    hleihen₂, hpersistenz₂, heinst₂, hectx₂, hecut₂, heq₂⟩ :=
    geraete_issue_tick (target := target) aus₂ hplans rfl owned₂ idle₂
  have heq : (s₁.stelleFrage t c (binding.question access)) =
      (s₂.stelleFrage t c (binding.question access)) := by
    simp only [Zustand.stelleFrage, hfragen]
  have impl₁Ideal : ((d.unit locals).system.regel ()).ideal c s₁ () [plan] u₁ := by
    dsimp only [Denotation.unit, Gabbro.Core.Ast.LowLevel.Device.unit]
    rw [ruleEq]
    dsimp only [Rule.machine]
    exact ⟨plan', hplans', rule₁⟩
  have impl₂Ideal : ((d.unit locals).system.regel ()).ideal c s₂ () [plan] u₂ := by
    dsimp only [Denotation.unit, Gabbro.Core.Ast.LowLevel.Device.unit]
    rw [ruleEq]
    dsimp only [Rule.machine]
    refine ⟨{ internal with aktion := .frage (binding.question access) }, hplans, ?_⟩
    exact Rule.issue owned₂ idle₂
  have hquell : QuellzustandGleich (d.unit locals) n₁ n₂ := by
    have hform₁ : FormSchritt (d.unit locals) () c s₁ () plan u₁ := ⟨kopf₁, impl₁Ideal⟩
    have hform₂ : FormSchritt (d.unit locals) () c s₂ () plan u₂ := ⟨kopf₂, impl₂Ideal⟩
    have hq := (geraeteSchrittNI locals d c s₁ s₂ () plan plan u₁ u₂ quell hform₁ hform₂).1
    have n1lokal : n₁.lokal = u₁.lokal := by rw [hlokal₁, hu]; rfl
    have n2lokal : n₂.lokal = u₂.lokal := by rw [hlokal₂]; rfl
    have n1status : n₁.status = u₁.status := by rw [hstatus₁, hu]; rfl
    have n2status : n₂.status = u₂.status := by rw [hstatus₂]; rfl
    have n1initial : n₁.initial = u₁.initial := by rw [hinitial₁, hu]; rfl
    have n2initial : n₂.initial = u₂.initial := by rw [hinitial₂]; rfl
    have n1rechte : n₁.rechte = u₁.rechte := by rw [hrechte₁, hu]; rfl
    have n2rechte : n₂.rechte = u₂.rechte := by rw [hrechte₂]; rfl
    have n1leihen : n₁.leihen = u₁.leihen := by rw [hleihen₁, hu]; rfl
    have n2leihen : n₂.leihen = u₂.leihen := by rw [hleihen₂]; rfl
    have n1antwort : n₁.naechsteAntwort = u₁.naechsteAntwort := by
      funext c'
      rw [hu]
      simp only [Zustand.naechsteAntwort, Zustand.angekommen, hantworten₁, hverbraucht₁,
        hverworfen₁, Zustand.frage, setFrame]
    have n2antwort : n₂.naechsteAntwort = u₂.naechsteAntwort := by
      funext c'
      simp only [Zustand.naechsteAntwort, Zustand.angekommen, hantworten₂, hverbraucht₂,
        hverworfen₂, Zustand.frage, u₂, setFrame]
    unfold QuellzustandGleich at hq ⊢
    unfold AntwortSicht at hq ⊢
    simpa only [n1lokal, n2lokal, n1status, n2status, n1initial, n2initial, n1rechte,
      n2rechte, n1leihen, n2leihen, n1antwort, n2antwort] using hq
  refine ⟨spur₂, u₂, n₂, regel₂, aus₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hquell⟩
  · rw [spurEq₁, spurEq₂, heq]
  · exact ⟨by rw [hfragen₁, hfragen₂, heq, hfragen], by rw [hverlauf₁, hverlauf₂, heq, hverlauf],
      by rw [hantworten₁, hantworten₂, hantworten],
      by rw [hverbraucht₁, hverbraucht₂, hverbraucht],
      by rw [hverworfen₁, hverworfen₂, hverworfen]⟩
  · rw [hbuchung₁, hbuchung₂, hbuch]
  · rw [hepoche₁, hepoche₂, hepoche]
  · rw [hgeliefert₁, hgeliefert₂, hgeliefert]
  · rw [hkerne₁, hkerne₂, hkerne]
  · rw [hstatus₁, hstatus₂, hstatus]

/-- Transport a device consume step from the left run to the right at the same cut. -/
theorem geraete_consume_transport {h₁ h₂ : Umgebung} {ρ₁ ρ₂ : Lauf (d.unit locals)}
    (vergleich : Vergleich (d.unit locals) h₁ h₂ ρ₁ ρ₂) {predictor : Praediktor} {t : Nat}
    {binding : Binding k} {access : RegisterAccess}
    {required : GeraetePhase} {target : Option GeraetePhase} {c : Kontext} {w : PUnit}
    {s₁ s₂ u₁ n₁ : State} {spur₁ : SchrittSpur Nat UInt8} {plan : Plan}
    {answer : AntwortEreignis}
    (hkopp : GeraeteKopplungAussage (d.unit locals) ρ₁ ρ₂ predictor t t)
    (hz₁ : ρ₁.zeit.zustand t = some s₁) (hz₂ : ρ₂.zeit.zustand t = some s₂)
    (quell : QuellzustandGleich (d.unit locals) s₁ s₂)
    (regel₁ : (d.unit locals).system.ImplSchritt c s₁ w [plan] u₁)
    (ruleEq : d.rule locals = Rule.machine binding access required target)
    (aus₁ : FuehrtSchrittAus (d.unit locals).einrichtung t c s₁ u₁ plan spur₁ n₁)
    (hplans : [plan] = [{ internal with aktion := .verbrauche answer }])
    (hu : u₁ = setFrame s₁ c (geraete_consume_rahmen s₁ c binding access answer target))
    (owned : Befugt binding required access s₁ c)
    (pending : (s₁.lokal c).pending = some (binding.question access))
    (ready : s₁.naechsteAntwort c = some answer)
    (sameQuestion : answer.question = binding.question access) :
    ∃ spur₂ u₂ n₂,
      (d.unit locals).system.ImplSchritt c s₂ w [plan] u₂ ∧
      FuehrtSchrittAus (d.unit locals).einrichtung t c s₂ u₂ plan spur₂ n₂ ∧
      spur₂.aussen = spur₁.aussen ∧
      GeraeteLedgerGleichAussage n₁ n₂ ∧ n₁.buchung = n₂.buchung ∧
      n₁.epoche = n₂.epoche ∧ n₁.geliefert = n₂.geliefert ∧
      n₁.kerne = n₂.kerne ∧ n₁.status = n₂.status ∧
      QuellzustandGleich (d.unit locals) n₁ n₂ := by
  have hplanF : plan = { internal with aktion := .verbrauche answer } := (List.cons.inj hplans).1
  obtain ⟨kopf₁, plan', hplans', rule₁⟩ := geraete_kontext_regel ruleEq regel₁
  have hbuch := geraeteKopplung_buchung hkopp hz₁ hz₂
  have hlokal := geraete_lokal_gleich quell
  obtain ⟨hfragen, hverlauf, hantworten, hverbraucht, hverworfen⟩ :=
    geraeteKopplung_ledger hkopp hz₁ hz₂
  have hstate := (geraeteKopplung_kopplung hkopp).2.1 s₁ s₂ hz₁ hz₂
  have hepoche := hstate.2.1
  have hgeliefert := hstate.2.2.1
  have hkerne := hstate.2.2.2.1
  have hstatus := hstate.2.2.2.2
  have owned₂ : Befugt binding required access s₂ c :=
    geraete_befugt_transport owned hbuch hlokal
  have pending₂ : (s₂.lokal c).pending = some (binding.question access) := by
    rw [← geraete_kopplung_pending hkopp hz₁ hz₂ c]
    exact pending
  have ready₂ : s₂.naechsteAntwort c = some answer := by
    rw [← geraete_antwort_gleich quell]
    exact ready
  have kopf₂ : (d.unit locals).system.kopf s₂ c = some () :=
    geraeteKopfGleich locals d quell hstatus kopf₁
  let u₂ : State := setFrame s₂ c (geraete_consume_rahmen s₂ c binding access answer target)
  have impl₂Ideal : ((d.unit locals).system.regel ()).ideal c s₂ () [plan] u₂ := by
    dsimp only [Denotation.unit, Gabbro.Core.Ast.LowLevel.Device.unit]
    rw [ruleEq]
    dsimp only [Rule.machine]
    refine ⟨{ internal with aktion := .verbrauche answer }, hplans, ?_⟩
    exact Rule.consume owned₂ pending₂ ready₂ sameQuestion
  have impl₂ : ((d.unit locals).system.regel ()).impl c s₂ w [plan] u₂ := by
    dsimp only [Denotation.unit, Gabbro.Core.Ast.LowLevel.Device.unit]
    rw [ruleEq]
    dsimp only [Rule.machine]
    refine ⟨{ internal with aktion := .verbrauche answer }, hplans, ?_⟩
    exact Rule.consume owned₂ pending₂ ready₂ sameQuestion
  have regel₂ : (d.unit locals).system.ImplSchritt c s₂ w [plan] u₂ := ⟨(), kopf₂, impl₂⟩
  let spur₂ : SchrittSpur Nat UInt8 := ⟨[], []⟩
  let n₂ : State := u₂.verbrauche c
  have aus₂ : FuehrtSchrittAus (d.unit locals).einrichtung t c s₂ u₂ plan spur₂ n₂ := by
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · intro l hl
      rw [hplanF] at hl
      cases hl
    · refine ⟨[], u₂.verbrauche c, ?_, ?_, rfl⟩
      · rw [hplanF]
        exact FuehrtAus.verbrauche ready₂
      · rw [hplanF]
        dsimp only [spur₂, n₂]
        exact Speicherfolge.nil s₂.graph
  obtain ⟨spurEq₁, hfragen₁, hverlauf₁, hantworten₁, hverbraucht₁, hverworfen₁, hbuchung₁,
    hepoche₁, hgeliefert₁, hkerne₁, hstatus₁, hlokal₁, hpending₁, hinitial₁, hrechte₁,
    hleihen₁, hpersistenz₁⟩ :=
    geraete_consume_tick (target := target) aus₁ hplans hu owned pending ready sameQuestion
  obtain ⟨spurEq₂, hfragen₂, hverlauf₂, hantworten₂, hverbraucht₂, hverworfen₂, hbuchung₂,
    hepoche₂, hgeliefert₂, hkerne₂, hstatus₂, hlokal₂, hpending₂, hinitial₂, hrechte₂,
    hleihen₂, hpersistenz₂⟩ :=
    geraete_consume_tick (target := target) aus₂ hplans rfl owned₂ pending₂ ready₂ sameQuestion
  have hquell : QuellzustandGleich (d.unit locals) n₁ n₂ := by
    have impl₁Ideal : ((d.unit locals).system.regel ()).ideal c s₁ () [plan] u₁ := by
      dsimp only [Denotation.unit, Gabbro.Core.Ast.LowLevel.Device.unit]
      rw [ruleEq]
      dsimp only [Rule.machine]
      exact ⟨plan', hplans', rule₁⟩
    have hform₁ : FormSchritt (d.unit locals) () c s₁ () plan u₁ := ⟨kopf₁, impl₁Ideal⟩
    have hform₂ : FormSchritt (d.unit locals) () c s₂ () plan u₂ := ⟨kopf₂, impl₂Ideal⟩
    have hq := (geraeteSchrittNI locals d c s₁ s₂ () plan plan u₁ u₂ quell hform₁ hform₂).1
    have n1lokal : n₁.lokal = u₁.lokal := by rw [hlokal₁, hu]; rfl
    have n2lokal : n₂.lokal = u₂.lokal := by rw [hlokal₂]; rfl
    have n1status : n₁.status = u₁.status := by rw [hstatus₁, hu]; rfl
    have n2status : n₂.status = u₂.status := by rw [hstatus₂]; rfl
    have n1initial : n₁.initial = u₁.initial := by rw [hinitial₁, hu]; rfl
    have n2initial : n₂.initial = u₂.initial := by rw [hinitial₂]; rfl
    have n1rechte : n₁.rechte = u₁.rechte := by rw [hrechte₁, hu]; rfl
    have n2rechte : n₂.rechte = u₂.rechte := by rw [hrechte₂]; rfl
    have n1leihen : n₁.leihen = u₁.leihen := by rw [hleihen₁, hu]; rfl
    have n2leihen : n₂.leihen = u₂.leihen := by rw [hleihen₂]; rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [n1lokal, n2lokal] using hq.1
    · simpa only [n1status, n2status] using hq.2.1
    · simpa only [n1initial, n2initial] using hq.2.2.1
    · simpa only [n1rechte, n2rechte] using hq.2.2.2.1
    · simpa only [n1leihen, n2leihen] using hq.2.2.2.2.1
    · intro c'
      unfold AntwortSicht
      simp only [Zustand.naechsteAntwort, Zustand.angekommen, hantworten₁, hantworten₂,
        hverbraucht₁, hverbraucht₂, hverworfen₁, hverworfen₂, hantworten, hverbraucht,
        hverworfen, Function.update_self]
  refine ⟨spur₂, u₂, n₂, regel₂, aus₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hquell⟩
  · rw [spurEq₁, spurEq₂]
  · exact ⟨by rw [hfragen₁, hfragen₂, hfragen], by rw [hverlauf₁, hverlauf₂, hverlauf],
      by rw [hantworten₁, hantworten₂, hantworten],
      by rw [hverbraucht₁, hverbraucht₂, hverbraucht],
      by rw [hverworfen₁, hverworfen₂, hverworfen]⟩
  · rw [hbuchung₁, hbuchung₂, hbuch]
  · rw [hepoche₁, hepoche₂, hepoche]
  · rw [hgeliefert₁, hgeliefert₂, hgeliefert]
  · rw [hkerne₁, hkerne₂, hkerne]
  · rw [hstatus₁, hstatus₂, hstatus]

/-- A reserved interrupt excludes every delivery at that cut: the catalogue row is only
    served when no interrupt was selected. -/
theorem geraete_interrupt_schliesst_antwort_aus
    {k : Katalog.Katalog} {h : Umgebung} {run : HwLauf} {t : Nat} {a : AntwortEreignis}
    {kern id irq}
    (gueltig : AngebotGueltig k h (run.angebot t) (run.interruptUrsprung t))
    (wahl : (run.angebot t).interruptAuswahl = some (kern, id, irq))
    {e : Endpunkt} (delivery : (run.angebot t).delivery e = true) : False := by
  have hres := AngebotGueltig.interrupt_reserviert gueltig wahl
  exact Bool.false_ne_true ((hres.2.2 e).symm.trans delivery)

/-- A reserved interrupt leaves no core opportunity, so no context step can be ready. -/
theorem geraete_interrupt_schliesst_kontext_aus
    {k : Katalog.Katalog} {h : Umgebung} {run : HwLauf} {t : Nat} {c : Kontext}
    {kern id irq}
    (gueltig : AngebotGueltig k h (run.angebot t) (run.interruptUrsprung t))
    (wahl : (run.angebot t).interruptAuswahl = some (kern, id, irq))
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    {s : Zustand L Ort Wert Raum Lok Grund}
    (bereit : KannSchreiten run t c s) : False := by
  have hres := AngebotGueltig.interrupt_reserviert gueltig wahl
  obtain ⟨core, geleg, _, _⟩ := bereit
  change (run.angebot t).core = some core at geleg
  rw [hres.2.1] at geleg
  cases geleg

/-- At a state with the single-run device invariant, at most one answer can be offered at a
    cut: an offered answer matches the unique unmatched question, and the policy fixes its reply. -/
theorem geraete_antwort_eindeutig {k : Katalog} {binding : Binding k}
    {s : State} {kat : Katalog.Katalog} {run : HwLauf} {t : Nat}
    {a a' : AntwortEreignis}
    (inv : GeraeteInvariantAussage binding s)
    (offered : s.AntwortAngeboten kat run t a)
    (offered' : s.AntwortAngeboten kat run t a') : a = a' := by
  obtain ⟨hothers, hqctx, hactx, hfwd, hrange, hpre, hpost⟩ := inv
  obtain ⟨hcut, herlaubt, henthaelt, hfrage, hfrisch⟩ := offered
  obtain ⟨hcut', herlaubt', henthaelt', hfrage', hfrisch'⟩ := offered'
  obtain ⟨q0, hq0mem, hq0cut, hzu0⟩ := hfrage
  obtain ⟨q1, hq1mem, hq1cut, hzu1⟩ := hfrage'
  have hwiderlege (halle : ∀ q ∈ s.fragen, s.epoche ≤ q.cut → ∃ e ∈ s.antworten, e.zu q) : False := by
    obtain ⟨e, hemem, hzue⟩ := halle q0 hq0mem hq0cut
    exact hfrisch e hemem (hzue.2.2.1.symm.trans hzu0.2.2.1)
  by_cases hB : s.buchung.geraet = (startBuchung binding.object binding.handle).geraet
  · obtain ⟨hverw, hepoche, hidle, hbusy⟩ := hpre hB
    by_cases hp : (s.lokal entryContext).pending = none
    · exact (hwiderlege (hidle hp).2.2).elim
    · cases hbusy hp with
      | inl hbb => exact (hwiderlege hbb.2.2).elim
      | inr hub =>
        obtain ⟨hnm, hverb, hex⟩ := hub
        have htake : s.fragen.take (s.antworten.length + 1) = s.fragen := by
          rw [← hnm]
          exact List.take_length
        have hfa := geraete_antwort_erklaert_letzte_frage hnm hrange hfwd hq0mem hzu0 hfrisch
        have hfa' := geraete_antwort_erklaert_letzte_frage hnm hrange hfwd hq1mem hzu1 hfrisch'
        rw [htake] at hfa hfa'
        have hn : s.antworten.length < s.fragen.length := by rw [hnm]; omega
        have hzua := hfa.get (i := s.antworten.length) (by simp only [List.length_append, List.length_singleton]; omega) (by rw [hnm]; omega)
        have hzua' := hfa'.get (i := s.antworten.length) (by simp only [List.length_append, List.length_singleton]; omega) (by rw [hnm]; omega)
        have hgeta : (s.antworten ++ [a]).get ⟨s.antworten.length, by simp only [List.length_append, List.length_singleton]; omega⟩ = a := by
          have h₂ : s.antworten.length < (s.antworten ++ [a]).length := by
            simp only [List.length_append, List.length_singleton]
            omega
          have hres := List.getElem_append_right (as := s.antworten) (bs := [a])
            (i := s.antworten.length) (le_refl _) (h₂ := h₂)
          simpa only [Nat.sub_self, List.getElem_cons_zero] using hres
        have hgeta' : (s.antworten ++ [a']).get ⟨s.antworten.length, by simp only [List.length_append, List.length_singleton]; omega⟩ = a' := by
          have h₂ : s.antworten.length < (s.antworten ++ [a']).length := by
            simp only [List.length_append, List.length_singleton]
            omega
          have hres := List.getElem_append_right (as := s.antworten) (bs := [a'])
            (i := s.antworten.length) (le_refl _) (h₂ := h₂)
          simpa only [Nat.sub_self, List.getElem_cons_zero] using hres
        rw [hgeta] at hzua
        rw [hgeta'] at hzua'
        have hqeq : s.fragen.get ⟨s.antworten.length, by rw [hnm]; omega⟩ = s.fragen.get ⟨s.antworten.length, by rw [hnm]; omega⟩ := rfl
        have hinst : a.questionInstance = a'.questionInstance :=
          hzua.2.2.1.symm.trans hzua'.2.2.1
        have hctx : a.context = a'.context := hzua.2.1.symm.trans hzua'.2.1
        have hquest : a.question = a'.question := hzua.2.2.2.symm.trans hzua'.2.2.2
        have hreply : a.reply = a'.reply := by
          have hpol := herlaubt.2
          have hpol' := herlaubt'.2
          rw [hcut] at hpol
          rw [hcut'] at hpol'
          rw [hquest] at hpol
          exact Entscheidung.antwort.inj (hpol.symm.trans hpol')
        have hcutEq : a.cut = a'.cut := hcut.trans hcut'.symm
        cases a with
        | mk ac actx ai aq ar =>
          cases a' with
          | mk ac' actx' ai' aq' ar' =>
            simp only at hcutEq hctx hinst hquest hreply
            subst ac'
            subst actx'
            subst ai'
            subst aq'
            subst ar'
            rfl
  · obtain ⟨hbuch, hpending, hcutalt⟩ := hpost hB
    have hqalt := hcutalt q0 hq0mem
    omega

/-- Invert a device rule to its issue or consume data without fixing the post-state. -/
theorem geraete_rule_faelle {k : Katalog} {binding : Binding k} {access : RegisterAccess}
    {required : GeraetePhase} {target : Option GeraetePhase} {c : Kontext} {s u : State}
    {plan : Plan} (rule : Rule binding access required target c s plan u) :
    (∃ owned : Befugt binding required access s c, ∃ idle : (s.lokal c).pending = none,
      u = setFrame s c { s.lokal c with pending := some (binding.question access) }) ∨
      (∃ owned : Befugt binding required access s c, (s.lokal c).pending = some (binding.question access) ∧
        ∃ answer, s.naechsteAntwort c = some answer ∧ answer.question = binding.question access ∧
          u = setFrame s c (geraete_consume_rahmen s c binding access answer target)) := by
  cases rule with
  | issue owned idle => exact Or.inl ⟨owned, idle, rfl⟩
  | @consume owned answer pending ready sameQuestion =>
      exact Or.inr ⟨owned, pending, answer, ready, sameQuestion, rfl⟩

/-- The rule's binding is the denotation's declared binding. -/
theorem geraete_rule_binding (locals : Umgebung scope) (d : Denotation k scope) :
    ∃ binding access required target,
      d.rule locals = Rule.machine binding access required target ∧ binding = d.binding := by
  cases d with
  | read dest b off => exact ⟨b, .read off, .ready, none, rfl, rfl⟩
  | fallibleRead dest b off promise handler =>
    exact ⟨b, .fallibleRead off promise, .ready, none, rfl, rfl⟩
  | write b off value =>
    exact ⟨b, .write off (value.wert locals).wert.toNat, .ready, none, rfl, rfl⟩
  | transition decl =>
    exact ⟨decl.binding, .write decl.row.offset decl.data, decl.changes.prior,
      some decl.changes.after, rfl, rfl⟩

end Gabbro.Core.Beobachtung
