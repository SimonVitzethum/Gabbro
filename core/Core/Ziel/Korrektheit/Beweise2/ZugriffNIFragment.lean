/-
  File:      core/Core/Ziel/Korrektheit/Beweise2/ZugriffNIFragment.lean
  Subject:   THE COUPLING MACHINERY OVER `FragmentNIBeweise` FOR THE TWO CLASSES. `ZugriffNIFragmentAussage`
             is the noninterference leg for a fragment whose code is frame-only or an access instruction.
             The accepted-fragment theorem of `Beobachtung` needs `rein : ∀ b ∈ p.code, b.Privat`, which a
             fragment `MitZugriff` does not have. Here the family dispatch is rerun with `.zugriff` filled by
             the pinned `ZugriffNIAussage`, and the pause obligation is carried for the two classes: when the
             right run takes a context step with an access head, the left run has a matching step from the
             liveness of the memory model (`ZugriffSchrittExistiertAussage`) and `zugriffKomponierbar`, so the
             same `KeinSchritt` contradiction applies. No pinned statement is changed.
-/
module

public import Core.Beobachtung.Fluss.Beweise.Gesamt
public import Core.Beobachtung.Fluss.Beweise.ZugriffSchritt
public import Core.Ast.Semantik.Runtime.Atom.Beweise.Komponierbar
public import Core.Ziel.Korrektheit.Zugriff

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core
open Gabbro.Core.Beobachtung
open Katalog Maschine

/-- Every state along an admitted fragment run has a consistent complete graph. Reproduced from
    `Beobachtung` (where it is private) for the two-class pause proof. -/
private theorem fragment_speicher_gut {p : Ast.Semantik.Fragment} {plattform : Plattform}
    {h : Umgebung} {ρ : Lauf (p.einheit plattform)}
    (lauf : Laeufe (p.einheit plattform) h ρ) (t : Nat) :
    ∃ z, ρ.zeit.zustand t = some z ∧ z.SpeicherGut := by
  induction t with
  | zero =>
    refine ⟨(I.start (p.einheit plattform) ρ.start).2, ?_, ?_⟩
    rw [lauf.2.2.2]
    exact fragment_geladen p plattform lauf.1 lauf.2.2.1
    change Speicher.Zustand.leer.graph.Konsistent ∧ Speicher.Zustand.leer.graph.Vollstaendig
    exact ⟨Speicher.Zustand.leer_konsistent, Speicher.Zustand.leer_vollstaendig⟩
  | succ t ih =>
    obtain ⟨z, atZ, gut⟩ := ih
    cases tick : ρ.zeit.takt t with
    | schritt label step =>
      rw [atZ] at step
      cases nach : ρ.zeit.zustand (t + 1) with
      | none =>
        rw [nach] at step
        cases step
      | some next =>
        rw [nach] at step
        cases step with
        | schritt impl => exact ⟨next, rfl, impl_speicher_gut _ _ impl gut⟩
    | wartet label gleich _ =>
      refine ⟨z, ?_, gut⟩
      exact gleich.trans atZ

/-- A paused cut keeps the coupling for a fragment of the two classes. The proof is the frame-only
    pause argument with one extra case: when the right run takes a context step whose head is an
    access instruction, the left run is given the very same step by the liveness of the memory model
    and `zugriffKomponierbar`, so `KeinSchritt` is contradicted there too. -/
theorem pause_klassenrein (existiert : ZugriffSchrittExistiertAussage)
    (p : Ast.Semantik.Fragment) (plattform : Plattform) (klassenrein : p.KlassenRein)
    {h₁ h₂ : Umgebung} {ρ₁ ρ₂ : Lauf (p.einheit plattform)}
    (vergleich : Vergleich (p.einheit plattform) h₁ h₂ ρ₁ ρ₂) (predictor : Praediktor) (t : Nat)
    (idle₁ : ρ₁.zeit.spur t = none)
    (kopplung : Kopplung (p.einheit plattform) ρ₁ ρ₂ predictor t t) :
    Kopplung (p.einheit plattform) ρ₁ ρ₂ predictor (t + 1) (t + 1) := by
  classical
  let E := p.einheit plattform
  have warte₁ := ρ₁.zeit.wartet idle₁
  have keinSchritt₁ : KeinSchritt (Lauffolge E ρ₁.hw) t (ρ₁.zeit.zustand t) := warte₁.2
  have zustandGleich₁ : ρ₁.zeit.zustand (t + 1) = ρ₁.zeit.zustand t := warte₁.1
  obtain ⟨v₁, zustand₁⟩ := fragment_zustand_some vergleich.links t
  obtain ⟨v₂, zustand₂⟩ := fragment_zustand_some vergleich.rechts t
  obtain ⟨cov, st, len⟩ := kopplung
  obtain ⟨⟨lokGleich, _, initialGleich, rechteGleich, leihenGleich, antwortGleich⟩,
    epocheEq, geliefertEq, kerneEq, statusEq⟩ := st v₁ v₂ zustand₁ zustand₂
  have lokEqFun : v₁.lokal = v₂.lokal := by
    funext d
    have hpub : oeffentlich ((E.fluss.lokal d).etikett ⟨0, Nat.zero_lt_one⟩) = true := rfl
    exact lokGleich d ⟨0, Nat.zero_lt_one⟩ hpub
  have crashEq : (ρ₁.hw.angebot t).crash = (ρ₂.hw.angebot t).crash :=
    congrArg (fun pr => (pr.1 t).2.2.2.2.2.1) vergleich.politik
  have coreEq : (ρ₁.hw.angebot t).core = (ρ₂.hw.angebot t).core :=
    congrArg (fun pr => (pr.1 t).1) vergleich.politik
  have interruptEq : (ρ₁.hw.angebot t).interrupt = (ρ₂.hw.angebot t).interrupt :=
    congrArg (fun pr => (pr.1 t).2.1) vergleich.politik
  have signaleEq : (ρ₁.hw.angebot t).interrupts = (ρ₂.hw.angebot t).interrupts :=
    congrArg (fun pr => (pr.1 t).2.2.1) vergleich.politik
  have auswahlEq : (ρ₁.hw.angebot t).interruptAuswahl = (ρ₂.hw.angebot t).interruptAuswahl := by
    simp only [Gelegenheit.interruptAuswahl, signaleEq]
  have sysKopf : ∀ s d, E.system.kopf s d = Ast.Semantik.kopf p.code s d := fun _ _ => rfl
  obtain ⟨wGut, atWGut, gutWGut⟩ := fragment_speicher_gut vergleich.links t
  have zustandGut₁ : v₁.SpeicherGut := by
    rw [Option.some.inj (zustand₁.symm.trans atWGut)]
    exact gutWGut
  have takt₂ := ρ₂.zeit.takt t
  rw [zustand₂] at takt₂
  generalize nachEq₂ : ρ₂.zeit.zustand (t + 1) = nach₂ at takt₂
  cases takt₂ with
  | wartet label₂ gleich₂ _ =>
    have idle₂ : ρ₂.zeit.spur t = none := label₂
    have zustandGleich₂ : ρ₂.zeit.zustand (t + 1) = ρ₂.zeit.zustand t :=
      nachEq₂.trans (gleich₂.trans zustand₂.symm)
    refine ⟨?_, ?_, ?_⟩
    · rw [beob_pause ρ₁ predictor t idle₁, beob_pause ρ₂ predictor t idle₂]
      exact cov
    · intro a b ha hb
      apply st a b
      · rw [zustandGleich₁] at ha
        exact ha
      · rw [zustandGleich₂] at hb
        exact hb
    · rw [beob_pause ρ₁ predictor t idle₁, beob_pause ρ₂ predictor t idle₂]
      exact len
  | schritt label₂ step₂ =>
    have someEv : ∃ wahl spur', ρ₂.zeit.spur t = some (wahl, spur') := by
      cases hlab : ρ₂.zeit.spur t with
      | none =>
        rw [hlab] at label₂
        cases label₂
      | some ev =>
        refine ⟨ev.1, ev.2, ?_⟩
        cases ev
        rfl
    obtain ⟨wahl, spur', label'⟩ := someEv
    have evEq := Option.some.inj (label₂.symm.trans label')
    rw [evEq] at step₂
    cases step₂ with
    | schritt impl₂ =>
      cases wahl with
      | kontext c₂ w₂ =>
        cases impl₂ with
        | kontext keinAbsturz₂ bereit₂ regel₂ aus₂ =>
          obtain ⟨f₂, kopf₂, _⟩ := regel₂
          obtain ⟨k, geleg₂, kern₂, stat₂⟩ := bereit₂
          have kopf₁_gleich : E.system.kopf v₁ c₂ = E.system.kopf v₂ c₂ := by
            have h : Ast.Semantik.kopf p.code v₁ c₂ = Ast.Semantik.kopf p.code v₂ c₂ := by
              simp only [Ast.Semantik.kopf, lokEqFun.symm, statusEq.symm]
            rw [sysKopf, h, ← sysKopf]
          have crash₁ : (ρ₁.hw.angebot t).crash = false := by
            rw [crashEq]
            exact keinAbsturz₂
          have bereit₁ : KannSchreiten ρ₁.hw t c₂ v₁ := by
            refine ⟨k, ?_, ?_, ?_⟩
            · show (ρ₁.hw.angebot t).core = some k
              rw [coreEq]
              exact geleg₂
            · rw [kerneEq]
              exact kern₂
            · rw [statusEq]
              exact stat₂
          have stepData : ∃ (plan : Ast.Semantik.Plan) (u : Ast.Semantik.Zustand)
              (spur : SchrittSpur Ast.Semantik.Zelle Int) (s' : Ast.Semantik.Zustand),
              E.system.ImplSchritt c₂ v₁ w₂ [plan] u ∧
                FuehrtSchrittAus E.einrichtung t c₂ v₁ u plan spur s' := by
            by_cases hpriv : f₂.Privat
            · refine ⟨f₂.plan (v₁.lokal c₂) 0, f₂.nach c₂ v₁, ⟨[], []⟩,
                f₂.maschinennach c₂ v₁ (f₂.nach c₂ v₁), ?_, ?_⟩
              · exact ⟨f₂, by rw [kopf₁_gleich]; exact kopf₂,
                  (f₂.impl_privat hpriv c₂ v₁ w₂ _ _).2 ⟨rfl, rfl⟩⟩
              · exact f₂.vollzug _ t c₂ v₁ hpriv
            · rcases klassenrein f₂ (Ast.Semantik.kopf_mem (code := p.code) kopf₂) with hpriv' | ⟨z, hz⟩
              · exact (hpriv hpriv').elim
              · subst f₂
                have kopf₁ : E.system.kopf v₁ c₂ = some (Ast.Semantik.Befehl.zugriff z) := by
                  rw [kopf₁_gleich]
                  exact kopf₂
                obtain ⟨wu, plan, u, es, g, step, folge⟩ :=
                  existiert p plattform z v₁ c₂ kopf₁ zustandGut₁
                obtain ⟨spur₁, s', run₁⟩ :=
                  Ast.Semantik.zugriffKomponierbar p plattform z t v₁ c₂ wu plan u es g kopf₁ step folge
                refine ⟨plan, u, spur₁, s', ?_, run₁⟩
                exact ⟨Ast.Semantik.Befehl.zugriff z, kopf₁, step⟩
          obtain ⟨plan, u, spur₁, s', regel₁, aus₁⟩ := stepData
          have step₁ : ImplSchritt E.einrichtung E.system E.katalog ρ₁.hw t v₁
              (.kontext c₂ w₂, spur₁) s' :=
            .kontext crash₁ bereit₁ regel₁ aus₁
          exact (keinSchritt₁ (.kontext c₂ w₂, spur₁) (some s')
            (by rw [zustand₁]; exact Lauffolge.schritt step₁)).elim
      | antwort a =>
        exact (antwortNI p plattform h₂ ρ₂ vergleich.rechts t a spur' label').elim
      | interrupt irqId =>
        cases impl₂ with
        | interrupt keinAbsturz₂ enters₂ =>
          obtain ⟨k, irq, c₂, nmi, intOffer₂, pending₂, nimmt₂, ruht₂, _, _, _⟩ := enters₂
          have crash₁ : (ρ₁.hw.angebot t).crash = false := by
            rw [crashEq]
            exact keinAbsturz₂
          have intOffer₁ : (ρ₁.hw.angebot t).interrupt k = true := by
            rw [interruptEq]
            exact intOffer₂
          have pending₁ : UnterbrechungAusstehend v₁ ρ₁.hw t k irqId irq := by
            refine ⟨?_, pending₂.2.1, ?_, ?_, ?_⟩
            · rw [epocheEq]
              exact pending₂.1
            · have signaleEqId : (ρ₁.hw.angebot irqId.1).interrupts =
                  (ρ₂.hw.angebot irqId.1).interrupts :=
                 congrArg (fun pr => (pr.1 irqId.1).2.2.1) vergleich.politik
              rw [signaleEqId]
              exact pending₂.2.2.1
            · intro mem
              exact pending₂.2.2.2.1 (by rw [geliefertEq] at mem; exact mem)
            · exact auswahlEq.trans pending₂.2.2.2.2
          have nimmt₁ : NimmtUnterbrechung (v₁.kerne k) k (Nat.pair irqId.1 irqId.2) irq c₂ nmi := by
            rw [kerneEq]
            exact nimmt₂
          have ruht₁ : v₁.status c₂ = .ruht := by
            rw [statusEq]
            exact ruht₂
          let label : Speicher.Etikett Ast.Semantik.Zelle Int :=
            aussenEtikett E.einrichtung (.interrupt k irq .handler)
          have labelNicht : ¬ label.art.liest := by
            simp only [label, aussenEtikett, Speicher.Art.liest]
            intro h
            cases h
          obtain ⟨graph', stepGraph⟩ :=
            Speicher.Zustand.schritt_ohne_lesen (Z := v₁.graph) zustandGut₁.1 zustandGut₁.2
              .aussen label labelNicht
          have folge₁ : Speicherfolge v₁.initial .aussen v₁.graph [label]
              [(.aussen, label)] graph' :=
            .cons (.ohne (Or.inl (by simp only [label, aussenEtikett]))) stepGraph (.nil _)
          let spur₁ : SchrittSpur Ast.Semantik.Zelle Int := ⟨[(.aussen, label)], [.interrupt k irq .handler]⟩
          let nach₁ := { Zustandseintritt v₁ k irqId c₂ nmi with graph := graph' }
          have enters₁ : UnterbrechungsSchritt E.einrichtung ρ₁.hw t irqId v₁ spur₁ nach₁ := by
            refine ⟨k, irq, c₂, nmi, intOffer₁, pending₁, nimmt₁, ruht₁, ?_, ?_, rfl⟩
            · rfl
            · exact folge₁
          have step₁ : ImplSchritt E.einrichtung E.system E.katalog ρ₁.hw t v₁
              (.interrupt irqId, spur₁) nach₁ :=
            .interrupt crash₁ enters₁
          exact (keinSchritt₁ (.interrupt irqId, spur₁) (some nach₁)
            (by rw [zustand₁]; exact Lauffolge.schritt step₁)).elim
      | absturz =>
        cases impl₂ with
        | absturz crash₂ =>
          have offer₁ : AbsturzAngeboten E.katalog ρ₁.hw t :=
            ⟨crash₂.1.1, by rw [crashEq]; exact crash₂.1.2⟩
          have crashStep₁ : AbsturzSchritt E.einrichtung.persistenzRegion E.einrichtung.wiederanlauf
              E.katalog ρ₁.hw t v₁ absturzSpur (v₁.wiederanlauf E.einrichtung.wiederanlauf t (nachAbsturz v₁.persistenz)) :=
            absturz_schritt_erfuellbar _ _ offer₁ v₁
          have step₁ : ImplSchritt E.einrichtung E.system E.katalog ρ₁.hw t v₁
              (.absturz, absturzSpur) (v₁.wiederanlauf E.einrichtung.wiederanlauf t (nachAbsturz v₁.persistenz)) :=
            .absturz crashStep₁
          exact (keinSchritt₁ (.absturz, absturzSpur)
            (some (v₁.wiederanlauf E.einrichtung.wiederanlauf t (nachAbsturz v₁.persistenz)))
            (by rw [zustand₁]; exact Lauffolge.schritt step₁)).elim

/-- **The noninterference leg for a fragment of the two classes**, from the pinned
    `ZugriffNIFragmentAussage`'s family packet `ZugriffNIAussage` and the liveness of the memory model.
    This is `akzeptiertes_fragment_ni` with the `rein` premise replaced by `KlassenRein` and the
    `zugriff` family filled by the pinned access-family statement. -/
theorem zugriffNIFragmentAusFamilie (zugriff : ZugriffNIAussage)
    (existiert : ZugriffSchrittExistiertAussage) : ZugriffNIFragmentAussage := by
  intro p plattform mitZugriff akzeptiert
  have klassenrein : p.KlassenRein := mitZugriff.1
  apply ni_akzeptierter_einheit (p.einheit plattform) akzeptiert (fragment_start_ni p plattform)
  · intro f quelle
    cases familie : f.familie with
    | skalar => exact skalarNI p plattform f familie quelle
    | kontrollfluss => exact kontrollflussNI p plattform f familie quelle
    | aufrufSchleife => exact aufrufSchleifeNI p plattform f familie quelle
    | aggregat => exact aggregatNI p plattform f familie quelle
    | text => exact textNI p plattform f familie quelle
    | variante => exact varianteNI p plattform f familie quelle
    | zugriff => exact zugriff p plattform f familie quelle
  · intro h₁ h₂ ρ₁ ρ₂ v predictor t w spur tick protokoll kopplung
    cases w with
    | kontext _ _ => exact False.elim protokoll
    | antwort a => exact (antwortNI p plattform h₁ ρ₁ v.links t a spur tick).elim
    | interrupt _ => exact interruptNI p plattform v predictor t _ spur tick trivial kopplung
    | absturz => exact absturzNI p plattform v predictor t _ spur tick trivial kopplung
  · intro h₁ h₂ ρ₁ ρ₂ v predictor t idle kopplung
    exact pause_klassenrein existiert p plattform klassenrein v predictor t idle kopplung

end Gabbro.Core.Ziel.Korrektheit
