module

public import Core.Beobachtung.Spur
public import Core.Beobachtung.Fluss.Quellregel

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine

variable {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}

/-- The independent premises for two admitted runs to be compared. -/
structure Vergleich (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (h₁ h₂ : Umgebung) (ρ₁ ρ₂ : Lauf E) : Prop where
  links : Laeufe E h₁ ρ₁
  rechts : Laeufe E h₂ ρ₂
  umgebung : GleicheNiedrigeUmgebung E h₁ h₂
  start : NiedrigGleich E ρ₁.start ρ₂.start
  politik : GleichePolitik E ρ₁ ρ₂

theorem Vergleich.symm {h₁ h₂ ρ₁ ρ₂} (h : Vergleich E h₁ h₂ ρ₁ ρ₂) : Vergleich E h₂ h₁ ρ₂ ρ₁ :=
  ⟨h.rechts, h.links, Eq.symm h.umgebung, Eq.symm h.start, Eq.symm h.politik⟩

/-- One finite public prefix is matched by the other run, possibly at a different hardware cut. -/
def PraefixAbgedeckt (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form) (ρ₁ ρ₂ : Lauf E)
    (predictor : Praediktor) (t : Nat) : Prop :=
  let links := NiedrigeBeob E ρ₁ predictor t
  ∃ u, List.Forall₂ (EreignisAequiv E.fluss.freigabe) links
    ((NiedrigeBeob E ρ₂ predictor u).take links.length)

/-- Coupling of two compared runs: the flexible prefix cover as before, plus the
    source-state equality and the machine-field equalities (epoch, delivered, cores,
    status) at the SAME cut on both sides, plus prefix-length equality.

    The state part is deliberately same-cut (t, t), not (t, u): with the flexible
    cut pair the silent-step obligation would be unprovable — a right run that
    pauses at u while the left takes a local-state-changing silent step breaks
    `QuellzustandGleich` of the stopped states, and no other right cut repairs the
    positional prefix. Same-cut offers coincide per index (`GleichePolitik`), so
    both sides lockstep through step kinds and the state part is maintainable. -/
def Kopplung (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form) (ρ₁ ρ₂ : Lauf E)
    (predictor : Praediktor) (t u : Nat) : Prop :=
  List.Forall₂ (EreignisAequiv E.fluss.freigabe) (NiedrigeBeob E ρ₁ predictor t)
    ((NiedrigeBeob E ρ₂ predictor u).take (NiedrigeBeob E ρ₁ predictor t).length)
  ∧ (∀ v w, ρ₁.zeit.zustand t = some v → ρ₂.zeit.zustand t = some w →
      QuellzustandGleich E v w ∧ v.epoche = w.epoche ∧ v.geliefert = w.geliefert ∧
      v.kerne = w.kerne ∧ v.status = w.status)
  ∧ (NiedrigeBeob E ρ₁ predictor t).length = (NiedrigeBeob E ρ₂ predictor u).length

/-- The coupling implies the old prefix cover (witness: the coupling cut). -/
theorem kopplung_prefix {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    {ρ₁ ρ₂ : Lauf E} {predictor : Praediktor} {t u : Nat}
    (h : Kopplung E ρ₁ ρ₂ predictor t u) : PraefixAbgedeckt E ρ₁ ρ₂ predictor t := by
  unfold PraefixAbgedeckt
  exact ⟨u, h.1⟩

/-- Same-cut length equality follows from one-sided coupling directly: it is
    maintained as part of the invariant, so the crash case no longer needs a
    separate global length hypothesis. -/
theorem kopplung_laenge {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    {ρ₁ ρ₂ : Lauf E} {predictor : Praediktor} {t : Nat}
    (h : Kopplung E ρ₁ ρ₂ predictor t t) :
    (NiedrigeBeob E ρ₁ predictor t).length = (NiedrigeBeob E ρ₂ predictor t).length :=
  h.2.2

def RegelNIPflicht (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form) (f : Form) : Prop :=
  ∀ {h₁ h₂ ρ₁ ρ₂}, Vergleich E h₁ h₂ ρ₁ ρ₂ → ∀ predictor t c w spur vor,
    ρ₁.zeit.zustand t = some vor → E.system.kopf vor c = some f →
    ρ₁.zeit.spur t = some (.kontext c w, spur) →
    Kopplung E ρ₁ ρ₂ predictor t t → Kopplung E ρ₁ ρ₂ predictor (t + 1) (t + 1)

def ProtokollWahl : SchrittWahl Wahl → Prop
  | .kontext _ _ => False
  | .antwort _ | .interrupt _ | .absturz => True

/-- The registry contributes one obligation per source form. The loader and non-form
    protocol transitions have shared obligations; an idle tick keeps the coupling
    through a dedicated pause obligation (the right run provably idles along). -/
structure NIPflichten (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form) : Prop where
  start : ∀ {h₁ h₂ ρ₁ ρ₂}, Vergleich E h₁ h₂ ρ₁ ρ₂ →
    ∀ predictor, Kopplung E ρ₁ ρ₂ predictor 0 0
  regel : ∀ f, RegelNIPflicht E f
  protokoll : ∀ {h₁ h₂ ρ₁ ρ₂}, Vergleich E h₁ h₂ ρ₁ ρ₂ → ∀ predictor t w spur,
    ρ₁.zeit.spur t = some (w, spur) → ProtokollWahl w →
    Kopplung E ρ₁ ρ₂ predictor t t → Kopplung E ρ₁ ρ₂ predictor (t + 1) (t + 1)
  pause : ∀ {h₁ h₂ ρ₁ ρ₂}, Vergleich E h₁ h₂ ρ₁ ρ₂ → ∀ predictor t,
    ρ₁.zeit.spur t = none →
    Kopplung E ρ₁ ρ₂ predictor t t → Kopplung E ρ₁ ρ₂ predictor (t + 1) (t + 1)

/-- A paused cut appends no observation; shared by the per-unit pause proofs. -/
theorem beob_pause (ρ : Lauf E) (predictor : Praediktor) (t : Nat) (idle : ρ.zeit.spur t = none) :
    NiedrigeBeob E ρ predictor (t + 1) = NiedrigeBeob E ρ predictor t := by
  change NiedrigeBeob E ρ predictor t ++ schrittBeob ρ predictor t = NiedrigeBeob E ρ predictor t
  simp only [schrittBeob, idle, List.append_nil]

private theorem anfangUndSchritte (pflicht : NIPflichten E) {h₁ h₂ ρ₁ ρ₂}
    (vergleich : Vergleich E h₁ h₂ ρ₁ ρ₂) (predictor : Praediktor) (t : Nat) :
    Kopplung E ρ₁ ρ₂ predictor t t := by
  induction t with
  | zero => exact pflicht.start vergleich predictor
  | succ t gekoppelt =>
    cases tick : ρ₁.zeit.spur t with
    | none =>
      exact pflicht.pause vergleich predictor t tick gekoppelt
    | some label =>
      rcases label with ⟨w, spur⟩
      cases w with
      | antwort _ | interrupt _ | absturz =>
        exact pflicht.protokoll vergleich predictor t _ spur tick trivial gekoppelt
      | kontext c w =>
        have recorded := ρ₁.zeit.takt t
        rw [tick] at recorded
        generalize vorEq : ρ₁.zeit.zustand t = vor at recorded
        generalize ρ₁.zeit.zustand (t + 1) = nach at recorded
        cases recorded with
        | wartet impossible _ _ => cases impossible
        | schritt mark transition =>
          cases mark
          cases transition with
          | schritt step =>
            cases step with
            | kontext _ _ regel _ =>
              obtain ⟨f, kopf, _⟩ := regel
              exact pflicht.regel f vergleich predictor t c w spur _ vorEq kopf tick gekoppelt

private theorem EreignisAequiv.umkehren {a b : NiedrigesEreignis Ort Wert Grund Form}
    {d : Nat → Option (Freigabe Wert)} (h : EreignisAequiv d a b) : EreignisAequiv d b a := by
  cases h with
  | gleich _ => exact .gleich _
  | freigabe c id a b g d h => exact .freigabe c id b a g d h.symm

private theorem relation_umkehren {a b : List (NiedrigesEreignis Ort Wert Grund Form)}
    {d : Nat → Option (Freigabe Wert)} (h : List.Forall₂ (EreignisAequiv d) a b) :
    List.Forall₂ (EreignisAequiv d) b a := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons h.umkehren ih

theorem ni_spur_aus_pflichten (pflicht : NIPflichten E) {h₁ h₂ ρ₁ ρ₂}
    (vergleich : Vergleich E h₁ h₂ ρ₁ ρ₂) :
    NiedrigAequiv E (NiedrigeBeob E ρ₁) (NiedrigeBeob E ρ₂) := by
  refine fun p => ⟨fun t => kopplung_prefix (anfangUndSchritte pflicht vergleich p t), fun u => ?_⟩
  obtain ⟨t, h⟩ := kopplung_prefix (anfangUndSchritte pflicht vergleich.symm p u)
  exact ⟨t, relation_umkehren h⟩

/-- Both NI conclusions over an admitted comparison start. Existence is discharged by the
    shared run constructor. Public-trace preservation reduces to the local obligations. -/
theorem ni_aus_pflichten (pflicht : NIPflichten E) {h₁ h₂ ρ₁ s₂}
    (run : Laeufe E h₁ ρ₁) (hardware : Hardware E.katalog h₂)
    (umgebung : GleicheNiedrigeUmgebung E h₁ h₂) (zul : E.ZulStart h₂ s₂)
    (start : NiedrigGleich E ρ₁.start s₂) :
    (∃ ρ₂, Laeufe E h₂ ρ₂ ∧ ρ₂.start = s₂ ∧ GleichePolitik E ρ₁ ρ₂) ∧
    ∀ ρ₂, Laeufe E h₂ ρ₂ → ρ₂.start = s₂ → GleichePolitik E ρ₁ ρ₂ →
      NiedrigAequiv E (NiedrigeBeob E ρ₁) (NiedrigeBeob E ρ₂) :=
  ⟨vergleichslauf E run hardware umgebung zul, fun ρ₂ run₂ start₂ politik =>
    ni_spur_aus_pflichten pflicht ⟨run, run₂, umgebung, start₂.symm ▸ start, politik⟩⟩

end Gabbro.Core.Beobachtung
