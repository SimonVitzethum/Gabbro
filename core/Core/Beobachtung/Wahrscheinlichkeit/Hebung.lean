/-
  File:      Core/Beobachtung/Wahrscheinlichkeit/Hebung.lean
  Subject:   The causal, measure-preserving lift: bands, schedulers, cylinders (M9P, B11(a)).

  The machine G/GX is lifted to a Markov decision process: random answers are drawn
  from the declared laws, while the scheduler and every other oracle answer stay
  adversarial - statements hold for every scheduler and every non-random answer.

  Design (form-independent, no Ast change):
  - `Band` is the raw randomness: source id × draw index → natural number. The
    outcome of draw `k` for source `Q` is `band Q.id k % Q.anz`.
  - Causality holds BY TYPING: `Scheduler.waehle t` sees only `Sicht t`, the draws
    strictly below `t`. No foresight is expressible (`scheduler_kausal`,
    `sichtGleich`, both proved).
  - `ZylinderGewicht` is the finite-cylinder weight: the product of the declared
    laws. It mentions no scheduler and no policy, so measure preservation is
    structural (`massEindeutig`, proved): any lift extending these weights preserves
    the declared laws under every scheduler and every non-random policy.
  - `Hebebuendel` packages what the lift proof (pinned `hebeAussage`) must deliver:
    the band measure, the replay into admitted runs, and the characteristic
    properties. Every per-form statement quantifies over bundles hypothetically, so
    all obligations stay independent for parallel proof.

  The existence proof is the model-side Ionescu-Tulcea construction: given a
  scheduler, replay the machine deterministically, consuming band draws in trace
  order. That construction is causal by construction, which is why `KausalReplay`
  is a bundle field rather than a separate theorem.
-/
module

public import Core.Beobachtung.Wahrscheinlichkeit.Quelle
public import Core.Beobachtung.Schranken
public import Core.Maschine.Schritte
public import Core.Katalog.Lauf

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog

/-- The raw randomness: source id × draw index → natural number. The outcome of a
    draw is the value modulo the source's outcome count (`Ziehung`). -/
abbrev Band : Type := Nat → Nat → Nat

/-- What a scheduler may see at tick `t`: the draws strictly below `t`, for every
    source. Causality by typing: the future is not in the domain. -/
abbrev Sicht (t : Nat) : Type := (id k : Nat) → k < t → Nat

/-- The prefix of a band visible at tick `t`. -/
def Band.sicht (band : Band) (t : Nat) : Sicht t :=
  fun _id k _ => band _id k

/-- Pointwise agreement below `t` gives equal sights. -/
theorem sichtGleich (b₁ b₂ : Band) (t : Nat)
    (h : ∀ id k : Nat, k < t → b₁ id k = b₂ id k) : b₁.sicht t = b₂.sicht t :=
  funext fun id => funext fun k => funext fun hlt => h id k hlt

/-- An adversarial scheduler: at each tick, the acting context, from the random past
    only. Program schedulers are code and stay inside the runs; this is the
    hardware-level adversarial choice of Markov decision processes. -/
structure Scheduler where
  waehle : (t : Nat) → Sicht t → Nat

/-- The scheduler's choice depends only on what it saw: equal sights give equal
    choices. No foresight, by congruence. -/
theorem scheduler_kausal (S : Scheduler) (t : Nat) (s₁ s₂ : Sicht t) (h : s₁ = s₂) :
    S.waehle t s₁ = S.waehle t s₂ :=
  congrArg (S.waehle t) h

/-- The outcome of draw `k` for source `Q` on this band. -/
def Ziehung (Q : Zufallsquelle) (band : Band) (k : Nat) : Fin Q.anz :=
  ⟨band Q.id k % Q.anz, Nat.mod_lt _ Q.pos⟩

/-- A finite cylinder: finitely many draw positions with prescribed outcomes.
    Cylinders determine the band measure; every run event the forms speak about is
    a countable combination of cylinders. -/
structure Zylinder (Q : Zufallsquelle) where
  pfad : List (Nat × Fin Q.anz)

/-- The cylinder weight: the product of the declared laws along the path. It mentions
    no scheduler and no policy: the declared laws are preserved structurally. -/
noncomputable def ZylinderGewicht (Q : Zufallsquelle) (Z : Zylinder Q) : ENNReal :=
  (Z.pfad.map fun p => Q.gesetz p.2).prod

/-- A singleton cylinder weighs exactly the law at that outcome. -/
theorem zylinderSingleton (Q : Zufallsquelle) (k : Nat) (a : Fin Q.anz) :
    ZylinderGewicht Q ⟨[(k, a)]⟩ = Q.gesetz a := by
  simp only [ZylinderGewicht, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]

/-- The set of bands extending a cylinder. -/
def zylinderMenge (Q : Zufallsquelle) (Z : Zylinder Q) : Set Band :=
  {band | ∀ p ∈ Z.pfad, band Q.id p.1 % Q.anz = p.2.val}

/-- An adversary is any probabilistic oracle strategy: a Lean function over the
    interaction history and the band, of unknown origin and code (B11). It answers
    the non-random questions; random questions are answered from the band. -/
abbrev Gegner : Type := Band → AussenVerlauf → Frage → Antwort

/-- The random-draw answers consumed in the trace prefix below `t`, in trace order.
    The `random` source form does not exist yet, so the filter is the boolean
    `istZufallsfrage` test, not a constructor match. -/
def praefixAntworten (B : Zufallsbindung)
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    {E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    (ρ : Maschine.Lauf E) (t : Nat) : List AntwortEreignis :=
  (List.finRange t).flatMap fun i => match ρ.zeit.spur i with
    | none => []
    | some (_, spur) =>
      (spur : Maschine.SchrittSpur Ort Wert).aussen.filterMap fun e => match e with
        | .antwort a => if istZufallsfrage B a.question then some a else none
        | _ => none

/-- A replay is causal: bands agreeing below `t` give runs agreeing below `t`.
    No foresight, stated over the observable cuts. -/
def KausalReplay
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    {E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    (replay : Band → Maschine.Lauf E) : Prop :=
  ∀ b₁ b₂ : Band, ∀ t : Nat, (∀ id k : Nat, k < t → b₁ id k = b₂ id k) →
    ∀ t' : Nat, t' < t →
      (replay b₁).zeit.zustand t' = (replay b₂).zeit.zustand t' ∧
        (replay b₁).zeit.spur t' = (replay b₂).zeit.spur t'

/-- The lift bundle: the band measure with the replay into admitted runs, and the
    characteristic properties every per-form statement assumes. The measure agrees
    with the cylinder weights (`massErhalt`); the replay lands in admitted runs,
    is causal, follows the scheduler unless its choice is stuck, and answers every
    random question from the band. -/
structure Hebebuendel (B : Zufallsbindung) (S : Scheduler)
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (h : Umgebung) where
  mu : MeasureTheory.Measure Band
  replay : Band → Maschine.Lauf E
  istWMass : MeasureTheory.IsProbabilityMeasure mu
  massErhalt : ∀ Z : Zylinder B.quelle,
    mu {band | ∀ p ∈ Z.pfad, band B.quelle.id p.1 % B.quelle.anz = p.2.val} =
      ZylinderGewicht B.quelle Z
  replayZulaessig : ∀ band, Maschine.Laeufe E h (replay band)
  replayKausal : KausalReplay replay
  replayFolgtScheduler : ∀ (band : Band) (t : Nat) (c : Maschine.Kontext) (w : Wahl)
      (spur : Maschine.SchrittSpur Ort Wert),
      (replay band).zeit.spur t = some (Maschine.SchrittWahl.kontext c w, spur) →
        S.waehle t (band.sicht t) = c.nummer ∨
          Maschine.KeinSchritt (Maschine.Lauffolge E (replay band).hw) t
            ((replay band).zeit.zustand t)
  replayZiehungen : ∀ (band : Band) (t : Nat) (a : AntwortEreignis),
      a ∈ praefixAntworten B (replay band) t →
        ∃ k : Nat, a.reply = ZiehungsAntwort a.reply.origin (Ziehung B.quelle band k).val

/-- Measure preservation, proved: any two bundles for the same source agree on every
    cylinder, since both extend the same weights. The declared laws survive the lift
    independently of scheduler and policy. -/
theorem massEindeutig (B : Zufallsbindung) (S : Scheduler)
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (h : Umgebung) (hb₁ hb₂ : Hebebuendel B S E h) (Z : Zylinder B.quelle) :
    hb₁.mu {band | ∀ p ∈ Z.pfad, band B.quelle.id p.1 % B.quelle.anz = p.2.val} =
    hb₂.mu {band | ∀ p ∈ Z.pfad, band B.quelle.id p.1 % B.quelle.anz = p.2.val} := by
  rw [hb₁.massErhalt, hb₂.massErhalt]

end Gabbro.Core.Beobachtung
