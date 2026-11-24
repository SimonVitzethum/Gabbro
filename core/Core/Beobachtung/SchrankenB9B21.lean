module

public import Core.Beobachtung.SchrankenB8

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine

variable {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}

/-- Every context's stack meets the unit's declared depth bound at this state. -/
def StapelZustand (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (s : Zustand L Ort Wert Raum Lok Grund) : Prop :=
  ∀ c, UnterGrenze E.schranken.stapel (E.schranken.stapelTiefe (s.lokal c))

/-- The unit's memory ceiling is global and counts live allocation cells. An open ceiling
    imposes no cardinality or finiteness condition on the provider's allocations. -/
def SpeicherZustand (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (s : Zustand L Ort Wert Raum Lok Grund) : Prop :=
  ∀ n, E.schranken.speicher = some n → (LebendeZellen s).encard ≤ n

/-- B9 and B21 are state properties. Each loaded cut is checked against the same declarations. -/
def RessourcenPrefix (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (ρ : Lauf E) (t : Nat) : Prop :=
  ∀ s, ρ.zeit.zustand t = some s → StapelZustand E s ∧ SpeicherZustand E s

/-- A successful load must establish both bounds on every admitted run. -/
def ressourcenStartAussage (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form) : Prop :=
  ∀ {h : Umgebung} {ρ : Lauf E}, Laeufe E h ρ → RessourcenPrefix E ρ 0

/-- A form preserves both bounds over its concrete implementation step on an admitted run.
    The witness to the step is available to local proofs, including the action's final effects. -/
def ressourcenRegelAussage (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (f : Form) : Prop :=
  ∀ {h : Umgebung} {ρ : Lauf E}, Laeufe E h ρ → ∀ t c w spur vor nach,
    ρ.zeit.zustand t = some vor → E.system.kopf vor c = some f →
    ρ.zeit.spur t = some (.kontext c w, spur) → ρ.zeit.zustand (t + 1) = some nach →
    ImplSchritt E.einrichtung E.system E.katalog ρ.hw t vor (.kontext c w, spur) nach →
    StapelZustand E vor → SpeicherZustand E vor → StapelZustand E nach ∧ SpeicherZustand E nach

/-- Answer, interrupt and crash steps preserve the declared bounds, including any reinitialisation. -/
def ressourcenProtokollAussage (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form) : Prop :=
  ∀ {h : Umgebung} {ρ : Lauf E}, Laeufe E h ρ → ∀ t w spur vor nach,
    ρ.zeit.zustand t = some vor → ρ.zeit.spur t = some (w, spur) →
    ProtokollB8Wahl w → ρ.zeit.zustand (t + 1) = some nach →
    ImplSchritt E.einrichtung E.system E.katalog ρ.hw t vor (w, spur) nach →
    StapelZustand E vor → SpeicherZustand E vor → StapelZustand E nach ∧ SpeicherZustand E nach

structure RessourcenPflichten (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form) : Prop where
  start : ressourcenStartAussage E
  regel : ∀ f, ressourcenRegelAussage E f
  protokoll : ressourcenProtokollAussage E

/-- The stack and memory legs of `ImSchranken` over a whole admitted run. -/
def ressourcenAbschlussAussage (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form) : Prop :=
  RessourcenPflichten E → ∀ {h : Umgebung} {ρ : Lauf E}, Laeufe E h ρ → ∀ t, RessourcenPrefix E ρ t

/-- Cover idle ticks by state equality, source steps by their selected form and all other
    occupied ticks by the protocol obligation. A failed load never produces a resource state. -/
theorem b9_b21_aus_pflichten : ressourcenAbschlussAussage E := by
  intro pflichten h ρ lauf t
  induction t with
  | zero => exact pflichten.start lauf
  | succ t ih =>
    intro nach nachEq
    have takt := ρ.zeit.takt t
    generalize vorEq : ρ.zeit.zustand t = vor at takt
    rw [nachEq] at takt
    cases takt with
    | wartet _ gleich _ => exact ih nach (vorEq.trans gleich.symm)
    | schritt label folge =>
      cases folge with
      | schritt step =>
        rename_i vor _
        have alt := ih vor vorEq
        cases step with
        | kontext normal bereit regel aus =>
          obtain ⟨f, kopf, regelSchritt⟩ := regel
          exact pflichten.regel f lauf t _ _ _ _ _ vorEq kopf label nachEq
            (.kontext normal bereit ⟨f, kopf, regelSchritt⟩ aus) alt.1 alt.2
        | antwort normal step =>
          exact pflichten.protokoll lauf t _ _ _ _ vorEq label trivial nachEq
            (.antwort normal step) alt.1 alt.2
        | interrupt normal step =>
          exact pflichten.protokoll lauf t _ _ _ _ vorEq label trivial nachEq
            (.interrupt normal step) alt.1 alt.2
        | absturz step =>
          exact pflichten.protokoll lauf t _ _ _ _ vorEq label trivial nachEq (.absturz step) alt.1 alt.2

/-- Supplying B8 and the B9/B21 obligations yields the original `ImSchranken` proposition. -/
theorem imSchranken_aus_abschluessen {h : Umgebung} {ρ : Lauf E} (lauf : Laeufe E h ρ)
    (b8 : B8Abschluss E ρ) (pflichten : RessourcenPflichten E) : ImSchranken E ρ := by
  have ressourcen := b9_b21_aus_pflichten pflichten lauf
  exact b8_abschluss_imSchranken.mp ⟨b8,
    fun t s eq => (ressourcen t s eq).2, fun t s eq => (ressourcen t s eq).1⟩

end Gabbro.Core.Beobachtung
