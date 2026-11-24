module

public import Core.Beobachtung.Fluss.Fragment

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Ast.Semantik (Fragment Befehl)

def KontrollflussNIAussage : Prop :=
  FamilienNI .kontrollfluss

private theorem spekulationszugriffe_leer {Ort : Type} (h : Spekulationshuelle) :
    h.zugriffe ([] : List (Option Ort)) = [] := by
  cases hfen : h.fenster with
  | none => rfl
  | some n => cases n <;> rfl

/-- Every context step of a source fragment changes only the local frame: its plan is the
    internal plan and the machine protocol contributes no event. The step is therefore
    unobservable, so an already covered low prefix stays covered. Control-flow forms are
    exactly the forms whose only effect is the program counter and the local bindings. -/
theorem kontrollflussNI : KontrollflussNIAussage := by
  intro p plattform f familie regelFluss
  intro h₁ h₂ ρ₁ ρ₂ vergleich predictor t c w spur vor vorAt kopf spurAt abgedeckt
  refine stummer_schritt_deckt ?_ abgedeckt
  have tick := ρ₁.zeit.takt t
  rw [vorAt] at tick
  rw [spurAt] at tick
  cases tick with
  | wartet label _ _ => cases label
  | schritt label step =>
      cases nach : ρ₁.zeit.zustand (t + 1) with
      | none =>
          rw [nach] at step
          cases step
      | some next =>
          rw [nach] at step
          cases step with
          | schritt impl =>
              cases impl with
              | kontext keinAbsturz bereit regel aus =>
                  obtain ⟨i, kopfI, implI⟩ := regel
                  change [plan] = [Ast.Semantik.plan] ∧ u = Befehl.nach i c vor at implI
                  have planEq : plan = Ast.Semantik.plan := (List.cons.inj implI.1).1
                  have uEq : u = Befehl.nach i c vor := implI.2
                  rw [planEq] at aus
                  rw [FuehrtSchrittAus] at aus
                  obtain ⟨rahmen, liest, sperren, v, fuehrtAus, speicherfolge, nextEq⟩ := aus
                  change FuehrtAus (p.einheit plattform).einrichtung t c vor u .intern sperren spur.aussen v at fuehrtAus
                  have bestimmt := FuehrtAus.bestimmt fuehrtAus
                    (FuehrtAus.intern (e := (p.einheit plattform).einrichtung) (t := t) (c := c) (s := vor) (u := u))
                  obtain ⟨sperrenLeer, aussenLeer, vEq⟩ := bestimmt
                  rw [sperrenLeer, aussenLeer] at speicherfolge
                  simp only [Ast.Semantik.plan, schreibEreignisse, List.nil_append, List.append_nil] at speicherfolge
                  have spurLeer : spur.speicher = [] := by
                    cases speicherfolge with
                    | nil => rfl
                  rw [vEq] at nextEq
                  have uStatus : u.status = vor.status := by
                    rw [uEq]
                    rfl
                  have uBuchung : u.buchung = vor.buchung := by
                    rw [uEq]
                    rfl
                  have nextStatus : next.status = vor.status := by
                    rw [nextEq]
                    exact uStatus
                  have nextBuchung : next.buchung = vor.buchung := by
                    rw [nextEq]
                    exact uBuchung
                  have nextStatusFun : ∀ c', next.status c' = vor.status c' := by
                    intro c'
                    rw [nextStatus]
                  have konstantFalsch : (p.einheit plattform).fluss.konstantzeit f = false := rfl
                  have spekLeer :
                      (p.einheit plattform).fluss.spekulativ f (vor.lokal c) predictor = [] := rfl
                  have zugriffeLeer :
                      (p.einheit plattform).katalog.plattform.spekulationshuelle.zugriffe
                        ((p.einheit plattform).fluss.spekulativ f (vor.lokal c) predictor) = [] := by
                    rw [spekLeer]
                    exact spekulationszugriffe_leer _
                  have commitLeer :
                      commitBeob (p.einheit plattform).katalog.plattform vor next = [] := by
                    rw [commitBeob, nextBuchung, List.drop_length]
                    rfl
                  have ausgabeLeer :
                      ausgabeBeob (p.einheit plattform) c (vor.lokal c) (next.lokal c) = [] := by
                    rw [ausgabeBeob, Flussdaten.ausgabeZuwachs]
                    rfl
                  have zeitLeer : zeitBeob ρ₁ c (vor.lokal c) (next.lokal c) = [] := by
                    rw [zeitBeob]
                    rfl
                  have kontextLeer : kontextBeob ρ₁ predictor t c vor next spur = [] := by
                    rw [kontextBeob]
                    rw [kopf]
                    simp only [zugriffeLeer, List.map_nil, konstantFalsch, ↓reduceIte,
                      List.nil_append, commitLeer, ausgabeLeer, zeitLeer]
                  have keinEnde :
                      ¬ ∃ c', (neuBeendet vor next (p.einheit plattform).etiketten c').isSome = true := by
                    rintro ⟨c', h⟩
                    have hn : neuBeendet vor next (p.einheit plattform).etiketten c' = none := by
                      rw [neuBeendet]
                      rw [nextStatusFun c']
                      cases vor.status c' <;> rfl
                    rw [hn] at h
                    cases h
                  rw [schrittBeob, spurAt, vorAt, nach]
                  rw [spurLeer, aussenLeer, kontextLeer]
                  simp only [keinEnde, ↓reduceIte, List.nil_append]
                  rfl

end Gabbro.Core.Beobachtung
