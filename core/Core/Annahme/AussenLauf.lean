module

public import Core.Annahme.Annahme

@[expose] public section

namespace Gabbro.Core.Annahme

open Katalog Maschine

variable {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}

private theorem fragen_vor_aktion {t c s u s' a ls es}
    (aktion : FuehrtAus E.einrichtung t c s u a ls es s')
    (rahmen : Zustandsrahmen s u)
    (alt : ∀ q ∈ s.fragen, q.cut < t) : ∀ q ∈ s'.fragen, q.cut < t + 1 := by
  cases aktion with
  | frage q =>
    intro ev mem
    change ev ∈ u.fragen ++ [s.stelleFrage t c q] at mem
    rw [rahmen.fragen, List.mem_append, List.mem_singleton] at mem
    rcases mem with bisher | rfl
    · exact Nat.lt_succ_of_lt (alt ev bisher)
    · exact Nat.lt_succ_self _
  | intern | warte _ | sperre _ _ | verbrauche _ | rueckkehr _ _ =>
    exact fun _ mem => Nat.lt_succ_of_lt (alt _ (rahmen.fragen ▸ mem))

private theorem fragen_vor_schritt {run t s w spur s'}
    (step : I.Schritt E.einrichtung E.system E.katalog run t s (w, spur) s')
    (alt : ∀ q ∈ s.fragen, q.cut < t) : ∀ q ∈ s'.fragen, q.cut < t + 1 := by
  cases step with
  | kontext _ _ _ aus =>
    obtain ⟨rahmen, _, _, v, aktion, _, ziel⟩ := aus
    rw [ziel]
    exact fragen_vor_aktion (E := E) aktion rahmen alt
  | antwort _ arrives =>
    rw [arrives.2.2.2]
    exact fun _ mem => Nat.lt_succ_of_lt (alt _ mem)
  | interrupt _ enters =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, ziel⟩ := enters
    rw [ziel]
    exact fun _ mem => Nat.lt_succ_of_lt (alt _ mem)
  | absturz crash =>
    rw [crash.genau.2]
    exact fun _ mem => Nat.lt_succ_of_lt (alt _ mem)

private theorem offene_griffe_schritt (akzeptiert : Akzeptiert E) {run t s w spur s'}
    (step : I.Schritt E.einrichtung E.system E.katalog run t s (w, spur) s')
    (alt : ∀ q ∈ s.fragen, q.cut < t) (offen : OffeneGriffeEigen s) : OffeneGriffeEigen s' := by
  have regel := akzeptiert.1.2.2.2 run t s w spur s' step
  cases step with
  | kontext _ _ _ _ => exact regel.2.1 offen
  | antwort _ arrives =>
    rw [arrives.2.2.2]
    intro q mem epoche unbenutzt
    exact offen q mem epoche (fun a bisher => unbenutzt a (List.mem_append_left _ bisher))
  | interrupt _ enters =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, ziel⟩ := enters
    rw [ziel]
    exact offen
  | absturz crash =>
    rw [crash.genau.2]
    intro q mem epoche _
    exact (Nat.not_le_of_lt (Nat.lt_succ_of_lt (alt q mem)) epoche).elim

/-- Outstanding ideal requests retain their own rights at every hardware cut. -/
theorem akzeptiert_offene_griffe (akzeptiert : Akzeptiert E) (η : I.Lauf E)
    (lauf : I.Laeufe E η) (t : Nat) : OffeneGriffeEigen (η.zeit.zustand t) := by
  suffices ∀ t, (∀ q ∈ (η.zeit.zustand t).fragen, q.cut < t) ∧ OffeneGriffeEigen (η.zeit.zustand t) from
    (this t).2
  intro t
  induction t with
  | zero =>
    rw [lauf.2.2.2.1]
    exact ⟨fun _ mem => (List.not_mem_nil mem).elim, fun _ mem => (List.not_mem_nil mem).elim⟩
  | succ t ih =>
    cases η.zeit.takt t with
    | wartet _ gleich _ => exact ⟨fun _ mem => Nat.lt_succ_of_lt (ih.1 _ (gleich ▸ mem)), gleich.symm ▸ ih.2⟩
    | schritt _ step =>
      exact ⟨fragen_vor_schritt (E := E) step ih.1, offene_griffe_schritt akzeptiert step ih.1 ih.2⟩

/-- A successful ideal reply commits with both program-held rights and catalogue validity
    at its own cut, for the exact request instance the answer completes. -/
theorem akzeptiert_antwort_commit (akzeptiert : Akzeptiert E) (η : I.Lauf E)
    (lauf : I.Laeufe E η) {t a spur}
    (step : AntwortSchritt E.einrichtung E.katalog η.hw t a (η.zeit.zustand t) spur (η.zeit.zustand (t + 1)))
    (ok : a.reply.result.isOk = true) :
    (∃ c, c.nummer = a.context ∧ AussengriffeEigen (η.zeit.zustand t) c a.question) ∧
    Aussen.GueltigBeiCommit E.katalog.plattform (η.hw.politik.sicht t (η.zeit.zustand t).verlauf) a.question := by
  obtain ⟨q, mem, epoche, _, kontext, instanz, frage⟩ := step.1.2.2.2.1
  have rechte := akzeptiert_offene_griffe akzeptiert η lauf t q mem epoche
    (fun e bisher => instanz.symm ▸ step.1.2.2.2.2 e bisher)
  rw [kontext, frage] at rechte
  exact ⟨rechte, antwort_gueltig (E := E) step lauf.1 lauf.2.1 ok⟩

end Gabbro.Core.Annahme
