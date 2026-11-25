module

public import Core.Annahme.Lokal

@[expose] public section

namespace Gabbro.Core.Annahme

open Katalog Maschine

variable {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}

/-- An invariant sufficient for proving commit authority in an ideal run. -/
def OffeneGriffeEigen (s : Zustand L Ort Wert Raum Lok Grund) : Prop :=
  ∀ q ∈ s.fragen, s.epoche ≤ q.cut →
    (∀ a ∈ s.antworten, a.questionInstance ≠ q.questionInstance) →
    ∃ c, c.nummer = q.context ∧ AussengriffeEigen s c q.question

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
  | intern | warte _ | sperre _ _ | verbrauche _ | rueckkehr _ _ | starte _ | verbinde _ _ | beende _
    | wechsle _ _ _ _ =>
    exact fun _ mem => Nat.lt_succ_of_lt (alt _ (rahmen.fragen ▸ mem))

private theorem fragen_vor_schritt {run t s w spur s'}
    (step : I.Schritt E.einrichtung E.system E.katalog run t s (w, spur) s')
    (alt : ∀ q ∈ s.fragen, q.cut < t) : ∀ q ∈ s'.fragen, q.cut < t + 1 := by
  cases step with
  | kontext _ _ _ aus =>
    obtain ⟨rahmen, _, _, v, aktion, _, ziel⟩ := aus
    rw [ziel]
    exact fragen_vor_aktion (E := E) (s' := v) aktion rahmen alt
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

section

variable (erhalt : ∀ run t s c w spur s',
  I.Schritt E.einrichtung E.system E.katalog run t s (.kontext c w, spur) s' →
  OffeneGriffeEigen s → OffeneGriffeEigen s')

include erhalt

private theorem offene_griffe_schritt {run t s w spur s'}
    (step : I.Schritt E.einrichtung E.system E.katalog run t s (w, spur) s')
    (alt : ∀ q ∈ s.fragen, q.cut < t) (offen : OffeneGriffeEigen s) : OffeneGriffeEigen s' := by
  cases step with
  | kontext normal bereit regel aus => exact erhalt run t s _ _ spur s' (.kontext normal bereit regel aus) offen
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

private theorem offene_griffe_am_schnitt (η : I.Lauf E)
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
      exact ⟨fragen_vor_schritt (E := E) step ih.1, offene_griffe_schritt erhalt step ih.1 ih.2⟩

end

private theorem antwort_aus_spur (η : I.Lauf E) {t a spur}
    (marke : η.zeit.spur t = some (.antwort a, spur)) :
    AntwortSchritt E.einrichtung E.katalog η.hw t a (η.zeit.zustand t) spur (η.zeit.zustand (t + 1)) := by
  have takt := η.zeit.takt t
  rw [marke] at takt
  cases takt with
  | wartet label _ _ => cases label
  | schritt label step =>
    cases label
    cases step with
    | antwort _ step => exact step

/-- The catalogue supplies commit validity. The forms can prove commit ownership by
    preserving ownership of pending requests. -/
theorem aussen_gueltig_aus_kontext (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (kontext : ∀ run t s c w spur s',
      I.Schritt E.einrichtung E.system E.katalog run t s (.kontext c w, spur) s' →
      AussenKontextLokal E c run t s spur s' ∧ (OffeneGriffeEigen s → OffeneGriffeEigen s')) :
    AussenGueltig E := by
  constructor
  · intro run t s w spur s' step
    cases step with
    | kontext normal bereit regel aus =>
      exact (kontext run t s _ _ spur s' (.kontext normal bereit regel aus)).1
    | antwort _ arrives => exact fun _ hw konform ok => antwort_gueltig (E := E) arrives hw konform ok
    | interrupt _ _ | absturz _ => trivial
  · intro η lauf t a spur marke _
    have step := antwort_aus_spur η marke
    obtain ⟨q, mem, epoche, _, actor, instanz, frage⟩ := step.1.2.2.2.1
    have offen := offene_griffe_am_schnitt (fun run t s c w spur s' h => (kontext run t s c w spur s' h).2) η lauf t
    have rechte := offen q mem epoche (fun e bisher => instanz.symm ▸ step.1.2.2.2.2 e bisher)
    rwa [actor, frage] at rechte

/-- A successful ideal reply commits with both program-held rights and catalogue validity
    at its own cut, for the exact request instance the answer completes. -/
theorem antwort_commit (gueltig : AussenGueltig E) (η : I.Lauf E)
    (lauf : I.Laeufe E η) {t a spur}
    (marke : η.zeit.spur t = some (.antwort a, spur))
    (ok : a.reply.result.isOk = true) :
    (∃ c, c.nummer = a.context ∧ AussengriffeEigen (η.zeit.zustand t) c a.question) ∧
    Aussen.GueltigBeiCommit E.katalog.plattform (η.hw.politik.sicht t (η.zeit.zustand t).verlauf) a.question :=
  ⟨gueltig.2 η lauf t a spur marke ok, antwort_gueltig (E := E) (antwort_aus_spur η marke) lauf.1 lauf.2.1 ok⟩

end Gabbro.Core.Annahme
