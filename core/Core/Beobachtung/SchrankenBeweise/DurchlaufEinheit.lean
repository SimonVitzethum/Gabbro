/-
  File:      Core/Beobachtung/SchrankenBeweise/DurchlaufEinheit.lean
  Subject:   PER-PASS COST MARKS (MK-12a follow-up): the start duty and the protocol duty of the
             units and their loaders. The start duty holds for every unit because every mark
             window is empty at cut zero; the protocol duty holds for every unit because a restart
             discards the volatile mark stand of every context before recovery code runs.
-/
module

public import Core.Beobachtung.SchrankenBeweise.Durchlauf

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Annahme
open Annahme.Hosted

variable {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}

/-- Counting a last unmarked tick does not change an interval count. -/
private theorem zaehle_still {markiert : Nat → Bool} {anfang k : Nat}
    (still : markiert (anfang + k) = false) :
    I.zaehle markiert anfang (k + 1) = I.zaehle markiert anfang k := by
  simp only [I.zaehle, still, Bool.false_eq_true, if_false, Nat.add_zero]

/-- A tick that is no context step of `c` adds nothing to the context cost of `c`. -/
private theorem kontextkosten_fremd {ρ : Lauf E} {c : Kontext} {a k t : Nat}
    (eq : a + k = t)
    (fremd : ∀ d w spur, ρ.zeit.spur t = some (.kontext d w, spur) → d ≠ c) :
    Kontextkosten ρ c a (k + 1) = Kontextkosten ρ c a k := by
  have tick : ∀ d w spur, ρ.zeit.spur (a + k) = some (.kontext d w, spur) → d ≠ c := by
    intro d w spur h
    rw [eq] at h
    exact fremd d w spur h
  have still : (fun t => match ρ.zeit.spur t with
      | some (.kontext d _, _) => decide (c = d)
      | some (.antwort _, _) | some (.interrupt _, _) | some (.absturz, _) | none => false)
      (a + k) = false := by
    change (match ρ.zeit.spur (a + k) with
      | some (.kontext d _, _) => decide (c = d)
      | some (.antwort _, _) | some (.interrupt _, _) | some (.absturz, _) | none => false)
      = false
    cases hsp : ρ.zeit.spur (a + k) with
    | none => rfl
    | some label =>
      rcases label with ⟨w, spur⟩
      cases w with
      | antwort _ | interrupt _ | absturz => rfl
      | kontext d _ =>
        show decide (c = d) = false
        exact decide_eq_false (Ne.symm (tick d _ _ hsp))
  simp only [Kontextkosten]
  rw [zaehle_still still]

/-- The start duty of every unit. At cut zero the only candidate is the loader's state; every
    mark read from its local stand has an empty cost window (`0 - m.2 = 0`), so the ceiling is
    met whether the stand is empty or carries marks. Loader data therefore need no extra premise
    for the start leg. -/
theorem durchlaufStart : DurchlaufStartPflicht E := by
  intro h ρ lauf t' s hle sEq c m hmem
  have ht0 : t' = 0 := by omega
  subst t'
  have e0 : 0 - m.2 = 0 := by omega
  rw [e0]
  simp only [Kontextkosten, I.zaehle]
  intro n _
  exact Nat.zero_le n

/-- The missing premise of the protocol duty: a protocol transition never introduces an open
    mark whose window already contains executed ticks. Every mark of the successor's stand was
    already open before the tick, or opens after it. Answers and interrupts satisfy this
    definitionally (they leave the local state untouched); a crash only satisfies it when the
    recovery entry's loader data carries no such back-dated mark. -/
def ProtokollMarkenErhaltend (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form) : Prop :=
  ∀ {h : Umgebung} {ρ : Lauf E} {t : Nat} {w : SchrittWahl Wahl} {spur : SchrittSpur Ort Wert}
    {vor nach : Zustand L Ort Wert Raum Lok Grund},
    Laeufe E h ρ →
    ρ.zeit.zustand t = some vor → ρ.zeit.spur t = some (w, spur) → ProtokollB8Wahl w →
    ρ.zeit.zustand (t + 1) = some nach →
    ∀ c m, m ∈ E.schranken.durchlaufstand (nach.lokal c) →
      m ∈ E.schranken.durchlaufstand (vor.lokal c) ∨ t < m.2

/-- Every protocol transition keeps the mark stand: an answer or an interrupt leaves the local
    state untouched, and a restart discards the volatile stand of every context before recovery
    code runs. The clearing is the declared binding of `Schrankendaten`, not a premise of a unit. -/
theorem durchlaufProtokollMarken : ProtokollMarkenErhaltend E := by
  intro h ρ t w spur vor nach lauf vorEq spurEq wahl nachEq c m hmem
  have takt := ρ.zeit.takt t
  rw [vorEq, spurEq, nachEq] at takt
  cases takt with
  | wartet label _ _ => cases label
  | schritt label step =>
      cases step with
      | schritt impl =>
          cases impl with
          | kontext _ _ _ _ =>
              cases w with
              | kontext _ _ => exact False.elim (by simpa only [ProtokollB8Wahl] using wahl)
              | antwort _ | interrupt _ | absturz => cases label
          | antwort _ hA =>
              have hlocal : nach.lokal = vor.lokal := by
                obtain ⟨_, _, _, stateEq⟩ := hA
                rw [stateEq]
                rfl
              rw [hlocal] at hmem
              exact Or.inl hmem
          | interrupt _ hI =>
              have hlocal : nach.lokal = vor.lokal := by
                obtain ⟨_, _, _, _, _, _, _, _, _, _, stateEq⟩ := hI
                rw [stateEq]
                rfl
              rw [hlocal] at hmem
              exact Or.inl hmem
          | absturz hA =>
              have hleer : E.schranken.durchlaufstand (nach.lokal c) = [] := by
                rw [hA.genau.2]
                simp only [Zustand.wiederanlauf, Zustand.start]
                exact E.schranken.durchlaufstand_nachVerwerfenLeer _ _
              rw [hleer] at hmem
              exact (List.not_mem_nil hmem).elim

/-- The protocol duty holds unconditionally: older cuts carry over by the mark-stand theorem; a new
    cut's inherited mark keeps its cost because the protocol tick is foreign to every context. A
    mark opening after the tick has an empty window. -/
theorem durchlaufProtokoll : DurchlaufProtokollPflicht E := by
  intro h ρ lauf t w spur vor nach hyp vorEq spurEq wahl nachEq t' s hle sEq c m hmem
  by_cases hle' : t' ≤ t
  · exact hyp t' s hle' sEq c m hmem
  · have et : t' = t + 1 := by omega
    subst t'
    by_cases hm2 : t < m.2
    · have e0 : t + 1 - m.2 = 0 := by omega
      rw [e0]
      simp only [Kontextkosten, I.zaehle]
      intro n _
      exact Nat.zero_le n
    · have hmemOder := durchlaufProtokollMarken lauf vorEq spurEq wahl sEq c m hmem
      have hvor : m ∈ E.schranken.durchlaufstand (vor.lokal c) := by
        cases hmemOder with
        | inl hm => exact hm
        | inr hlt => exact (hm2 hlt).elim
      have boundVor := hyp t vor (Nat.le_refl t) vorEq c m hvor
      have fremd : ∀ d w' spur', ρ.zeit.spur t = some (.kontext d w', spur') → d ≠ c := by
        intro d w' spur' hsp
        have pairEq : (w, spur) = (.kontext d w', spur') := Option.some.inj (spurEq.symm.trans hsp)
        have wEq : w = .kontext d w' := congrArg Prod.fst pairEq
        cases w with
        | kontext _ _ => exact False.elim wahl
        | antwort _ | interrupt _ | absturz => cases wEq
      have ewin : t + 1 - m.2 = (t - m.2) + 1 := by omega
      rw [ewin]
      have eadd : m.2 + (t - m.2) = t := by omega
      rw [kontextkosten_fremd eadd fremd]
      exact boundVor

/-- **Per-pass duties of units and loaders, in one pinned statement** (MK-12a follow-up): the
    start duty and the protocol duty hold for every unit. The mark-stand premise is discharged
    by the model: a restart discards every volatile mark before recovery code runs. -/
def DurchlaufEinheitAussage : Prop :=
  (∀ (L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type) [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form),
    DurchlaufStartPflicht E) ∧
  ∀ (L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type) [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form),
    DurchlaufProtokollPflicht E

theorem durchlaufEinheit : DurchlaufEinheitAussage := by
  refine ⟨?_, ?_⟩
  · intro L Ort Wert Raum Lok Grund Bedingung Wahl Form inst E
    exact durchlaufStart
  · intro L Ort Wert Raum Lok Grund Bedingung Wahl Form inst E
    exact durchlaufProtokoll

/-- Joint satisfiability: the hosted unit with its concrete run has no open marks, so both duties
    hold and the mark-stand premise is discharged by its empty declaration. -/
theorem durchlaufEinheit_erfuellbar :
    ∃ (E : Modell) (h : Umgebung) (ρ : Lauf E),
      Laeufe E h ρ ∧ DurchlaufStartPflicht E ∧ DurchlaufProtokollPflicht E := by
  obtain ⟨s, zul⟩ := zulStart_erfuellbar (erlaubt []) Sicherheit.Laufkonstruktion.bild_gueltig
  obtain ⟨ρ, g, g', lauf, _, _, _, _, _, _, _, _, _, _⟩ := konkreter_lauf zul []
  exact ⟨einheit, umgebung [], ρ, lauf, durchlaufStart, durchlaufProtokoll⟩

end Gabbro.Core.Beobachtung
