module

public import Core.Ideal.Komposition
public import Core.Verfeinerung.Maschine
public import Core.Verfeinerung.Sicherheit

@[expose] public section

namespace Gabbro.Core.Maschine.I

open Gabbro.Core.Katalog

variable {L Ort Wert Raum Lok Grund Bedingung Wahl F Obs : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F}
variable {ρ : Maschine.Lauf E} {η : Lauf E}

/-- Every concrete cut of a run covered by the M4 obligations has its graph
    and answer-consumption invariants. -/
theorem AbgleichPflichten.sicherheit_am_schnitt (pflicht : AbgleichPflichten E)
    {h : Umgebung} (run : Maschine.Laeufe E h ρ) (k : Maschine.Schnitt E ρ) :
    ∃ z, ρ.zeit.zustand k.val = some z ∧ z.SpeicherGut ∧ z.Verbrauch := by
  obtain ⟨z, loaded, related⟩ := pflicht.laden h ρ.start run.1 run.2.2.1
  exact speicher_verbrauch_im_lauf ⟨z, run.2.2.2.trans loaded, related.1⟩ k.val

/-- At the image of each concrete cut, the ideal state is the state at that
    hardware tick, even if the most recent ideal transition was earlier. -/
theorem Laufabgleich.schnitt (h : Laufabgleich ρ η) (k : Maschine.Schnitt E ρ) :
    ∃ s, ρ.zeit.zustand k.val = some s ∧
      Zustandsbezug E s (η.zeit.zustand (Zeitlauf.schnittBild ρ.zeit η.zeit k).val) := by
  obtain ⟨s, load, rel⟩ := h.zustand k.val
  exact ⟨s, load, (η.zeit.letzterSchnitt_zustand k.val).symm ▸ rel⟩

theorem Laufabgleich.schnitt_deckt (h : Laufabgleich ρ η) :
    Function.Surjective (Zeitlauf.schnittBild ρ.zeit η.zeit) :=
  Zeitlauf.schnittBild_deckt ρ.zeit η.zeit fun t pause => (h.spur t).gedeckt pause

theorem Laufabgleich.endlich (h : Laufabgleich ρ η) (run : Laeufe E η) :
    ρ.zeit.Endlich ↔ η.zeit.Endlich := by
  constructor
  · rintro ⟨k, tail⟩
    exact Zeitlauf.endlich_ab (ρ := η.zeit) k.val fun t after => (h.spur t).gedeckt (tail t after)
  · intro ends
    obtain ⟨q, vacant⟩ := run.2.2.2.2.1.2 ends
    obtain ⟨k, idle⟩ := ends
    refine Zeitlauf.endlich_ab (ρ := ρ.zeit) (max k.val q) fun t after => ?_
    rcases (h.frei t).mp (vacant t ((Nat.le_max_right _ _).trans after)) with empty | used
    · exact empty
    · exact (used (idle t ((Nat.le_max_left _ _).trans after))).elim

theorem Laufabgleich.anfang (h : Laufabgleich ρ η) (run : Laeufe E η) :
    ZustandAm E η (Zeitlauf.schnittBild ρ.zeit η.zeit ⟨0, Or.inl rfl⟩) = I.start E ρ.start :=
  (I.anfang E η run).trans (congrArg (I.start E) h.start)

theorem Laufabgleich.aussen_am_schnitt (h : Laufabgleich ρ η) (k : Maschine.Schnitt E ρ) :
    ∃ s, ρ.zeit.zustand k.val = some s ∧
      AussenBezug s (η.zeit.zustand (Zeitlauf.schnittBild ρ.zeit η.zeit k).val) := by
  obtain ⟨s, load, related⟩ := h.schnitt k
  exact ⟨s, load, related.1.aussen⟩

/-- The concrete run records the reads-from and coherence choices as well as
    program order. The matched ideal run uses the same resolution at every tick. -/
theorem Laufabgleich.speicherwahl (h : Laufabgleich ρ η) (t : Nat) :
    ∃ s, ρ.zeit.zustand t = some s ∧ SpeicherWahlGleich s.graph (η.zeit.zustand t).graph := by
  obtain ⟨s, loaded, related⟩ := h.zustand t
  have eq := congrArg Zustand.graph related.1
  rw [← eq]
  exact ⟨s, loaded, rfl, rfl, rfl⟩

theorem SpurAbgleich.beobachtung {c i : Option (SchrittWahl Wahl × SchrittSpur Ort Wert)}
    (h : SpurAbgleich c i)
    (sicht : SchrittSpur Ort Wert → List Obs) (privat : sicht ⟨[], []⟩ = []) :
    c.elim [] (sicht ∘ Prod.snd) = i.elim [] (sicht ∘ Prod.snd) := by
  cases h with
  | pause => rfl
  | privat _ _ => exact privat
  | schritt _ => rfl

/-- Equality of the entire ordered observed prefix. In particular either
    projection of the M4 step trace, or a projection keeping both, may be used. -/
theorem Laufabgleich.beobachtung (h : Laufabgleich ρ η)
    (sicht : SchrittSpur Ort Wert → List Obs) (privat : sicht ⟨[], []⟩ = []) (k : Maschine.Schnitt E ρ) :
    Zeitlauf.praefix (fun t => (ρ.zeit.spur t).elim [] (sicht ∘ Prod.snd)) k.val =
      Zeitlauf.praefix (fun t => (η.zeit.spur t).elim [] (sicht ∘ Prod.snd))
        (Zeitlauf.schnittBild ρ.zeit η.zeit k).val := by
  let beob := fun t => (η.zeit.spur t).elim [] (sicht ∘ Prod.snd)
  have gleich : (fun t => (ρ.zeit.spur t).elim [] (sicht ∘ Prod.snd)) = beob :=
    funext fun t => (h.spur t).beobachtung sicht privat
  rw [gleich]
  exact (η.zeit.praefix_letzterSchnitt beob (fun t no => by simp only [beob, no, Option.elim]) k.val).symm

/-- Extract the complete typed arrivals carried by a step's catalogue trace. -/
def Antwortspur (spur : SchrittSpur Ort Wert) : List AntwortEreignis :=
  spur.aussen.filterMap fun
    | .antwort a => some a
    | _ => none

private theorem aktions_antwortbuch {e : Einrichtung L Ort Wert Raum Lok Grund Bedingung}
    {s u v : Zustand L Ort Wert Raum Lok Grund} {t c akt locks outside}
    (frame : Zustandsrahmen s u) (action : FuehrtAus e t c s u akt locks outside v) :
    v.antworten = s.antworten ++ Antwortspur (Ort := Ort) (Wert := Wert) ⟨[], outside⟩ := by
  cases action <;> exact frame.antworten.trans (List.append_nil _).symm

/-- The concrete answer book is exactly the ordered arrival trace at every cut
    from an empty book. In particular, consuming a reply leaves this trace intact. -/
theorem antwortbuch_im_lauf
    (init : ∃ z, ρ.zeit.zustand 0 = some z ∧ z.antworten = []) (t : Nat) :
    ∃ z, ρ.zeit.zustand t = some z ∧ z.antworten =
      Zeitlauf.praefix (fun n => (ρ.zeit.spur n).elim [] (Antwortspur ∘ Prod.snd)) t := by
  induction t with
  | zero => exact init
  | succ t ih =>
    obtain ⟨s, loaded, book⟩ := ih
    have tick := ρ.zeit.takt t
    rw [loaded] at tick
    cases tick with
    | wartet mark same _ =>
      exact ⟨s, same, by simpa only [Zeitlauf.praefix, mark, Option.elim, List.append_nil] using book⟩
    | schritt mark transition =>
      cases after : ρ.zeit.zustand (t + 1) with
      | none =>
        rw [after] at transition
        cases transition
      | some s' =>
        refine ⟨s', rfl, ?_⟩
        rw [Zeitlauf.praefix, ← book, mark]
        rw [after] at transition
        cases transition with
        | schritt step =>
          cases step with
          | kontext _ _ _ execute =>
            obtain ⟨frame, _, _, _, action, _, state⟩ := execute
            have accounted := aktions_antwortbuch frame action
            rw [state]
            exact accounted
          | antwort _ arrives =>
            obtain ⟨trace, book, _⟩ := arrives.ankunft E.einrichtung
            rw [book]
            simp only [Option.elim, Function.comp_apply, Antwortspur, trace, List.filterMap_cons,
              List.filterMap_nil]
          | interrupt _ enters =>
            obtain ⟨_, _, _, _, _, _, _, _, trace, _, state⟩ := enters
            rw [state]
            simp only [Option.elim, Function.comp_apply, Antwortspur, trace, List.filterMap_cons,
              List.filterMap_nil, List.append_nil]
            rfl
          | absturz crash =>
            rw [crash.genau.1, crash.genau.2]
            exact (List.append_nil _).symm

/-- Both traces account for the same arrival book at the matched cut.
    Consumption and crash discards are tracked separately from arrival. -/
def Antwortabgleich (ρ : Maschine.Lauf E) (η : Lauf E) : Prop :=
  ∀ k : Maschine.Schnitt E ρ,
    let j := Zeitlauf.schnittBild ρ.zeit η.zeit k
    let ankunft := Zeitlauf.praefix (fun n => (ρ.zeit.spur n).elim [] (Antwortspur ∘ Prod.snd)) k.val
    ∃ s, ρ.zeit.zustand k.val = some s ∧ s.antworten = ankunft ∧
      (η.zeit.zustand j.val).antworten = ankunft ∧
      Zeitlauf.praefix (fun n => (η.zeit.spur n).elim [] (Antwortspur ∘ Prod.snd)) j.val = ankunft ∧
      s.verbraucht = (η.zeit.zustand j.val).verbraucht ∧
      s.verworfen = (η.zeit.zustand j.val).verworfen

theorem Laufabgleich.antwortabgleich (matched : Laufabgleich ρ η) (valid : Laeufe E η) :
    Antwortabgleich ρ η := by
  obtain ⟨startState, loaded, related⟩ := matched.zustand 0
  have empty : startState.antworten = [] := by
    rw [related.1.aussen.antworten, valid.2.2.2.1]
    rfl
  intro k
  obtain ⟨s, state, book⟩ := antwortbuch_im_lauf ⟨startState, loaded, empty⟩ k.val
  obtain ⟨z, atCut, outside⟩ := matched.aussen_am_schnitt k
  have same := Option.some.inj (atCut.symm.trans state)
  subst z
  exact ⟨s, state, book, outside.antworten.symm.trans book,
    (matched.beobachtung Antwortspur rfl k).symm, outside.verbraucht, outside.verworfen⟩

/-- The crash cut is matched at the same tick, with the same persistence event,
    and the recovery continuations start in one and the same state. -/
theorem Laufabgleich.absturz (h : Laufabgleich ρ η) {t : Nat}
    (offer : AbsturzAngeboten E.katalog ρ.hw t) :
    ρ.zeit.spur t = some (.absturz, absturzSpur) ∧ η.zeit.spur t = some (.absturz, absturzSpur) ∧
      ρ.zeit.zustand (t + 1) = some (η.zeit.zustand (t + 1)) := by
  obtain ⟨s, load, rel⟩ := h.zustand t
  have shared := rel.1
  change { s with lokal := (η.zeit.zustand t).lokal } = η.zeit.zustand t at shared
  exact absturz_im_lauf h.hardware.symm offer load rel.1.aussen
    (congrArg (fun z => nachAbsturz z.persistenz) shared)

theorem Laufabgleich.absturzschnitt (h : Laufabgleich ρ η) {t : Nat}
    (offer : AbsturzAngeboten E.katalog ρ.hw t) :
    ∃ (k : Maschine.Schnitt E ρ) (j : Schnitt E η),
      k.val = t + 1 ∧ j.val = t + 1 ∧ Zeitlauf.schnittBild ρ.zeit η.zeit k = j := by
  obtain ⟨konkret, ideal, _⟩ := h.absturz offer
  exact ⟨⟨t + 1, Or.inr ⟨t, _, rfl, konkret⟩⟩, ⟨t + 1, Or.inr ⟨t, _, rfl, ideal⟩⟩,
    rfl, rfl, η.zeit.letzterSchnitt_schritt ideal⟩

/-- A persistent live dispatch on a fair physical core reaches an ideal
    progress alternative other than a withheld opportunity. -/
theorem Laufabgleich.fortschritt_am_angebot (h : Laufabgleich ρ η) (run : Laeufe E η)
    (fair : FairLaeufe E.katalog η.umgebung ρ.hw)
    (fertig : ∀ s c, E.system.kopf s c = none → E.system.fertig s c)
    (regeln : ∀ i, Gabbro.Core.Ideal.RegelFortschritt E.system i)
    (komponierbar : ∀ i t s c, E.system.kopf s c = some i → s.SpeicherGut →
      ∃ w plan u spur s', (E.system.regel i).ideal c s w [plan] u ∧
        FuehrtSchrittAus E.einrichtung t c s u plan spur s')
    {kern t : Nat} {c : Kontext} (physical : kern < η.umgebung.kernzahl)
    (dispatch : ∀ i, t ≤ i → ∀ s, ρ.zeit.zustand i = some s →
      (s.kerne kern).laeuft = some c ∧ s.status c = .laeuft) :
    ∃ i, t ≤ i ∧ let s := η.zeit.zustand i
      (∃ spur next, Schritt E.einrichtung E.system E.katalog η.hw i s (.absturz, spur) next) ∨
      E.system.fertig s c ∨ (∃ b, E.system.blockiert s c b) ∨
      (∃ w spur next, Schritt E.einrichtung E.system E.katalog η.hw i s (.kontext c w, spur) next) := by
  obtain ⟨i, after, slot⟩ := fair.kerne.2 kern physical t
  obtain ⟨s, load, rel⟩ := h.zustand i
  have shared := rel.1
  change { s with lokal := (η.zeit.zustand i).lokal } = η.zeit.zustand i at shared
  have dispatched : ((η.zeit.zustand i).kerne kern).laeuft = some c := by
    rw [← shared]
    exact (dispatch i after s load).1
  have running : (η.zeit.zustand i).status c = .laeuft := by
    rw [← shared]
    exact (dispatch i after s load).2
  refine ⟨i, after, ?_⟩
  rcases fortschritt_im_lauf_koepfen run fertig regeln komponierbar i c running ⟨kern, dispatched⟩ with
    crash | done | blocked | enabled | withheld
  · exact Or.inl crash
  · exact Or.inr (Or.inl done)
  · exact Or.inr (Or.inr (Or.inl blocked))
  · exact Or.inr (Or.inr (Or.inr enabled))
  · exact (withheld.2 kern dispatched (h.hardware.symm ▸ slot)).elim

end Gabbro.Core.Maschine.I
