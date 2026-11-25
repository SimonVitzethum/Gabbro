/-
  File:      core/Core/Beobachtung/SchrankenBeweise/Klasse.lean
  Subject:   THE BOUND DUTY OF AN EFFECT CLASS (MK-03, PERFECT-MODEL §3.7, B9/B21). The checker's bounds row
             asks each instruction for `RegelSchranken`: a step keeps the stack bound and the memory bound.
             The duty is proved once per class from the FOOTPRINT of the class on the steps of a run
             (`Fussabdruck`): a `lokal` step keeps the live set and deepens no frame, a `ruf` step keeps the
             live set and leaves every frame within the declared depth. A duty never quantifies over a free
             rule of the unit without that footprint: the earlier per-form statements did, and were refuted.
             * `klassenSchranken`: the duty from the footprint of the class of the instruction.
             * `schranken_lokal_einheit`: for the elaborated unit with declared bounds, a `lokal` instruction
               pays only its stack effect (`Befehl.Stapelwirkung 0`); the footprint follows from the rule.
             * `speicherverwaltungSchranken`: the same shape for space management, whose steps may allocate
               up to the memory ceiling and never deepen a frame.
             * `klassenSchranken_erfuellbar`: the premises hold jointly, with finite declared bounds.
-/
module

public import Core.Beobachtung.SchrankenB9B21
public import Core.Ast.Semantik.Runtime.Klasse.Klasse
public import Core.Ast.Semantik.Runtime.Mehrkontext.Kopf
public import Core.Ast.Semantik.Pflichten
public import Core.Ast.LowLevel.Mem.Meaning

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine Annahme Gabbro.Core.Ast

section Allgemein

variable {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type} [DecidableEq L]

/-- **The footprint of an instruction on the steps of a run**: `P` relates the state before and the
    state after every step the instruction takes at the head of a context. -/
def Fussabdruck (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι) (i : ι)
    (P : Zustand L Ort Wert Raum Lok Grund → Zustand L Ort Wert Raum Lok Grund → Prop) : Prop :=
  ∀ {η : I.Lauf E}, I.Laeufe E η → ∀ t c w spur vor nach,
    η.zeit.zustand t = vor → E.system.kopf vor c = some i →
    η.zeit.spur t = some (.kontext c w, spur) → η.zeit.zustand (t + 1) = nach →
    I.Schritt E.einrichtung E.system E.katalog η.hw t vor (.kontext c w, spur) nach → P vor nach

/-- **Space management keeps the bounds from its footprint**: no frame gets deeper, and under a declared
    memory ceiling the live set after the step fits it or lies within the live set before. An open ceiling
    admits every step. -/
theorem speicherverwaltungSchranken
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl LowLevel.MemInstruction)
    (op : LowLevel.MemInstruction)
    (fuss : Fussabdruck E op fun vor nach =>
      (∀ d, E.schranken.stapelTiefe (nach.lokal d) ≤ E.schranken.stapelTiefe (vor.lokal d)) ∧
        ∀ n, E.schranken.speicher = some n →
          (LebendeZellen nach).encard ≤ n ∨ LebendeZellen nach ⊆ LebendeZellen vor) :
    RegelSchranken E op := by
  intro η lauf t c w spur vor nach vorEq kopf spurEq nachEq step stapelVor speicherVor
  obtain ⟨tiefe, platz⟩ := fuss lauf t c w spur vor nach vorEq kopf spurEq nachEq step
  refine And.intro ?_ ?_
  · intro d n bound
    exact le_trans (tiefe d) (stapelVor d n bound)
  · intro n bound
    rcases platz n bound with fits | inside
    · exact fits
    · exact le_trans (Set.encard_le_encard inside) (speicherVor n bound)

end Allgemein

/-- The stack footprint of a class: a `lokal` step and a step of an access class (load, store, update,
    lock action, question) deepen no frame; a `ruf` step leaves every frame within the declared depth. -/
def klassenStapelFuss (E : Semantik.Einheit) (vor nach : Semantik.Zustand) :
    Semantik.Wirkungsklasse → Prop
  | .lokal | .lesen .. | .schreiben .. | .rmw .. | .zaun .. | .sperre .. | .frage | .verbrauche
  | .starte | .beende | .verbinde | .wechsle | .maskiere | .prioritaet | .sendeUnterbrechung
  | .leiteLeitung =>
    ∀ d, E.schranken.stapelTiefe (nach.lokal d) ≤ E.schranken.stapelTiefe (vor.lokal d)
  | .ruf => ∀ n, E.schranken.stapel = some n → ∀ d, E.schranken.stapelTiefe (nach.lokal d) ≤ n

/-- **The footprint of a class on the bounds**: both classes keep the live set within the one before the
    step; the stack part is the class's own. -/
def KlassenFuss (E : Semantik.Einheit) (k : Semantik.Wirkungsklasse) (vor nach : Semantik.Zustand) : Prop :=
  LebendeZellen nach ⊆ LebendeZellen vor ∧ klassenStapelFuss E vor nach k

/-- **The bound duty of an instruction from the footprint of its class.** -/
theorem klassenSchranken (E : Semantik.Einheit) (b : Semantik.Befehl)
    (fuss : Fussabdruck E b (KlassenFuss E b.klasse)) : RegelSchranken E b := by
  intro η lauf t c w spur vor nach vorEq kopf spurEq nachEq step stapelVor speicherVor
  obtain ⟨live, stack⟩ := fuss lauf t c w spur vor nach vorEq kopf spurEq nachEq step
  refine And.intro ?_ ?_
  · generalize b.klasse = k at stack
    cases k with
    | ruf =>
      intro d n bound
      exact stack n bound d
    | lokal | lesen _ | schreiben _ | rmw _ | zaun _ | sperre _ | frage | verbrauche | starte | beende
    | verbinde | wechsle | maskiere | prioritaet | sendeUnterbrechung | leiteLeitung =>
      intro d n bound
      exact le_trans (stack d) (stapelVor d n bound)
  · intro n bound
    exact le_trans (Set.encard_le_encard live) (speicherVor n bound)

/-- **A `lokal` instruction of the elaborated unit pays only its stack effect.** In the unit with the
    declared bounds `grenzen`, whose depth is the number of continuations of the frame, the duty holds for
    every instruction of class `lokal` whose frame step deepens nothing: the live set, and every other
    context's frame, are untouched by the rule. -/
theorem schranken_lokal_einheit (p : Semantik.Fragment) (platform : Plattform)
    (grenzen : Schrankendaten Nat Semantik.Rahmen)
    (tiefe : ∀ r, grenzen.stapelTiefe r = r.fortsetzungen.length) (b : Semantik.Befehl)
    (klasse : b.klasse = .lokal) (stapel : b.Stapelwirkung 0) :
    RegelSchranken { p.einheit platform with schranken := grenzen } b := by
  apply klassenSchranken
  intro η lauf t c w spur vor nach vorEq kopf spurEq nachEq step
  cases step with
  | kontext _ _ regel aus =>
    obtain ⟨i, kopfI, rule⟩ := regel
    have same : i = b := Option.some.inj (kopfI.symm.trans kopf)
    rw [same] at rule
    obtain ⟨_, nachBefehl⟩ := b.vollzug_genau (show b.impl c vor w [_] _ from rule) aus (Or.inl klasse)
    subst nachBefehl
    rw [klasse]
    refine And.intro (fun z hz => hz) ?_
    intro d
    change grenzen.stapelTiefe _ ≤ grenzen.stapelTiefe _
    rw [tiefe, tiefe]
    rcases eq_or_ne d c with hd | hd
    · rw [hd, Semantik.Befehl.nach_lokal_eigener]
      have fact := stapel (vor.lokal c) (Semantik.Zustand.regionLive vor)
      omega
    · rw [Semantik.Befehl.nach_lokal_anderer b hd]
      all_goals exact Nat.le_refl _

/-- With the frame fact of the classes (`KlassenStapelAussage`), every `lokal` instruction of the
    elaborated unit with declared bounds meets the duty. -/
theorem schranken_lokal_aus_klasse (p : Semantik.Fragment) (platform : Plattform)
    (grenzen : Schrankendaten Nat Semantik.Rahmen)
    (tiefe : ∀ r, grenzen.stapelTiefe r = r.fortsetzungen.length) (stapelKlasse : Semantik.KlassenStapelAussage)
    (b : Semantik.Befehl) (klasse : b.klasse = .lokal) :
    RegelSchranken { p.einheit platform with schranken := grenzen } b := by
  refine schranken_lokal_einheit p platform grenzen tiefe b klasse ?_
  have fact := stapelKlasse b
  rw [klasse] at fact
  exact fact

/-- **Satisfiability of the class duty.** In the elaborated unit of a one-instruction fragment with the
    finite stack bound `3` and the finite memory ceiling `5`, whose depth is the number of continuations,
    the load instruction `literal` is of class `lokal`, deepens nothing, and the duty holds. -/
theorem klassenSchranken_erfuellbar (platform : Plattform) :
    ∃ grenzen : Schrankendaten Nat Semantik.Rahmen,
      grenzen.stapel = some 3 ∧ grenzen.speicher = some 5 ∧
      (∀ r, grenzen.stapelTiefe r = r.fortsetzungen.length) ∧
      (Semantik.Befehl.literal 0 1).klasse = .lokal ∧
      (Semantik.Befehl.literal 0 1).Stapelwirkung 0 ∧
      RegelSchranken
        { (Semantik.Fragment.einzel (.literal 0 1)).einheit platform with schranken := grenzen }
        (Semantik.Befehl.literal 0 1) := by
  let grenzen : Schrankendaten Nat Semantik.Rahmen :=
    { Schrankendaten.leer with
      stapel := some 3, speicher := some 5, stapelTiefe := fun r => r.fortsetzungen.length }
  have stapel : (Semantik.Befehl.literal 0 1).Stapelwirkung 0 := fun _ _ => Nat.le_refl _
  exact ⟨grenzen, rfl, rfl, fun _ => rfl, rfl, stapel,
    schranken_lokal_einheit _ platform grenzen (fun _ => rfl) _ rfl stapel⟩

end Gabbro.Core.Beobachtung
