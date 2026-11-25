/-
  File:      Core/Beobachtung/SchrankenBeweise/Durchlauf.lean
  Subject:   PER-PASS COST MARKS (MK-12a, D-1): the duties, the composition, the checker line.

  `DurchlaufPrefix` (`Beobachtung.Schranken`) is the per-pass cost leg of `ImSchranken`:
  every open cost mark (`durchlaufstand`, block number with opening cut) visible in the
  acting context meets its declared ceiling (`durchlauf`) over the executed ticks only.
  This file carries the clock-independent duties for it (start, one per source form, the
  shared protocol part), their composition over the cuts, and the checker's per-pass line
  with its soundness. The per-form duties are discharged with the `per_pass`/`costs`
  elaboration (MK-19/MK-21); the class bound duty (`klassenSchranken`) is their Grundlage.

  Pinned in ONE collective statement (`durchlaufKostenAussage`, composition and checker
  soundness), with `durchlaufKosten_erfuellbar` (premises hold jointly) and
  `durchlaufKosten_nichtTrivial` (the model represents the violation and the checker
  refuses it) beside it.
-/
module

public import Core.Beobachtung.SchrankenB8
public import Core.Annahme.HostedLauf

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Annahme.Hosted

variable {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}

/-- The clock-independent start obligation: the initial cut of every admitted run satisfies
    the per-pass cost prefix. Open marks stay admitted. -/
def DurchlaufStartPflicht (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form) : Prop :=
  ∀ {h : Umgebung} {ρ : Lauf E}, Laeufe E h ρ → DurchlaufPrefix E ρ 0

/-- The per-form obligation: a step of form `f` preserves the per-pass cost prefix. The new
    cut's marks come from the step's target state and its cost windows end at the step's own
    tick, so the form's rule discharges this with the `per_pass`/`costs` elaboration. -/
def DurchlaufRegelPflicht (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (f : Form) : Prop :=
  ∀ {h : Umgebung} {ρ : Lauf E}, Laeufe E h ρ → ∀ t c w spur vor nach,
    DurchlaufPrefix E ρ t →
    ρ.zeit.zustand t = some vor → E.system.kopf vor c = some f →
    ρ.zeit.spur t = some (.kontext c w, spur) → ρ.zeit.zustand (t + 1) = some nach →
    DurchlaufPrefix E ρ (t + 1)

/-- The clock-independent protocol obligation: an answer, interrupt or crash transition
    preserves the per-pass cost prefix. Protocol ticks are foreign to every context. -/
def DurchlaufProtokollPflicht (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form) : Prop :=
  ∀ {h : Umgebung} {ρ : Lauf E}, Laeufe E h ρ → ∀ t w spur vor nach,
    DurchlaufPrefix E ρ t →
    ρ.zeit.zustand t = some vor →
    ρ.zeit.spur t = some (w, spur) → ProtokollB8Wahl w →
    ρ.zeit.zustand (t + 1) = nach →
    DurchlaufPrefix E ρ (t + 1)

/-- The clock-independent per-pass obligations of a unit: start, one per source form, and the
    shared protocol part. Discharged per form as the `per_pass`/`costs` elaboration lands,
    exactly as `KHPflichten` is for cost and hold. -/
structure DurchlaufPflichten (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form) : Prop where
  start : DurchlaufStartPflicht E
  regel : ∀ f, DurchlaufRegelPflicht E f
  protokoll : DurchlaufProtokollPflicht E

/-- A last tick whose mark is absent does not change the count. -/
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

/-- An idle tick preserves the per-pass cost prefix: the state is unchanged (same marks)
    and the cost windows end at the idle tick itself, whose contribution is zero. Older
    cuts carry over; the new cut's windows split into the old windows plus the idle tick. -/
private theorem durchlauf_leerlauf {ρ : Lauf E} {t : Nat}
    (idle : ρ.zeit.spur t = none) (hyp : DurchlaufPrefix E ρ t) :
    DurchlaufPrefix E ρ (t + 1) := by
  intro t' s _ zust c m hmem
  by_cases h : t' ≤ t
  · exact hyp t' s h zust c m hmem
  · have e : t' = t + 1 := by omega
    subst e
    have takt := ρ.zeit.takt t
    rw [idle] at takt
    cases takt with
    | schritt label _ => cases label
    | wartet _ gleich _ =>
      have zust_t : ρ.zeit.zustand t = some s := gleich ▸ zust
      by_cases hle : m.2 ≤ t
      · have e1 : t + 1 - m.2 = (t - m.2) + 1 := by omega
        have e2 : m.2 + (t - m.2) = t := by omega
        have kosten : Kontextkosten ρ c m.2 (t + 1 - m.2)
            = Kontextkosten ρ c m.2 (t - m.2) := by
          rw [e1, kontextkosten_fremd e2 (fun d w spur h => by rw [idle] at h; cases h)]
        rw [kosten]
        exact hyp t s (Nat.le_refl t) zust_t c m hmem
      · have e1 : t + 1 - m.2 = 0 := by omega
        rw [e1]
        simp only [Kontextkosten, I.zaehle]
        intro n _
        exact Nat.zero_le n

/-- Every prefix of an admitted run satisfies the per-pass cost obligations, by induction
    over the cuts. Idle ticks are generic; form steps use the per-form obligation, protocol
    steps the shared one. The mirror image of `prefix_alle_kh` for the per-pass leg. -/
private theorem durchlauf_prefix_alle (pflicht : DurchlaufPflichten E) {h : Umgebung} {ρ : Lauf E}
    (run : Laeufe E h ρ) (t : Nat) : DurchlaufPrefix E ρ t := by
  induction t with
  | zero => exact pflicht.start run
  | succ t ih =>
    cases tick : ρ.zeit.spur t with
    | none => exact durchlauf_leerlauf tick ih
    | some label =>
      rcases label with ⟨w, spur⟩
      cases w with
      | antwort _ =>
        have recorded := ρ.zeit.takt t
        rw [tick] at recorded
        generalize vorEq : ρ.zeit.zustand t = vor at recorded
        generalize nachEq : ρ.zeit.zustand (t + 1) = nach at recorded
        cases recorded with
        | wartet impossible _ _ => cases impossible
        | schritt mark transition =>
          cases mark
          cases transition with
          | schritt step =>
            cases step with
            | antwort _ => exact pflicht.protokoll run t _ _ _ _ ih vorEq tick trivial nachEq
      | interrupt _ =>
        have recorded := ρ.zeit.takt t
        rw [tick] at recorded
        generalize vorEq : ρ.zeit.zustand t = vor at recorded
        generalize nachEq : ρ.zeit.zustand (t + 1) = nach at recorded
        cases recorded with
        | wartet impossible _ _ => cases impossible
        | schritt mark transition =>
          cases mark
          cases transition with
          | schritt step =>
            cases step with
            | interrupt _ => exact pflicht.protokoll run t _ _ _ _ ih vorEq tick trivial nachEq
      | absturz =>
        have recorded := ρ.zeit.takt t
        rw [tick] at recorded
        generalize vorEq : ρ.zeit.zustand t = vor at recorded
        generalize nachEq : ρ.zeit.zustand (t + 1) = nach at recorded
        cases recorded with
        | wartet impossible _ _ => cases impossible
        | schritt mark transition =>
          cases mark
          cases transition with
          | schritt step =>
            cases step with
            | absturz _ => exact pflicht.protokoll run t _ _ _ _ ih vorEq tick trivial nachEq
      | kontext c w =>
        have recorded := ρ.zeit.takt t
        rw [tick] at recorded
        generalize vorEq : ρ.zeit.zustand t = vor at recorded
        generalize nachEq : ρ.zeit.zustand (t + 1) = nach at recorded
        cases recorded with
        | wartet impossible _ _ => cases impossible
        | schritt mark transition =>
          cases mark
          cases transition with
          | schritt step =>
            cases step with
            | kontext _ _ regel _ =>
              obtain ⟨f, kopf, _⟩ := regel
              exact pflicht.regel f run t c w spur _ _ ih vorEq kopf tick nachEq

/-- Every admitted run of a unit meeting its per-pass obligations holds the per-pass cost
    leg at every prefix: the composition theorem of the per-pass step. -/
theorem durchlauf_aus_pflichten (pflicht : DurchlaufPflichten E) {h : Umgebung} {ρ : Lauf E}
    (run : Laeufe E h ρ) (t : Nat) : DurchlaufPrefix E ρ t :=
  durchlauf_prefix_alle pflicht run t

/-- The checker's per-pass cost line: a declared ceiling admits the measured need; an open
    ceiling admits everything. This is the decidable fragment of the per-pass leg: both the
    bound and the need are closed natural numbers at check time. -/
def pruefeDurchlauf (grenze : Option Nat) (bedarf : Nat) : Bool :=
  match grenze with
  | none => true
  | some n => decide (bedarf ≤ n)

/-- SOUNDNESS of the checker's per-pass line: acceptance gives the bound. -/
theorem pruefeDurchlauf_korrekt (grenze : Option Nat) (bedarf : Nat) :
    pruefeDurchlauf grenze bedarf = true → UnterGrenze grenze bedarf := by
  intro h n eq
  subst eq
  simp only [pruefeDurchlauf] at h
  exact of_decide_eq_true h

/-- **Per-pass cost bounds, in one pinned statement** (MK-12a, D-1): with the per-pass
    obligations, every admitted run holds the per-pass cost prefix at every prefix; and
    the checker's per-pass line decides the bound in the decidable fragment. Feeds:
    `ImSchranken` (the per-pass leg), the `per_pass`/`costs` elaboration (MK-19/MK-21)
    discharging `DurchlaufPflichten` per form. Difficulty: mittel (this file proves the
    composition; the per-form duties are open). -/
def durchlaufKostenAussage : Prop :=
  (∀ (L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type) [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (pflicht : DurchlaufPflichten E) {h : Umgebung} {ρ : Lauf E},
    Laeufe E h ρ → ∀ t, DurchlaufPrefix E ρ t)
  ∧ (∀ (grenze : Option Nat) (bedarf : Nat),
    pruefeDurchlauf grenze bedarf = true → UnterGrenze grenze bedarf)

/-- The pinned per-pass statement holds: composition over the cuts, and the checker line
    is sound. -/
theorem durchlaufKosten : durchlaufKostenAussage := by
  constructor
  · intro L Ort Wert Raum Lok Grund Bedingung Wahl Form inst E pflicht h ρ run t
    exact durchlauf_aus_pflichten pflicht run t
  · intro grenze bedarf h
    exact pruefeDurchlauf_korrekt grenze bedarf h

/-- With open marks every prefix holds on every run: the hosted unit carries no per-pass
    declarations. -/
private theorem prefix_leer_all {ρ : Lauf einheit} (t : Nat) : DurchlaufPrefix einheit ρ t := by
  intro t' s _ zust c m hmem
  have leer : einheit.schranken.durchlaufstand (s.lokal c) = [] := rfl
  rw [leer] at hmem
  exact (List.not_mem_nil hmem).elim

/-- The hosted unit meets the per-pass obligations: with an empty mark stand every duty
    is vacuous. -/
private theorem pflichten_leer : DurchlaufPflichten einheit := by
  refine ⟨?_, ?_, ?_⟩
  · intro _ _ _
    exact prefix_leer_all 0
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    exact prefix_leer_all _
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _
    exact prefix_leer_all _

/-- The premises hold jointly: the hosted run with open marks satisfies the per-pass
    prefix at the initial cut. -/
theorem durchlaufKosten_erfuellbar :
    ∃ (E : Einheit Unit Unit Unit Unit (Option Handle) Unit Unit Unit Unit)
      (h : Umgebung) (ρ : Lauf E),
      Laeufe E h ρ ∧ DurchlaufPflichten E ∧ DurchlaufPrefix E ρ 0 := by
  obtain ⟨s, zul⟩ := zulStart_erfuellbar (erlaubt []) Sicherheit.Laufkonstruktion.bild_gueltig
  obtain ⟨ρ, _, _, lauf, _, _, _, _, _, _, _, _, _, _⟩ := konkreter_lauf zul []
  exact ⟨_, _, _, lauf, pflichten_leer, prefix_leer_all 0⟩

/-- The model represents the violation and the checker refuses it: ceiling zero against
    need one fails the line and falsifies the bound. With soundness this rules out the
    accept-everything checker; the line is not vacuous. -/
theorem durchlaufKosten_nichtTrivial :
    ∃ (grenze : Option Nat) (bedarf : Nat),
      pruefeDurchlauf grenze bedarf = false ∧ ¬ UnterGrenze grenze bedarf := by
  refine ⟨some 0, 1, by decide, ?_⟩
  intro h
  exact (by decide : ¬ 1 ≤ 0) (h 0 rfl)

end Gabbro.Core.Beobachtung
