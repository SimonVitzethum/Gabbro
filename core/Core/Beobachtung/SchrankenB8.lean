module

public import Core.Beobachtung.Schranken
public import Core.Maschine.Schritte

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine

variable {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}

/-- The cost leg of `ImSchranken` at one prefix: the occupied ticks so far meet the declared bound. -/
def KostenPrefix (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (ρ : Lauf E) (t : Nat) : Prop :=
  UnterGrenze E.schranken.kosten (Laufkosten ρ 0 t)

/-- The hold leg of `ImSchranken` at one prefix: every completed hold interval inside the prefix
    meets its bound. An interval that ends exactly at the prefix cut is included. -/
def HaltePrefix (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (ρ : Lauf E) (t : Nat) : Prop :=
  ∀ l c a n, a + n ≤ t →
    (∀ t', a ≤ t' → t' < a + n →
      ∃ s, ρ.zeit.zustand t' = some s ∧ (s.sperren l).besitzer = some c) →
    UnterGrenze (E.schranken.halten l) (Kontextkosten ρ c a n)

/-- The time leg of `ImSchranken` at one prefix: every mark visible at a cut inside the prefix
    meets its declaration there. -/
def ZeitPrefix (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (ρ : Lauf E) (t : Nat) : Prop :=
  ∀ t' s, t' ≤ t → ρ.zeit.zustand t' = some s →
    ∀ c m, m ∈ E.schranken.zeitstand (s.lokal c) →
      ∃ d, E.schranken.zeit m.block = some d ∧
        ZeitInSchranken (E.katalog.dauerMaximum d.zeile) d m.phase m.anfang t'
          (fun i => (ρ.hw.angebot i).cycles)
          (fun i => Kontextkosten ρ c i (t' + 1 - i))

/-- The B8 legs (hold bounds, cost, per-pass cost, time) of `ImSchranken` at one prefix.
    Stack (B9) and memory (B21) follow in later steps. -/
def B8Prefix (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (ρ : Lauf E) (t : Nat) : Prop :=
  KostenPrefix E ρ t ∧ HaltePrefix E ρ t ∧ ZeitPrefix E ρ t ∧ DurchlaufPrefix E ρ t

/-- The B8 conclusion: exactly the hold, cost, per-pass cost and time legs of `ImSchranken`.
    The stack and memory legs are separate obligations of the B9 and B21 steps. -/
def B8Abschluss (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (ρ : Lauf E) : Prop :=
  HalteSchranken E ρ ∧ (∀ t, KostenPrefix E ρ t) ∧ (∀ t, DurchlaufPrefix E ρ t) ∧
    ∀ t s, ρ.zeit.zustand t = some s →
      ∀ c m, m ∈ E.schranken.zeitstand (s.lokal c) →
        ∃ d, E.schranken.zeit m.block = some d ∧
          ZeitInSchranken (E.katalog.dauerMaximum d.zeile) d m.phase m.anfang t
            (fun i => (ρ.hw.angebot i).cycles)
            (fun i => Kontextkosten ρ c i (t + 1 - i))

/-- The clock-independent start obligation: the initial cut of every admitted run satisfies
    the cost and hold prefix. The time part is a separate obligation (`ZeitStartPflicht`):
    marks are loader data, and their evaluation needs the B19 clock bounds. -/
def KHStartPflicht (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form) : Prop :=
  ∀ {h : Umgebung} {ρ : Lauf E}, Laeufe E h ρ →
    KostenPrefix E ρ 0 ∧ HaltePrefix E ρ 0

/-- The clock-independent per-form obligation: a step of form `f` preserves the cost and hold
    prefix. Cost counting and hold accounting are machine-determined and need no clock facts;
    the step is identified by the head form and the recorded trace, exactly as in
    `RegelNIPflicht`. The time part is `ZeitRegelPflicht`. -/
def KHRegelPflicht (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (f : Form) : Prop :=
  ∀ {h : Umgebung} {ρ : Lauf E}, Laeufe E h ρ → ∀ t c w spur vor nach,
    KostenPrefix E ρ t → HaltePrefix E ρ t →
    ρ.zeit.zustand t = some vor → E.system.kopf vor c = some f →
    ρ.zeit.spur t = some (.kontext c w, spur) → ρ.zeit.zustand (t + 1) = some nach →
    KostenPrefix E ρ (t + 1) ∧ HaltePrefix E ρ (t + 1)

/-- Loader and non-form protocol transitions share one clock-independent obligation; an idle
    tick is handled generically by the composition theorem. -/
def ProtokollB8Wahl : SchrittWahl Wahl → Prop
  | .kontext _ _ => False
  | .antwort _ | .interrupt _ | .absturz => True

/-- The clock-independent protocol obligation: an answer, interrupt or crash transition
    preserves the cost and hold prefix. -/
def KHProtokollPflicht (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form) : Prop :=
  ∀ {h : Umgebung} {ρ : Lauf E}, Laeufe E h ρ → ∀ t w spur vor nach,
    KostenPrefix E ρ t → HaltePrefix E ρ t →
    ρ.zeit.zustand t = some vor →
    ρ.zeit.spur t = some (w, spur) → ProtokollB8Wahl w →
    ρ.zeit.zustand (t + 1) = some nach →
    KostenPrefix E ρ (t + 1) ∧ HaltePrefix E ρ (t + 1)

/-- The clock-independent B8 obligations of a unit: start, one per source form, and the shared
    protocol part. Discharged per form as the M6 rules land, exactly as `NIPflichten` is for NI. -/
structure KHPflichten (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form) : Prop where
  start : KHStartPflicht E
  regel : ∀ f, KHRegelPflicht E f
  protokoll : KHProtokollPflicht E

/-- The time start obligation: the initial cut of every admitted run satisfies the time prefix.
    Discharged with the loader rules (M6) and the B19 clock bounds. -/
def ZeitStartPflicht (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form) : Prop :=
  ∀ {h : Umgebung} {ρ : Lauf E}, Laeufe E h ρ → ZeitPrefix E ρ 0

/-- The per-form time obligation: a step of form `f` preserves the time prefix. Discharged
    per form with the rule content (new marks, local state), the `zeit...ErweiternAussage`
    extension lemmas for decided marks, and the B19 clock bounds for running `rumpf` marks. -/
def ZeitRegelPflicht (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (f : Form) : Prop :=
  ∀ {h : Umgebung} {ρ : Lauf E}, Laeufe E h ρ → ∀ t c w spur vor nach,
    ZeitPrefix E ρ t →
    ρ.zeit.zustand t = some vor → E.system.kopf vor c = some f →
    ρ.zeit.spur t = some (.kontext c w, spur) → ρ.zeit.zustand (t + 1) = some nach →
    ZeitPrefix E ρ (t + 1)

/-- The protocol time obligation: an answer, interrupt or crash transition preserves the time
    prefix. Discharged with the B19 clock bounds. -/
def ZeitProtokollPflicht (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form) : Prop :=
  ∀ {h : Umgebung} {ρ : Lauf E}, Laeufe E h ρ → ∀ t w spur vor nach,
    ZeitPrefix E ρ t →
    ρ.zeit.zustand t = some vor →
    ρ.zeit.spur t = some (w, spur) → ProtokollB8Wahl w →
    ρ.zeit.zustand (t + 1) = some nach →
    ZeitPrefix E ρ (t + 1)

/-- The time obligations of a unit. The composition over cuts closes with the B19 clock
    bounds; the extension lemmas for decided phases are pinned as `...Aussage` now. -/
structure ZeitPflichten (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form) : Prop where
  start : ZeitStartPflicht E
  regel : ∀ f, ZeitRegelPflicht E f
  protokoll : ZeitProtokollPflicht E

/-- The B8 obligations of a unit: the clock-independent cost and hold part, closed by the
    composition theorem of this step, and the time part, closed with the B19 clock bounds. -/
structure B8Pflichten (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form) : Prop where
  kh : KHPflichten E
  zeit : ZeitPflichten E

/-- A marked tick is dropped from the count when its mark is absent. -/
private theorem zaehle_still {markiert : Nat → Bool} {anfang k : Nat}
    (still : markiert (anfang + k) = false) :
    I.zaehle markiert anfang (k + 1) = I.zaehle markiert anfang k := by
  simp only [I.zaehle, still, Bool.false_eq_true, if_false, Nat.add_zero]

/-- An idle tick adds no abstract cost. -/
private theorem laufkosten_leerlauf {ρ : Lauf E} {t : Nat}
    (idle : ρ.zeit.spur t = none) :
    Laufkosten ρ 0 (t + 1) = Laufkosten ρ 0 t := by
  simp only [Laufkosten, I.zaehle, Nat.zero_add, idle, Option.isSome_none,
    Bool.false_eq_true, ite_false, Nat.add_zero]

/-- A tick that is not a context step of `c` adds nothing to the context cost of `c`. -/
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

/-- An idle tick preserves the cost and hold prefix: the state is unchanged and neither
    cost counter moves. The time prefix is not preserved here: the hardware clock may advance
    on an idle tick, so running `rumpf` marks need the B19 clock bounds (`ZeitPflichten`). -/
private theorem leerlauf_erhaelt_kh {ρ : Lauf E} {t : Nat}
    (idle : ρ.zeit.spur t = none) (hyp : KostenPrefix E ρ t ∧ HaltePrefix E ρ t) :
    KostenPrefix E ρ (t + 1) ∧ HaltePrefix E ρ (t + 1) := by
  obtain ⟨kosten, halte⟩ := hyp
  have fremd : ∀ (c : Kontext) d w spur,
      ρ.zeit.spur t = some (.kontext d w, spur) → d ≠ c := by
    intro c d w spur h
    rw [idle] at h
    cases h
  refine ⟨?_, ?_⟩
  · unfold KostenPrefix
    rw [laufkosten_leerlauf idle]
    exact kosten
  · intro l c a n bound own
    by_cases h : a + n ≤ t
    · exact halte l c a n h own
    · cases n with
      | zero =>
        intro lim _
        simp only [Kontextkosten, I.zaehle]
        exact Nat.zero_le lim
      | succ k =>
        have ak_le : a + k ≤ t := by
          have b1 : Nat.succ (a + k) ≤ t + 1 := by
            rw [← Nat.add_succ]
            exact bound
          have b2 : Nat.succ (a + k) ≤ Nat.succ t := by
            rwa [← Nat.succ_eq_add_one] at b1
          exact Nat.le_of_succ_le_succ b2
        have ak_ge : t ≤ a + k := by
          have h1 : ¬ Nat.succ (a + k) ≤ t := by
            rw [← Nat.add_succ]
            exact h
          exact Nat.le_of_lt_succ (lt_of_not_ge h1)
        have ak : a + k = t := Nat.le_antisymm ak_le ak_ge
        have own' : ∀ t', a ≤ t' → t' < a + k →
            ∃ s, ρ.zeit.zustand t' = some s ∧ (s.sperren l).besitzer = some c := by
          intro t' h1 h2
          exact own t' h1 (Nat.lt_of_lt_of_le h2 (Nat.add_le_add_left (Nat.le_succ k) a))
        have zb := halte l c a k (le_of_eq ak) own'
        rw [kontextkosten_fremd ak (fremd c)]
        exact zb

/-- Every prefix of an admitted run satisfies the cost and hold obligations, by induction
    over the cuts. Idle ticks are generic; form steps use the per-form obligation, protocol
    steps the shared one. The time prefix needs the B19 clock bounds and is composed in the
    `ZeitPflichten` step. -/
private theorem prefix_alle_kh (pflicht : KHPflichten E) {h : Umgebung} {ρ : Lauf E}
    (run : Laeufe E h ρ) (t : Nat) : KostenPrefix E ρ t ∧ HaltePrefix E ρ t := by
  induction t with
  | zero => exact pflicht.start run
  | succ t ih =>
    cases tick : ρ.zeit.spur t with
    | none => exact leerlauf_erhaelt_kh tick ih
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
            | antwort _ => exact pflicht.protokoll run t _ _ _ _ ih.1 ih.2 vorEq tick trivial nachEq
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
            | interrupt _ => exact pflicht.protokoll run t _ _ _ _ ih.1 ih.2 vorEq tick trivial nachEq
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
            | absturz _ => exact pflicht.protokoll run t _ _ _ _ ih.1 ih.2 vorEq tick trivial nachEq
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
              exact pflicht.regel f run t c w spur _ _ ih.1 ih.2 vorEq kopf tick nachEq

/-- Every admitted run of a unit meeting its clock-independent obligations meets the hold and
    cost legs of `ImSchranken`: the hold leg from the prefix at the interval end, the cost leg
    directly. This is the composition theorem of the B8 step; the time leg closes with the B19
    clock bounds over `ZeitPflichten`. -/
theorem b8_kh_aus_pflichten (pflicht : KHPflichten E) {h : Umgebung} {ρ : Lauf E}
    (run : Laeufe E h ρ) : HalteSchranken E ρ ∧ ∀ t, KostenPrefix E ρ t := by
  have alle := prefix_alle_kh pflicht run
  refine ⟨?_, fun t => (alle t).1⟩
  intro l c a n own
  exact (alle (a + n)).2 l c a n (Nat.le_refl _) own

/-- The B8 conclusion is exactly the hold, cost, per-pass cost and time legs of
    `ImSchranken`; the remaining two legs are the stack (B9) and memory (B21) obligations
    of the later steps. -/
theorem b8_abschluss_imSchranken {ρ : Lauf E} :
    B8Abschluss E ρ ∧
      (∀ t s, ρ.zeit.zustand t = some s →
        ∀ n, E.schranken.speicher = some n → (LebendeZellen s).encard ≤ n) ∧
      (∀ t s, ρ.zeit.zustand t = some s →
        ∀ c, UnterGrenze E.schranken.stapel (E.schranken.stapelTiefe (s.lokal c))) ↔
    ImSchranken E ρ := by
  simp only [B8Abschluss, ImSchranken, KostenPrefix]
  constructor
  · rintro ⟨⟨halte, kosten, durchlauf, zeit⟩, speicher, stapel⟩
    exact ⟨halte, kosten, durchlauf, fun t s h => ⟨speicher t s h, stapel t s h, zeit t s h⟩⟩
  · rintro ⟨halte, kosten, durchlauf, rest⟩
    exact ⟨⟨halte, kosten, durchlauf, fun t s h => (rest t s h).2.2⟩,
      fun t s h => (rest t s h).1, fun t s h => (rest t s h).2.1⟩

end Gabbro.Core.Beobachtung
