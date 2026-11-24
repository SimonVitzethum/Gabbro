module

public import Core.Maschine.Start

@[expose] public section

namespace Gabbro.Core.Maschine.I

open Gabbro.Core.Katalog

variable {L Ort Wert Raum Lok Grund Bedingung Wahl F : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F}

/-- Count the marked ticks of an interval with a given start and length. -/
def zaehle (markiert : Nat → Bool) (anfang : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => zaehle markiert anfang n + if markiert (anfang + n) then 1 else 0

/-- The checked length bounds all private steps of a context while the same
    source unit remains at its head and neither completes nor is reset by a crash.
    The count uses the concrete context recorded at each occupied tick. -/
def StotterSchranke (laenge : F → Nat) (η : Lauf E) : Prop :=
  ∀ c f a n, (∀ t, a ≤ t → t < a + n →
    E.system.kopf (η.zeit.zustand t) c = some f ∧
    (∀ w spur, η.zeit.spur t ≠ some (.kontext c w, spur)) ∧
    η.zeit.spur t ≠ some (.absturz, absturzSpur)) →
    zaehle (fun t => decide (η.belegt t = some c)) a n ≤ laenge f

theorem StotterSchranke.ohne_stottern {laenge : F → Nat} {η : Lauf E}
    (frei : ∀ t, η.belegt t = none) : StotterSchranke laenge η := by
  intro c f a n interval
  clear interval
  have count : zaehle (fun t => decide (η.belegt t = some c)) a n = 0 := by
    induction n with
    | zero => rfl
    | succ n ih =>
      have empty : decide (η.belegt (a + n) = some c) = false :=
        decide_eq_false (fun h => Option.some_ne_none c (h.symm.trans (frei _)))
      simp only [zaehle, ih, empty, Bool.false_eq_true, if_false, Nat.add_zero]
  rw [count]
  exact Nat.zero_le _

omit [DecidableEq L] in
private theorem markierungen_endlich (m : Nat → Bool) (a b : Nat)
    (bound : ∀ n, zaehle m a n ≤ b) : ∃ q, ∀ t, q ≤ t → m t = false := by
  classical
  let P (d : Nat) := ∃ n, zaehle m a n + d = b
  have p : ∃ d, P d := ⟨b, 0, Nat.zero_add _⟩
  obtain ⟨n, maxCount⟩ := Nat.find_spec p
  have stable (k : Nat) : zaehle m a (n + k) = zaehle m a n ∧ m (a + (n + k)) = false := by
    have quiet (j : Nat) (same : zaehle m a j = zaehle m a n) : m (a + j) = false := by
      cases marked : m (a + j) with
      | false => rfl
      | true =>
        have addOne : zaehle m a (j + 1) = zaehle m a n + 1 := by
          simp only [zaehle, same, marked, if_true]
        have h := bound (j + 1)
        rw [addOne] at h
        have less : Nat.find p - 1 < Nat.find p := by omega
        have better : P (Nat.find p - 1) := ⟨j + 1, by rw [addOne]; omega⟩
        exact (Nat.not_lt_of_ge (Nat.find_min' p better) less).elim
    induction k with
    | zero => exact ⟨rfl, quiet n rfl⟩
    | succ k ih =>
      have same : zaehle m a (n + (k + 1)) = zaehle m a n := by
        change zaehle m a (n + k) + (if m (a + (n + k)) then 1 else 0) = zaehle m a n
        simp only [ih.1, ih.2, Bool.false_eq_true, if_false, Nat.add_zero]
      exact ⟨same, quiet _ same⟩
  refine ⟨a + n, fun t le => ?_⟩
  have h := (stable (t - (a + n))).2
  rwa [← Nat.add_assoc, Nat.add_sub_of_le le] at h

omit [DecidableEq L] in
private theorem endlich_viele (P : Nat → Nat → Prop) (n : Nat)
    (einzeln : ∀ k, k < n → ∃ q, ∀ t, q ≤ t → P k t) :
    ∃ q, ∀ k, k < n → ∀ t, q ≤ t → P k t := by
  induction n with
  | zero => exact ⟨0, fun _ lt => (Nat.not_lt_zero _ lt).elim⟩
  | succ n ih =>
    obtain ⟨q, alt⟩ := ih (fun k lt => einzeln k (Nat.lt_succ_of_lt lt))
    obtain ⟨r, neu⟩ := einzeln n (Nat.lt_succ_self _)
    refine ⟨max q r, fun k lt t after => ?_⟩
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ lt) with before | rfl
    · exact alt k before t ((Nat.le_max_left _ _).trans after)
    · exact neu t ((Nat.le_max_right _ _).trans after)

/-- On an ideal pause suffix the dispatch map is fixed. There are finitely many
    offered cores, and each dispatched context can occupy only finitely many
    of their ticks, by its own unit bound. -/
theorem StotterSchranke.endet {laenge : F → Nat} {η : Lauf E}
    (bound : StotterSchranke laenge η) (valid : η.hw.konform E.katalog η.umgebung)
    (privat : ∀ t c, η.belegt t = some c →
      KannSchreiten η.hw t c (η.zeit.zustand t) ∧ ∃ f, E.system.kopf (η.zeit.zustand t) c = some f)
    {a : Nat} (quiet : ∀ t, a ≤ t → η.zeit.spur t = none) :
    ∃ q, a ≤ q ∧ ∀ t, q ≤ t → η.belegt t = none := by
  have still (t : Nat) (ge : a ≤ t) : η.zeit.zustand t = η.zeit.zustand a := by
    induction t, ge using Nat.le_induction with
    | base => rfl
    | succ t ge ih => exact (η.zeit.wartet (quiet t ge)).1.trans ih
  have contextEnds (c : Kontext) : ∃ q, a ≤ q ∧ ∀ t, q ≤ t → η.belegt t ≠ some c := by
    cases head : E.system.kopf (η.zeit.zustand a) c with
    | none =>
      refine ⟨a, Nat.le_refl _, fun t after mark => ?_⟩
      obtain ⟨f, form⟩ := (privat t c mark).2
      rw [still t after, head] at form
      cases form
    | some f =>
      obtain ⟨q, tail⟩ := markierungen_endlich (fun t => decide (η.belegt t = some c)) a (laenge f)
        (fun n => bound c f a n (fun t after _ => by
          rw [still t after, quiet t after]
          exact ⟨head, fun _ _ h => Option.some_ne_none _ h.symm, fun h => Option.some_ne_none _ h.symm⟩))
      exact ⟨max a q, Nat.le_max_left _ _, fun t after mark => by
        have empty := tail t ((Nat.le_max_right _ _).trans after)
        simp only [mark, decide_true] at empty
        cases empty⟩
  obtain ⟨q, tail⟩ := endlich_viele
    (fun k t => ∀ c, ((η.zeit.zustand a).kerne k).laeuft = some c → η.belegt t ≠ some c)
    η.umgebung.kernzahl (fun k _ => by
      cases dispatch : ((η.zeit.zustand a).kerne k).laeuft with
      | none => exact ⟨a, fun _ _ _ h => nomatch h⟩
      | some c =>
        obtain ⟨q, _, ends⟩ := contextEnds c
        exact ⟨q, fun t after d eq => Option.some.inj eq ▸ ends t after⟩)
  refine ⟨max a q, Nat.le_max_left _ _, fun t after => ?_⟩
  cases mark : η.belegt t with
  | none => rfl
  | some c =>
    obtain ⟨k, slot, dispatch, _⟩ := (privat t c mark).1
    rw [still t ((Nat.le_max_left _ _).trans after)] at dispatch
    exact (tail k ((valid.2 t).1 k slot) t ((Nat.le_max_right _ _).trans after) c dispatch mark).elim

end Gabbro.Core.Maschine.I
