/-
  File:      core/Core/Beobachtung/SchrankenBeweise/KostenEndlichBeweise.lean
  Subject:   THE PROOFS OF THE FINITE-BOUND CORE STATEMENTS. `GebundenKHEndlichAussage`
               closes from estimator correctness plus the finite checker line; the
               window and segment costs come from `KostenSchaetzerKorrektAussage` over
               admitted runs, the prefixes by context-cost monotonicity.

  The first half is unconditional over the checker outcomes: an open ceiling makes every
  `UnterGrenze` vacuous, and a finite ceiling gives `E ≤ K` from `pruefeSchrankenEndlich`
  and the window and segment costs from estimator correctness. The context-cost monotonicity
  used for a window prefix is proved from `I.zaehle`'s split equation, not assumed.

  Estimator correctness itself is NOT proved here: it follows from the open step
  correspondence (`KostenSchrittKorrespondenzAussage`, one induction over the window
  from its start cut), which Hy4 discharges. The old prefix-from-zero shape over
  arbitrary `Lauf` is gone by design: `Zeitlauf.existiert` admits every initial state,
  and every platform catalogue carries `.persistence`, so a run that restarts the entry
  context after a crash accumulates more than one invocation while `E` bounds one.
  `kontextkosten_segmente` and `ohneFensterung_akkumuliert` below record exactly that:
  the unwindowed prefix is the sum over crash-separated segments, so two full segments
  already break any positive bound. Windowing is load-bearing, not a reformulation.
-/
module

public import Core.Beobachtung.SchrankenBeweise.KostenEndlich
public import Core.Beobachtung.SchrankenBeweise.SchrankenSpielraum

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine Annahme
open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

variable {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}

/-- The marked-tick count splits over adjacent intervals. -/
private theorem zaehle_teil (markiert : Nat → Bool) (a m n : Nat) :
    I.zaehle markiert a (m + n) = I.zaehle markiert a m + I.zaehle markiert (a + m) n := by
  induction n with
  | zero => simp only [Nat.add_zero, I.zaehle]
  | succ n ih =>
    have h1 : m + (n + 1) = (m + n) + 1 := (Nat.add_assoc m n 1).symm
    have h2 : a + (m + n) = (a + m) + n := (Nat.add_assoc a m n).symm
    rw [h1]
    simp only [I.zaehle]
    rw [h2, ih]
    omega

/-- A longer interval costs a context at least as much: the tail count is nonnegative. -/
private theorem kontextkosten_mono (ρ : Lauf E) (c : Kontext) (a m n : Nat)
    (h : m ≤ n) : Kontextkosten ρ c a m ≤ Kontextkosten ρ c a n := by
  have hn : n = m + (n - m) := (Nat.add_sub_of_le h).symm
  rw [hn]
  simp only [Kontextkosten]
  rw [zaehle_teil]
  exact Nat.le_add_right _ _

/-- An open ceiling imposes no duty. -/
private theorem unterGrenze_none (bedarf : Nat) : UnterGrenze none bedarf := by
  intro n h
  cases h

/-- The open leg of the endliche line opens the hold list. -/
private theorem endlich_offen (u : UnitMitSchranken) (tab : KostenTabelle)
    (z : Wirkungsklasse → KlassenKostenzeile)
    (hk : u.deklaration.kosten = none)
    (ok : pruefeSchrankenEndlich u tab z = true) :
    u.deklaration.halten = [] := by
  simp only [pruefeSchrankenEndlich, hk, pruefeSchrankenSpielraum,
    Option.isNone_none, Bool.true_and] at ok
  cases hh : u.deklaration.halten with
  | nil => rfl
  | cons x xs =>
    rw [hh, List.isEmpty_cons] at ok
    cases ok

/-- The finite leg of the endliche line opens the hold list and extracts the estimator
    value with the declared ceiling above it. -/
private theorem endlich_finite (u : UnitMitSchranken) (tab : KostenTabelle)
    (z : Wirkungsklasse → KlassenKostenzeile) (K : Nat)
    (hk : u.deklaration.kosten = some K)
    (ok : pruefeSchrankenEndlich u tab z = true) :
    u.deklaration.halten = [] ∧
      ∃ E, schaetzeEinheit z tab u.baum = some E ∧ E ≤ K := by
  rw [pruefeSchrankenEndlich, hk] at ok
  have handes := Bool.and_eq_true_iff.mp ok
  have hhalten : u.deklaration.halten = [] := by
    cases hh : u.deklaration.halten with
    | nil => rfl
    | cons x xs =>
      rw [hh, List.isEmpty_cons] at handes
      cases handes.1
  refine ⟨hhalten, ?_⟩
  cases hE : schaetzeEinheit z tab u.baum with
  | none =>
    simp only [hE] at handes
    cases handes.2
  | some e =>
    simp only [hE] at handes
    exact ⟨e, rfl, decide_eq_true_eq.mp handes.2⟩

/-- The declared hold lookup of a bound unit is open when the declaration lists no hold. -/
private theorem halten_none (P : Katalog.Plattform) (u : UnitMitSchranken) (l : Nat)
    (hhalten : u.deklaration.halten = []) :
    (einheitMitSchranken P u).schranken.halten l = none := by
  rw [einheitMitSchranken_halten]
  simp only [Schrankendeklaration.haltenVon, hhalten, List.find?_nil, Option.map_none]

/-- The context cost splits over adjacent intervals: the unwindowed prefix is the sum
    over its segments. A crash that restarts the entry context therefore extends the
    old count instead of opening a new one — unless windows cut at the crash. -/
theorem kontextkosten_segmente (ρ : Lauf E) (c : Kontext) (a m n : Nat) :
    Kontextkosten ρ c a (m + n) =
      Kontextkosten ρ c a m + Kontextkosten ρ c (a + m) n := by
  simp only [Kontextkosten]
  exact zaehle_teil _ _ _ _

/-- **Without windowing the bound is false in general**: two full segments — for
    instance two crash-separated invocations each costing the whole bound — already
    exceed any positive bound on the unwindowed prefix. This is the old k-restart
    counterexample (k = 2); the windowed statement bounds each segment alone. -/
theorem ohneFensterung_akkumuliert (ρ : Lauf E) (c : Kontext) (a m n Ebound : Nat)
    (h1 : Kontextkosten ρ c a m = Ebound)
    (h2 : Kontextkosten ρ c (a + m) n = Ebound)
    (hE : 0 < Ebound) :
    ¬ Kontextkosten ρ c a (m + n) ≤ Ebound := by
  rw [kontextkosten_segmente, h1, h2]
  omega

/-- **The finite cost and hold duties from estimator correctness.** An open ceiling is
    vacuous; a finite ceiling closes its cost legs by `E ≤ K` and the window monotonicity,
    and its hold legs by the empty hold list. -/
theorem gebundenKHEndlich_ausKorrekt
    (hKorrekt : KostenSchaetzerKorrektAussage) :
    GebundenKHEndlichAussage := by
  intro P u tab z akk h ρ run
  have ok := akk.2
  cases hk : u.deklaration.kosten with
  | none =>
    have hhalten := endlich_offen u tab z hk ok
    have hkost : (einheitMitSchranken P u).schranken.kosten = none := by
      rw [einheitMitSchranken_kosten, hk]
    constructor
    · intro c f a b fenster t _ _
      constructor
      · rw [hkost]
        exact unterGrenze_none _
      · intro l a' n _ _ _
        rw [halten_none P u l hhalten]
        exact unterGrenze_none _
    · intro a b seg t _ _
      constructor
      · rw [hkost]
        exact unterGrenze_none _
      · intro l a' n _ _ _
        rw [halten_none P u l hhalten]
        exact unterGrenze_none _
  | some K =>
    obtain ⟨hhalten, E, hE, hEK⟩ := endlich_finite u tab z K hk ok
    have korrekt := hKorrekt P u tab z E akk hE run
    have hkost : (einheitMitSchranken P u).schranken.kosten = some K := by
      rw [einheitMitSchranken_kosten, hk]
    constructor
    · intro c f a b fenster t _ _
      constructor
      · intro n hn
        have hnK : K = n := Option.some.inj (by simpa only [hkost] using hn)
        subst n
        have hfull : Kontextkosten ρ c a (b - a) ≤ E := korrekt.1 c f a b fenster
        have htlen : t - a ≤ b - a := by omega
        have hmono : Kontextkosten ρ c a (t - a) ≤ Kontextkosten ρ c a (b - a) :=
          kontextkosten_mono ρ c a (t - a) (b - a) htlen
        exact le_trans hmono (le_trans hfull hEK)
      · intro l a' n _ _ _
        rw [halten_none P u l hhalten]
        exact unterGrenze_none _
    · intro a b seg t _ _
      constructor
      · intro n hn
        have hnK : K = n := Option.some.inj (by simpa only [hkost] using hn)
        subst n
        have hfull : Kontextkosten ρ eintritt a (b - a) ≤ E := korrekt.2 a b seg
        have htlen : t - a ≤ b - a := by omega
        have hmono : Kontextkosten ρ eintritt a (t - a) ≤
            Kontextkosten ρ eintritt a (b - a) :=
          kontextkosten_mono ρ eintritt a (t - a) (b - a) htlen
        exact le_trans hmono (le_trans hfull hEK)
      · intro l a' n _ _ _
        rw [halten_none P u l hhalten]
        exact unterGrenze_none _

end Gabbro.Core.Beobachtung
