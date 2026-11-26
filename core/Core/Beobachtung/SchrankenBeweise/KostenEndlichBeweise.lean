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

  Estimator correctness remains a premise. The measured-entry example in
  `Kosten.KostenGegenbeispiel` refutes it for the current estimator.
  The old prefix-from-zero shape over
  arbitrary `Lauf` is gone by design: `Zeitlauf.existiert` admits every initial state,
  and every platform catalogue carries `.persistence`, so a run that restarts the entry
  context after a crash accumulates more than one invocation while `E` bounds one.
  `kontextkosten_segmente` and `ohneFensterung_akkumuliert` below record exactly that:
  the unwindowed prefix is the sum over crash-separated segments, so two full segments
  already break any positive bound. Windowing is load-bearing, not a reformulation.
-/
module

public import Core.Beobachtung.SchrankenBeweise.KostenEndlich
public import Core.Beobachtung.SchrankenBeweise.Kosten.KostenLauf
public import Core.Beobachtung.SchrankenBeweise.SchrankenSpielraum
public import Core.Ast.Semantik.Runtime.Mehrkontext.System

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine Annahme
open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- The code-membership leg holds for every head of the elaborated unit. -/
theorem kostenKopf_mem (P : Katalog.Plattform) (u : UnitMitSchranken)
    {s : Zustand} {c : Kontext} {b : Befehl}
    (head : (einheitMitSchranken P u).system.kopf s c = some b) :
    b ∈ (programm u.baum).code :=
  kopf_mem head

/-- The while setup's counter at its test address is bounded by the source type. -/
theorem whilePasszahl_le {lo hi : Int} (bound : Expr scope (.int lo hi))
    (value : Zahl lo hi) (r : Rahmen) (src distance : Nat)
    (read : r.zahl src = some (⟨lo, hi, value⟩ : Ganzzahl)) :
    ∃ n, n ≤ boundSchranke bound ∧
      ((Befehl.setzePasszahl src distance).auswerten r).zaehler (r.pc + distance) = some n := by
  refine ⟨value.wert.toNat, ?_, ?_⟩
  · exact Int.toNat_le_toNat value.oben
  · simp only [Befehl.auswerten, read, Function.update_self]

/-- A successful range setup installs a counter and upper value within the source bounds. -/
theorem forEinrichtung_inGrenzen {low lowHi highLo high : Int}
    (lo : Expr scope (.int low lowHi)) (hi : Expr scope (.int highLo high))
    (start : Zahl low lowHi) (stop : Zahl highLo high)
    (r : Rahmen) (lower upper skip : Nat) (index : Ty .value) (shadowed missing : Bool)
    (readLower : r.zahl lower = some (⟨low, lowHi, start⟩ : Ganzzahl))
    (readUpper : r.zahl upper = some (⟨highLo, high, stop⟩ : Ganzzahl))
    (nonempty : start.wert < stop.wert)
    (allowed : (shadowed || (missing && decide (start.wert < stop.wert))) = false)
    (initial : Dynamisch) (fits : wertIn index (Ganzzahl.pack ⟨low, lowHi, start⟩) = some initial) :
    let next := (Befehl.forAnfang lower upper index skip shadowed missing).auswerten r
    ∃ n b, next.zaehler (r.pc + 1) = some n ∧ n ≤ forSchranke lo hi ∧
      next.obergrenzen (r.pc + 1) = some b ∧ b.zahl.wert ≤ high := by
  have ordered : ¬ stop.wert ≤ start.wert := Int.not_le.mpr nonempty
  refine ⟨(stop.wert - start.wert).toNat, ⟨highLo, high, stop⟩, ?_, ?_, ?_, stop.oben⟩
  · simp only [Befehl.auswerten, Id.run, readLower, readUpper, allowed, Bool.false_eq_true,
      if_false, ordered, fits, Function.update_self]
    exact Function.update_self _ _ _
  · exact Int.toNat_le_toNat (Int.sub_le_sub stop.oben start.unten)
  · simp only [Befehl.auswerten, Id.run, readLower, readUpper, allowed, Bool.false_eq_true,
      if_false, ordered, fits, Function.update_self]
    exact Function.update_self _ _ _

/-- Converting a nonnegative measure to the runtime representation preserves both endpoints. -/
theorem masswert_imIntervall {lo hi : Int} (value : Zahl lo hi) (nonneg : 0 ≤ lo) :
    lo ≤ (value.wert.toNat : Int) ∧ (value.wert.toNat : Int) ≤ hi := by
  rw [Int.toNat_of_nonneg (Int.le_trans nonneg value.unten)]
  exact ⟨value.unten, value.oben⟩

/-- A changed measure after `pruefeMass` is the value from its typed operand. -/
theorem neuesMass_imIntervall {lo hi : Int} (value : Zahl lo hi) (nonneg : 0 ≤ lo)
    (r : Rahmen) (slot n : Nat)
    (read : r.zahl slot = some (⟨lo, hi, value⟩ : Ganzzahl))
    (installed : ((Befehl.pruefeMass slot).auswerten r).mass = some n)
    (changed : r.mass ≠ some n) :
    lo ≤ (n : Int) ∧ (n : Int) ≤ hi := by
  have effect : ((Befehl.pruefeMass slot).auswerten r).mass = r.mass ∨
      ((Befehl.pruefeMass slot).auswerten r).mass = some value.wert.toNat := by
    simp only [Befehl.auswerten, Rahmen.setzeMass, Id.run, read]
    repeat' first | exact Or.inl rfl | exact Or.inr rfl | split
  rcases effect with unchanged | stored
  · exact (changed (unchanged.symm.trans installed)).elim
  · cases Option.some.inj (installed.symm.trans stored)
    exact masswert_imIntervall value nonneg

variable {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}

/-- Static bounds attached to a unit's loop tests and function declarations. -/
def kostenGrenzen (u : Ast.Unit) : KostenGrenzen where
  zaehler pc n := ∃ bound, (pc, bound) ∈ (programm u).schleifen ∧ n ≤ bound.paesse
  zaehlerKleiner := by
    rintro pc n m smaller ⟨bound, present, bounded⟩
    exact ⟨bound, present, smaller.trans bounded⟩
  obergrenze pc b := ∃ bound hi, (pc, bound) ∈ (programm u).schleifen ∧
    bound.oben = some hi ∧ b.zahl.wert ≤ hi
  mass name n := ∀ id kern lo hi, name = some id → findeKern u.2 id = some kern →
    kern.massIntervall = some (lo, hi) → lo ≤ (n : Int) ∧ (n : Int) ≤ hi

/-- The source-specific obligations at cost writes. Operand types are related to
    the exact destination test address or to the current function declaration. -/
def KostenEinrichtung (u : Ast.Unit) (b : Befehl) (r : Rahmen) : Prop :=
  match b with
  | .setzePasszahl src distance =>
    ∀ a, r.zahl src = some a → (kostenGrenzen u).zaehler (r.pc + distance) a.hi.toNat
  | .forAnfang lower upper _ _ _ _ =>
    ∀ a b, r.zahl lower = some a → r.zahl upper = some b → a.zahl.wert < b.zahl.wert →
      ∃ bound hi, (r.pc + 1, bound) ∈ (programm u).schleifen ∧
        (b.hi - a.lo).toNat ≤ bound.paesse ∧ bound.oben = some hi ∧ b.hi ≤ hi
  | .pruefeMass slot =>
    ∀ id a kern lo hi, r.funktion = some id → r.zahl slot = some a → 0 ≤ a.zahl.wert →
      findeKern u.2 id = some kern → kern.massIntervall = some (lo, hi) →
      lo ≤ a.lo ∧ a.hi ≤ hi
  | _ => True

theorem KostenEinrichtung.gueltig {u : Ast.Unit} {b : Befehl} {r : Rahmen}
    (typed : KostenEinrichtung u b r) : (kostenGrenzen u).Einrichtung b r := by
  cases b <;> simp only [KostenEinrichtung, KostenGrenzen.Einrichtung] at typed ⊢
  all_goals try exact typed
  case setzePasszahl =>
    intro a read
    exact (kostenGrenzen u).zaehlerKleiner _ _ _ (Int.toNat_le_toNat a.zahl.oben) (typed a read)
  case forAnfang =>
    intro a b lower upper ordered
    obtain ⟨bound, hi, mem, width, endpoint, high⟩ := typed a b lower upper ordered
    exact ⟨⟨bound, mem, (Int.toNat_le_toNat (Int.sub_le_sub b.zahl.oben a.zahl.unten)).trans width⟩,
      ⟨bound, hi, mem, endpoint, b.zahl.oben.trans high⟩⟩
  case pruefeMass =>
    intro id a named read nonneg want kern lo hi same find interval
    cases same
    obtain ⟨lower, upper⟩ := typed id a kern lo hi named read nonneg find interval
    rw [Int.toNat_of_nonneg nonneg]
    exact ⟨lower.trans a.zahl.unten, a.zahl.oben.trans upper⟩

/-- Once elaboration establishes the source-specific obligations at the three
    cost writes, the original correspondence follows over admitted machine runs. -/
theorem kostenSchrittKorrespondenz_ausEinrichtung
    (installs : ∀ (P : Plattform) (u : UnitMitSchranken) {h : Umgebung}
      {ρ : Lauf (einheitMitSchranken P u)}, Laeufe (einheitMitSchranken P u) h ρ →
      ∀ t s c b, ρ.zeit.zustand t = some s → (kostenGrenzen u.baum).ZustandGut s →
        (s.lokal c).Aktiv → (programm u.baum).code[(s.lokal c).pc]? = some b →
        KostenEinrichtung u.baum b (s.lokal c)) : KostenSchrittKorrespondenzAussage := by
  intro P u _ _ _ _ _ h ρ run
  have good (t : Nat) (s : Zustand) (cut : ρ.zeit.zustand t = some s) :=
    KostenGrenzen.lauf (g := kostenGrenzen u.baum) (programm u.baum) P
      (schrankenAusDeklaration u.deklaration) run
      (fun t s c b cut ok active lookup => (installs P u run t s c b cut ok active lookup).gueltig) t cut
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro _ _ _ _ _ _ _ _ head
    exact kostenKopf_mem P u head
  · intro t s c pc n cut read
    exact (good t s cut c).1.1 pc n read
  · intro t s c pc b cut read
    exact (good t s cut c).1.2.1 pc b read
  · intro t s c name n lo hi kern cut named read find interval
    exact (good t s cut c).1.2.2 n read name kern lo hi named find interval

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
  intro h
  have h2 : Ebound + Ebound ≤ Ebound + 0 := by
    simpa only [two_mul, Nat.add_zero] using h
  have hle : Ebound ≤ 0 := Nat.le_of_add_le_add_left h2
  have h0 : Ebound = 0 := Nat.le_zero.mp hle
  rw [h0] at hE
  exact Nat.lt_irrefl 0 hE

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
