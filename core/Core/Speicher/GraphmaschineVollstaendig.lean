/-
  File:      core/Core/Speicher/GraphmaschineVollstaendig.lean
  Subject:   COMPLETENESS of the graph machine against `Konsistent` (`erzeugt`): every finite,
             consistent and complete execution graph whose events of one thread are ordered by
             program order is produced by a run of the machine, up to a renaming of its events.
             The run appends the events last-first by induction: a `po ∪ rf`-maximal event
             exists since `po ∪ rf` is acyclic (`maximal_existiert`), the rest is consistent by
             `einschraenken_konsistent`, and the event is appended at the end of its thread.
-/
module

public import Core.Speicher.Graphmaschine
public import Mathlib.Data.Fintype.Card
public import Mathlib.SetTheory.Cardinal.NatCard

@[expose] public section

namespace Gabbro.Core.Speicher

namespace Zustand

variable {E F Ort Wert : Type}

/-- **The graph `G` with threads `th` is produced by the machine**: a reachable state and a
    bijection from its indices onto the events of `G` that carries threads, labels, `po`, `rf`
    and `mo`. -/
def Erzeugt (G : Graph E Ort Wert) (th : E → F) : Prop :=
  ∃ Z : Zustand F Ort Wert, Erreichbar Z ∧ ∃ e : Fin Z.ev.length → E, Function.Bijective e ∧
    (∀ a, (Z.ev[a.1]'a.2).kontext = th (e a)) ∧ Graph.Einbettung Z.graph G e

/-- A finite graph without `po ∪ rf` cycles has an event after which nothing comes in
    `po ∪ rf`. -/
theorem maximal_existiert [Finite E] [Nonempty E] {G : Graph E Ort Wert}
    (hk : G.Konsistent) : ∃ m, ∀ x, ¬ G.porf m x := by
  let r : E → E → Prop := fun x y => Relation.TransGen G.porf y x
  have : IsTrans E r := ⟨fun _ _ _ h1 h2 => Relation.TransGen.trans h2 h1⟩
  have : Std.Irrefl r := ⟨fun a h => hk.ohneLB a h⟩
  obtain ⟨m, -, hm⟩ := (Finite.wellFounded_of_trans_of_irrefl r).has_min Set.univ Set.univ_nonempty
  exact ⟨m, fun x hx => hm x (Set.mem_univ x) (.single hx)⟩

/-- Without a `po ∪ rf`-maximal event the rest of a complete graph stays complete. -/
theorem ohne_vollstaendig {G : Graph E Ort Wert} {m : E} (hv : G.Vollstaendig)
    (hmax : ∀ x, ¬ G.porf m x) : (G.einschraenken (· ≠ m)).Vollstaendig := by
  intro r hr
  obtain ⟨w, hw⟩ := hv r.1 hr
  have hwm : w ≠ m := by
    intro e
    rw [e] at hw
    exact hmax r.1 (Or.inr hw)
  exact ⟨⟨w, hwm⟩, hw⟩

/-! ## Appending the maximal event -/

/-- The enumeration of the old events extended by the new last event `m`. -/
def erweitern {m : E} {n : Nat} (e₀ : Fin n → {x // x ≠ m}) (i : Nat) : E :=
  if h : i < n then (e₀ ⟨i, h⟩).1 else m

theorem erweitern_alt {m : E} {n : Nat} {e₀ : Fin n → {x // x ≠ m}} {i : Nat} (h : i < n) :
    erweitern e₀ i = (e₀ ⟨i, h⟩).1 := by
  simp only [erweitern, h, ↓reduceDIte]

theorem erweitern_neu {m : E} {n : Nat} {e₀ : Fin n → {x // x ≠ m}} : erweitern e₀ n = m := by
  simp only [erweitern, Nat.lt_irrefl, ↓reduceDIte]

theorem erweitern_inj {m : E} {n : Nat} {e₀ : Fin n → {x // x ≠ m}}
    (he : Function.Injective e₀) {i j : Nat} (hi : i < n + 1) (hj : j < n + 1)
    (h : erweitern e₀ i = erweitern e₀ j) : i = j := by
  rcases Nat.lt_or_ge i n with hi' | hi'
  · rcases Nat.lt_or_ge j n with hj' | hj'
    · rw [erweitern_alt hi', erweitern_alt hj'] at h
      exact congrArg Fin.val (he (Subtype.ext h))
    · rw [show j = n by omega, erweitern_alt hi', erweitern_neu] at h
      exact absurd h (e₀ ⟨i, hi'⟩).2
  · rcases Nat.lt_or_ge j n with hj' | hj'
    · rw [show i = n by omega, erweitern_alt hj', erweitern_neu] at h
      exact absurd h.symm (e₀ ⟨j, hj'⟩).2
    · omega

theorem erweitern_surj {m : E} {n : Nat} {e₀ : Fin n → {x // x ≠ m}}
    (he : Function.Surjective e₀) (x : E) : ∃ i, i < n + 1 ∧ erweitern e₀ i = x := by
  by_cases hx : x = m
  · exact ⟨n, Nat.lt_succ_self n, by rw [erweitern_neu, hx]⟩
  · obtain ⟨c, hc⟩ := he ⟨x, hx⟩
    refine ⟨c.1, Nat.lt_succ_of_lt c.2, ?_⟩
    rw [erweitern_alt c.2]
    exact congrArg Subtype.val hc

section Fortsetzung

variable (G : Graph E Ort Wert) (th : E → F) {m : E} (Z : Zustand F Ort Wert)
  (e₀ : Fin Z.ev.length → {x // x ≠ m})

/-- **The state after appending `m`**: the relations are those of `G` along the extended
    enumeration. -/
def fortsetzung : Zustand F Ort Wert :=
  Z.anhaengen ⟨th m, G.lab m⟩ (fun i j => G.po (erweitern e₀ i) (erweitern e₀ j))
    (fun i j => G.rf (erweitern e₀ i) (erweitern e₀ j))
    (fun i j => G.mo (erweitern e₀ i) (erweitern e₀ j))

variable {G th Z e₀}

theorem fortsetzung_laenge : (fortsetzung G th Z e₀).ev.length = Z.ev.length + 1 :=
  anhaengen_laenge _ _ _ _ _

/-- The hypotheses of one induction step: `e₀` enumerates the rest without `m`, which the
    state `Z` produces. -/
structure Annahmen (G : Graph E Ort Wert) (th : E → F) (m : E) (Z : Zustand F Ort Wert)
    (e₀ : Fin Z.ev.length → {x // x ≠ m}) : Prop where
  bij : Function.Bijective e₀
  kontext : ∀ i (h : i < Z.ev.length), (Z.ev[i]'h).kontext = th (e₀ ⟨i, h⟩).1
  einb : Graph.Einbettung Z.graph (G.einschraenken (· ≠ m)) e₀
  max : ∀ x, ¬ G.porf m x
  tot : ∀ a b, th a = th b → a ≠ b → G.po a b ∨ G.po b a

theorem fortsetzung_ev_alt {i : Nat} (hi : i < Z.ev.length)
    (h : i < (fortsetzung G th Z e₀).ev.length) :
    (fortsetzung G th Z e₀).ev[i]'h = Z.ev[i]'hi :=
  anhaengen_alt _ _ _ _ _ hi h

theorem fortsetzung_ev_neu (h : Z.ev.length < (fortsetzung G th Z e₀).ev.length) :
    (fortsetzung G th Z e₀).ev[Z.ev.length]'h = ⟨th m, G.lab m⟩ :=
  anhaengen_neu _ _ _ _ _ h

theorem fortsetzung_faden (A : Annahmen G th m Z e₀) (i : Nat)
    (h : i < (fortsetzung G th Z e₀).ev.length) :
    ((fortsetzung G th Z e₀).ev[i]'h).kontext = th (erweitern e₀ i) := by
  have h1 : i < Z.ev.length + 1 := by rw [← fortsetzung_laenge]; exact h
  rcases Nat.lt_or_ge i Z.ev.length with hi | hi
  · rw [fortsetzung_ev_alt hi, erweitern_alt hi]
    exact A.kontext i hi
  · obtain rfl : i = Z.ev.length := by omega
    rw [fortsetzung_ev_neu, erweitern_neu]

theorem fortsetzung_lab (i : Nat) (h : i < (fortsetzung G th Z e₀).ev.length)
    (A : Annahmen G th m Z e₀) :
    ((fortsetzung G th Z e₀).ev[i]'h).lab = G.lab (erweitern e₀ i) := by
  have h1 : i < Z.ev.length + 1 := by rw [← fortsetzung_laenge]; exact h
  rcases Nat.lt_or_ge i Z.ev.length with hi | hi
  · rw [fortsetzung_ev_alt hi, erweitern_alt hi]
    exact A.einb.lab ⟨i, hi⟩
  · obtain rfl : i = Z.ev.length := by omega
    rw [fortsetzung_ev_neu, erweitern_neu]

/-- The extended enumeration as a map on the indices of the new state. -/
def fortsetzungAbb (G : Graph E Ort Wert) (th : E → F) (Z : Zustand F Ort Wert)
    (e₀ : Fin Z.ev.length → {x // x ≠ m}) (a : Fin (fortsetzung G th Z e₀).ev.length) : E :=
  erweitern e₀ a.1

theorem fortsetzung_einbettung (A : Annahmen G th m Z e₀) :
    Graph.Einbettung (fortsetzung G th Z e₀).graph G (fortsetzungAbb G th Z e₀) where
  inj := fun a b h => by
    have ha : a.1 < Z.ev.length + 1 := by rw [← fortsetzung_laenge]; exact a.2
    have hb : b.1 < Z.ev.length + 1 := by rw [← fortsetzung_laenge]; exact b.2
    exact Fin.ext (erweitern_inj A.bij.1 ha hb h)
  lab := fun a => fortsetzung_lab a.1 a.2 A
  po := fun _ _ => Iff.rfl
  rf := fun _ _ => Iff.rfl
  mo := fun _ _ => Iff.rfl

theorem fortsetzung_bij (A : Annahmen G th m Z e₀) :
    Function.Bijective (fortsetzungAbb G th Z e₀) := by
  refine ⟨fun a b h => (fortsetzung_einbettung A).inj a b h, fun x => ?_⟩
  obtain ⟨i, hi, hx⟩ := erweitern_surj A.bij.2 x
  exact ⟨⟨i, by rw [fortsetzung_laenge]; exact hi⟩, hx⟩

/-- The relations among the old events are those of `Z`. -/
theorem fortsetzung_alt (A : Annahmen G th m Z e₀) {i j : Nat} (hi : i < Z.ev.length)
    (hj : j < Z.ev.length) :
    ((fortsetzung G th Z e₀).po i j ↔ Z.po i j) ∧ ((fortsetzung G th Z e₀).rf i j ↔ Z.rf i j) ∧
      ((fortsetzung G th Z e₀).mo i j ↔ Z.mo i j) := by
  show (G.po (erweitern e₀ i) (erweitern e₀ j) ↔ Z.po i j) ∧
    (G.rf (erweitern e₀ i) (erweitern e₀ j) ↔ Z.rf i j) ∧
    (G.mo (erweitern e₀ i) (erweitern e₀ j) ↔ Z.mo i j)
  rw [erweitern_alt hi, erweitern_alt hj]
  exact ⟨(A.einb.po ⟨i, hi⟩ ⟨j, hj⟩).symm, (A.einb.rf ⟨i, hi⟩ ⟨j, hj⟩).symm,
    (A.einb.mo ⟨i, hi⟩ ⟨j, hj⟩).symm⟩

/-- **Appending `m` is a step of the machine.** -/
theorem fortsetzung_schritt (A : Annahmen G th m Z e₀) (hk : G.Konsistent)
    (hv : G.Vollstaendig) : Schritt Z (th m) (G.lab m) (fortsetzung G th Z e₀) where
  ev := rfl
  po_alt := fun _ _ hi hj => (fortsetzung_alt A hi hj).1
  rf_alt := fun _ _ hi hj => (fortsetzung_alt A hi hj).2.1
  mo_alt := fun _ _ hi hj => (fortsetzung_alt A hi hj).2.2
  po_faden := fun i hi hf => by
    show G.po (erweitern e₀ i) (erweitern e₀ Z.ev.length)
    rw [erweitern_alt hi, erweitern_neu]
    rw [A.kontext i hi] at hf
    rcases A.tot _ _ hf (e₀ ⟨i, hi⟩).2 with h | h
    · exact h
    · exact absurd (Or.inl h) (A.max _)
  po_ende := fun i _ h => by
    have h' : G.po (erweitern e₀ Z.ev.length) (erweitern e₀ i) := h
    rw [erweitern_neu] at h'
    exact A.max _ (Or.inl h')
  rf_ende := fun i _ h => by
    have h' : G.rf (erweitern e₀ Z.ev.length) (erweitern e₀ i) := h
    rw [erweitern_neu] at h'
    exact A.max _ (Or.inr h')
  konsistent := (fortsetzung_einbettung A).konsistent hk
  vollstaendig := (fortsetzung_einbettung A).vollstaendig (fortsetzung_bij A).2 hv

end Fortsetzung

/-! ## Completeness -/

theorem erzeugt_leer [IsEmpty E] (G : Graph E Ort Wert) (th : E → F) : Erzeugt G th := by
  refine ⟨leer, .start, fun a => (leer_elim a).elim, ⟨fun a => (leer_elim a).elim,
    fun x => (IsEmpty.false x).elim⟩, fun a => (leer_elim a).elim, ?_⟩
  exact {
    inj := fun a => (leer_elim a).elim
    lab := fun a => (leer_elim a).elim
    po := fun a => (leer_elim a).elim
    rf := fun a => (leer_elim a).elim
    mo := fun a => (leer_elim a).elim }

theorem erzeugt_aux (n : Nat) : ∀ (X : Type) [Finite X], Nat.card X = n →
    ∀ (G : Graph X Ort Wert) (th : X → F), G.Konsistent → G.Vollstaendig →
      (∀ a b, th a = th b → a ≠ b → G.po a b ∨ G.po b a) → Erzeugt G th := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X _ hn G th hk hv htot
    rcases isEmpty_or_nonempty X with hX | hX
    · exact erzeugt_leer G th
    · have : Nonempty X := hX
      obtain ⟨m, hmax⟩ := maximal_existiert hk
      have hlt : Nat.card {x // x ≠ m} < n := by
        rw [← hn]
        exact Finite.card_subtype_lt (p := fun x => x ≠ m) (x := m) (fun h => h rfl)
      obtain ⟨Z, hZ, e₀, hb, hf, hE₀⟩ := ih _ hlt {x // x ≠ m} rfl (G.einschraenken (· ≠ m))
        (fun x => th x.1) (Graph.einschraenken_konsistent hk _) (ohne_vollstaendig hv hmax)
        (fun a b h hne => htot a.1 b.1 h (fun e => hne (Subtype.ext e)))
      have A : Annahmen G th m Z e₀ :=
        ⟨hb, fun i h => hf ⟨i, h⟩, hE₀, hmax, htot⟩
      exact ⟨fortsetzung G th Z e₀, .schritt _ _ hZ (fortsetzung_schritt A hk hv),
        fortsetzungAbb G th Z e₀, fortsetzung_bij A,
        fun a => fortsetzung_faden A a.1 a.2, fortsetzung_einbettung A⟩

/-- **Completeness of the graph machine**: every finite, consistent and complete execution
    graph whose events of one thread are ordered by program order is produced by a run of the
    machine (up to a renaming of its events). Together with `erreichbar_gut` the machine's
    reachable states are exactly the consistent complete graphs. -/
theorem erzeugt [Finite E] (G : Graph E Ort Wert) (th : E → F) (hk : G.Konsistent)
    (hv : G.Vollstaendig) (htot : ∀ a b, th a = th b → a ≠ b → G.po a b ∨ G.po b a) :
    Erzeugt G th :=
  erzeugt_aux _ E rfl G th hk hv htot

end Zustand

end Gabbro.Core.Speicher
