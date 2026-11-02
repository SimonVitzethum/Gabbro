/-
  File:      Grammatik/DisziplinBedarf.lean
  Subject:   Guards only where they are needed (D3).

  The discipline package `invariantenKontext_aus_disziplin`
  (`InterferenzAllgemein.lean`) requires `hGuardEx`: every carrier has a
  guard lock. Ordinary programs leave unshared or read-only carriers
  unguarded, so the premise fits nothing ordinary. This file proves the
  narrowed version: only carriers that some member thread WRITES need a
  guard (`hGuardBedarf`). A carrier no member writes keeps its slots
  along the whole chain (`traegerStill_ohneSchreiber`, via the
  non-writer preservation `nichtschreiber_erhaelt`); a written carrier
  runs through the existing per-carrier chain lemma
  (`hinv_kette_aus_disziplin`), exactly as the old proof did.
-/
module

public import Grammatik.Nebenlaeufigkeit.Allgemein.DisziplinBedarf.Teil1a

public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.InterferenzAllgemein
public import Grammatik.Kern.Semantik.Maschine
public import Grammatik.Korpus.Referenz.ReferenzB

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}
/-- No threads are declared to share the witness run. -/
def bedNb : Nebeneinander := fun _ _ => False

/-- The joint witness run: thread `0` runs the writer, over the two
    worlds where the single step stores `100` into `konto`. -/
def bedJ : GemeinsamerLauf (D := bedD) bedNb :=
  { faeden := [0]
    code := fun _ => true
    eintritt := fun _ => bedW0
    welten := [bedW0, bedW1]
    schrittFaden := [0]
    l := []
    hKette := by rfl
    hSchritt := by
      intro k f vor nach hkg hkv hkn
      cases k with
      | zero =>
        have hf : 0 = f := by simpa using hkg
        have hv : bedW0 = vor := by simpa using hkv
        have hn : bedW1 = nach := by simpa using hkn
        subst hf
        subst hv
        subst hn
        exact ⟨by simp only [List.mem_cons, List.not_mem_nil, or_false], bedRahmen⟩
      | succ n =>
        cases n with
        | zero => simp only [Nat.zero_add, Nat.reduceAdd, List.length_cons, List.length_nil, Nat.lt_irrefl, not_false_eq_true,
  getElem?_neg, reduceCtorEq] at hkn
        | succ n => simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.not_lt, Nat.le_add_left,
  getElem?_neg, reduceCtorEq] at hkv
    hPaar := by
      intro f hf g hg hne
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf hg
      subst hf
      subst hg
      exact absurd rfl hne
    hGesittet := by
      show Gesittet ([] : Lauf bedD)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro f j
        have hsp : Lauf.spur ([] : Lauf bedD) f j = [] := by simp only [Lauf.spur, List.take_nil, List.filterMap_nil, List.reverse_nil]
        rw [hsp]
        exact konsistent_nil
      · intro f j e he
        have hsp : Lauf.spur ([] : Lauf bedD) f j = [] := by simp only [Lauf.spur, List.take_nil, List.filterMap_nil, List.reverse_nil]
        rw [hsp] at he
        simp only [List.not_mem_nil] at he
      · intro j f L h hi g hne
        simp only [List.length_nil, Nat.not_lt_zero, not_false_eq_true, getElem?_neg, reduceCtorEq] at hi
      · intro i j f g m s s' ei ej hi hj hm hm'
        simp only [List.length_nil, Nat.not_lt_zero, not_false_eq_true, getElem?_neg, reduceCtorEq] at hi
      · intro i j f g o ei ej hi hj ht1 ht2 hu
        simp only [List.length_nil, Nat.not_lt_zero, not_false_eq_true, getElem?_neg, reduceCtorEq] at hi
    hBeschraenkt := by
      show BeschraenkteVerschraenkung (D := bedD) bedNb ([] : Lauf bedD)
      intro i j f g ei ej hi hj hne
      simp only [List.length_nil, Nat.not_lt_zero, not_false_eq_true, getElem?_neg, reduceCtorEq] at hi
    hEintritt := by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      subst hf
      show HeldGenau (Signatur.anfang bedD (bedD.signatur true)) bedW0.haelt
      rw [bedAnfang_schreib]
      intro L
      have eL : L = () := by cases L <;> rfl
      have eH : bedW0.haelt = [()] := rfl
      rw [eH, eL]
      constructor
      · intro hL
        have heq : Res.held (D := bedD) L = Res.held (D := bedD) () :=
          (List.mem_singleton.mp hL)
        cases heq
        exact List.mem_singleton.mpr rfl
      · intro hL
        have heq : L = () :=
          (List.mem_singleton.mp (eH ▸ hL))
        cases heq
        exact List.mem_singleton.mpr rfl
    hSchuld := by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      subst hf
      intro i hs
      exact nomatch i
    hInvSicht := by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      subst hf
      intro i hs
      exact nomatch i
  }

/-- Equation helpers for rewriting in the witness proofs. -/
theorem bedJ_faeden : bedJ.faeden = [0] := by rfl

theorem bedJ_welten : bedJ.welten = [bedW0, bedW1] := by rfl

/-- Trivially true carrier invariant; its discipline holds because the
    writer holds the lock over the one carrier it writes. -/
def bedI : TraegerInv (D := bedD) where
  inv := fun _ _ => True
  disziplin := by
    intro f c h
    cases c with
    | inl t =>
      cases t with
      | true =>
        cases f with
        | true =>
          intro w hw
          rw [bedBraucht_konto] at hw
          have hw2 : w = Sum.inl () := List.mem_singleton.mp hw
          subst hw2
          rw [bedAnfang_schreib]
          exact List.mem_singleton.mpr rfl
        | false => exact absurd h (by decide)
      | false =>
        cases f with
        | true => exact absurd h (by decide)
        | false => exact absurd h (by decide)
    | inr g => exact nomatch g

/-- Singleton table footprint: the witness of the carrier itself. -/
def bedWc : (c : bedD.Tab ⊕ bedD.Glob) → bedD.Tab → Bool
  | .inl t', t => decide (t = t')
  | .inr g, _ => nomatch g

/-- Empty global footprint: there are no globals. -/
def bedGc : (c : bedD.Tab ⊕ bedD.Glob) → bedD.Glob → Bool
  | _, x => nomatch x

/-- The trivial invariant hangs on any footprint. -/
theorem bedAb : ∀ c, HaengtAb (bedWc c) (bedGc c) (bedI.inv c) := by
  intro c σ σ' _
  exact Iff.rfl

/-- The table footprint is a singleton frame. -/
theorem bedFrameT :
    ∀ (c : bedD.Tab ⊕ bedD.Glob) (t : bedD.Tab),
      bedWc c t = true → c = .inl t := by
  intro c t h
  cases c with
  | inl t' =>
    simp only [bedWc] at h
    have ht : t = t' := of_decide_eq_true h
    subst ht
    rfl
  | inr g => exact nomatch g

/-- The global footprint is a singleton frame, vacuously. -/
theorem bedFrameG :
    ∀ (c : bedD.Tab ⊕ bedD.Glob) (x : bedD.Glob),
      bedGc c x = true → c = .inr x := by
  intro c x _
  exact nomatch x

/-- Only `konto` is ever written, and it is guarded. -/
theorem bedGuardBedarf : ∀ c : bedD.Tab ⊕ bedD.Glob,
    (∃ g, g ∈ bedJ.faeden ∧ TraegerSchreibt (bedJ.code g) c = true) →
      ∃ L : bedD.Lock, Bewacht (D := bedD) c L := by
  intro c h
  obtain ⟨g, hg, hw⟩ := h
  rw [bedJ_faeden] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  subst hg
  cases c with
  | inl t =>
    cases t with
    | true => exact ⟨(), bedGuard_konto⟩
    | false => exact absurd hw (by decide)
  | inr x => exact nomatch x

/-- Entry holds: the invariant is trivially true. -/
theorem bedEntry : ∀ (c : bedD.Tab ⊕ bedD.Glob) (σ₀ : World bedD),
    bedJ.welten[0]? = some σ₀ → bedI.inv c σ₀ := by
  intro c σ₀ h
  rw [bedJ_welten] at h
  have h0 : bedW0 = σ₀ := by simpa using h
  subst h0
  trivial

/-- Return re-establishes the trivial invariant; the chain position is
    pinned by the two-element world list. -/
theorem bedReturn : ∀ (c : bedD.Tab ⊕ bedD.Glob) (L : bedD.Lock) (k : Nat)
    (g : Faden) (vor nach : World bedD),
    Bewacht (D := bedD) c L → g ∈ bedJ.faeden → bedJ.schrittFaden[k]? = some g →
      bedJ.welten[k]? = some vor → bedJ.welten[k + 1]? = some nach →
        TraegerSchreibt (bedJ.code g) c = true → L ∈ bedD.haelt (bedJ.code g) →
          bedI.inv c nach := by
  intro c L k g vor nach hB hg hkg hkv hkn hw hh
  rw [bedJ_welten] at hkn
  have hk0 : k = 0 := by
    have hlen : k + 1 < [bedW0, bedW1].length := lt_of_belegt _ _ _ hkn
    simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hlen
    omega
  subst hk0
  have hn : bedW1 = nach := by simpa using hkn
  subst hn
  trivial

end Gabbro.Grammatik
