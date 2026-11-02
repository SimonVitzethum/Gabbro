/-
  File:      Grammatik/StabilBewacht.lean
  Subject:   STABILITY WITHOUT INVARIANT FORM (lane 105, D9).

  The goal theorem needs, for assertions over shared carriers that are NOT
  in invariant form, the full `InterferenceFree` shape (`hFree`). This file
  replaces it by the standard rely/guarantee argument at chain grain:

  * `stabil_ohne_form` -- the induction: head validity plus own-step
    preservation plus foreign-step preservation (`hStabil`, one direction
    only) give the assertion at every chain world. No invariant form, no
    `HaengtAb`, no discipline -- pure chain folding (`kette_erhaelt` grain).
  * `stabil_aus_bewachung` -- the corollary that connects `hStabil` to the
    checker: `hStabil` follows from a static GUARANTEE (every foreign write
    to a carrier `Q f` reads happens only while holding a guard lock that
    `f` holds throughout -- `Bewacht` / `TraegerSchreibt` / `D.haelt`) plus
    a per-step RELY (guarded foreign writes leave `Q f`'s slots alone).
    The rely is memory-level (slot agreement, checker-comparable per run),
    so no assertion-level per-step proof is owed any more.
  * `haengtAb_aus_slotDep` -- the checker-shape link: slot-level dependence
    plus footprint coverage give table-level `HaengtAb`, the shape the
    `InterferenceFree` machinery consumes downstream.

  Witnesses (`_zeuge`) run on the reference fixture (`ReferenzB.lean`):
  a two-thread chain where `Q` (`slot 0 = slot 1`, "my slot equals my local
  counter") is not a whole-table invariant and the other thread writes only
  slot 5, a different slot of the same shared table.
-/
module
public import Grammatik.Nebenlaeufigkeit.Allgemein.StabilBewacht.Teil1a

public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.InterferenzAllgemein
public import Grammatik.Korpus.Referenz.ReferenzB

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- The witness step stays in the writer's frame: `einzahlen` may write
    the whole table, so every successor pair agrees outside `false`. -/
theorem zbSchritt_rahmen :
    Rahmen (refD.schreibt (zbCode 1)) (refD.gschreibt (zbCode 1)) zbW0 zbW1 := by
  constructor
  · intro t ht _ _
    cases t
    have htrue : refD.schreibt (zbCode 1) () = true := rfl
    rw [htrue] at ht
    simp only [Bool.true_eq_false] at ht
  · intro g
    exact nomatch g

/-- The witness chain: two threads, one step by the writer, empty run. -/
def zbJ : GemeinsamerLauf (D := refD) zbNb where
  faeden := [0, 1]
  code := zbCode
  eintritt := zbEintritt
  welten := [zbW0, zbW1]
  schrittFaden := [1]
  l := ([] : Lauf refD)
  hKette := rfl
  hSchritt := by
    intro k f' vor nach hk hv hn
    cases k with
    | zero =>
      simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_add_one, getElem?_pos,
  List.getElem_cons_zero, Option.some.injEq, Nat.reduceAdd, Nat.zero_lt_succ, List.getElem_cons_succ] at hk hv hn
      subst hk
      subst hv
      subst hn
      exact ⟨by simp only [List.mem_cons, Nat.succ_ne_self, List.not_mem_nil, or_false, or_true], zbSchritt_rahmen⟩
    | succ k => simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_one_iff, Nat.add_eq_zero_iff,
  Nat.succ_ne_self, and_false, not_false_eq_true, getElem?_neg, reduceCtorEq] at hk
  hPaar := by
    intro f' hf' g hg' hne
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hf' hg'
    rcases hf' with rfl | rfl <;> rcases hg' with rfl | rfl
    · exact absurd rfl hne
    · exact True.intro
    · exact True.intro
    · exact absurd rfl hne
  hGesittet := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro f j
      have hsp : Lauf.spur ([] : Lauf refD) f j = [] := by simp only [Lauf.spur, List.take_nil, List.filterMap_nil, List.reverse_nil]
      rw [hsp]
      exact konsistent_nil
    · intro f j e he
      have hsp : Lauf.spur ([] : Lauf refD) f j = [] := by simp only [Lauf.spur, List.take_nil, List.filterMap_nil, List.reverse_nil]
      rw [hsp] at he
      simp only [List.not_mem_nil] at he
    · intro j f L h hi g hne
      simp only [List.length_nil, Nat.not_lt_zero, not_false_eq_true, getElem?_neg, reduceCtorEq] at hi
    · intro i j f g m s s' ei ej hi hj hm hm'
      simp only [List.length_nil, Nat.not_lt_zero, not_false_eq_true, getElem?_neg, reduceCtorEq] at hi
    · intro i j f g o ei ej hi hj ht1 ht2 hu
      simp only [List.length_nil, Nat.not_lt_zero, not_false_eq_true, getElem?_neg, reduceCtorEq] at hi
  hBeschraenkt := by
    intro i j f g ei ej hi hj hne
    simp only [List.length_nil, Nat.not_lt_zero, not_false_eq_true, getElem?_neg, reduceCtorEq] at hi
  hEintritt := by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hf
    rcases hf with rfl | rfl
    · show EintrittPasst refLies zbWE
      show HeldGenau (Signatur.anfang refD (refD.signatur refLies)) zbWE.haelt
      rw [refLies_start]
      exact zbWE_haelt
    · show EintrittPasst refEin zbWE
      show HeldGenau (Signatur.anfang refD (refD.signatur refEin)) zbWE.haelt
      rw [refEin_start]
      exact zbWE_haelt
  hSchuld := by
    intro f hf i _
    exact nomatch i
  hInvSicht := by
    intro f hf i _
    exact nomatch i

/-- Projections of the witness chain, by computation. -/
theorem zbJ_welten : zbJ.welten = [zbW0, zbW1] := by rfl

/-- Projections of the witness chain, by computation. -/
theorem zbJ_schritt : zbJ.schrittFaden = [1] := by rfl

/-- Projections of the witness chain, by computation. -/
theorem zbJ_faeden : zbJ.faeden = [0, 1] := by rfl

/-- `Q` holds at the head world: both read slots are `0`. -/
theorem zbQ_W0 (f : Faden) : zbQ f zbW0 := by rfl

/-- `Q` holds at the end world: slots 0 and 1 are untouched by the
    slot-5 write. -/
theorem zbQ_W1 (f : Faden) : zbQ f zbW1 := by
  show (if (0 : Int) = 5 then zbV7 else zbV0) =
    (if (1 : Int) = 5 then zbV7 else zbV0)
  rw [if_neg (by decide), if_neg (by decide)]

/-- Head validity on the witness chain. -/
theorem zbKopf : ∀ f ∈ zbJ.faeden, ∀ σ₀, zbJ.welten[0]? = some σ₀ → zbQ f σ₀ := by
  intro f hf σ₀ h
  rw [zbJ_welten] at h
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.zero_lt_succ, getElem?_pos,
  List.getElem_cons_zero, Option.some.injEq] at h
  subst h
  rw [zbJ_faeden] at hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact zbQ_W0 0
  · exact zbQ_W0 1

/-- Own-step preservation on the witness chain: the only step is thread 1's
    slot-5 write, which leaves `Q`'s slots alone. (`hQvor` is carried for
    shape; the step preserves `Q` by computation.) -/
theorem zbEigen : ∀ f ∈ zbJ.faeden, ∀ (k : Nat) (vor nach : World refD),
    zbJ.schrittFaden[k]? = some f → zbJ.welten[k]? = some vor →
      zbJ.welten[k + 1]? = some nach → zbQ f vor → zbQ f nach := by
  intro f hf k vor nach hk hv hn hQvor
  rw [zbJ_schritt] at hk
  rw [zbJ_welten] at hv hn
  rw [zbJ_faeden] at hf
  cases k with
  | zero =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_add_one, getElem?_pos,
  List.getElem_cons_zero, Option.some.injEq, Nat.succ_ne_self] at hk
    · simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_add_one, getElem?_pos,
  List.getElem_cons_zero, Nat.reduceAdd, Nat.zero_lt_succ, Option.some.injEq, List.getElem_cons_succ] at hk hv hn
      subst hv
      subst hn
      exact zbQ_W1 1
  | succ k => simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_one_iff, Nat.add_eq_zero_iff,
  Nat.succ_ne_self, and_false, not_false_eq_true, getElem?_neg, reduceCtorEq] at hk

/-- Foreign-step preservation on the witness chain: the only foreign step
    (thread 1, seen from thread 0) is the slot-5 write. (`hQvor` is carried
    for shape; preservation is by computation.) -/
theorem zbStabil : ∀ f ∈ zbJ.faeden, ∀ (k : Nat) (g : Faden) (vor nach : World refD),
    g ∈ zbJ.faeden → g ≠ f → zbJ.schrittFaden[k]? = some g →
      zbJ.welten[k]? = some vor → zbJ.welten[k + 1]? = some nach →
      zbQ f vor → zbQ f nach := by
  intro f hf k g vor nach hgm hne hk hv hn hQvor
  rw [zbJ_schritt] at hk
  rw [zbJ_welten] at hv hn
  rw [zbJ_faeden] at hgm hf
  cases k with
  | zero =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hgm hf
    rcases hgm with rfl | rfl
    · simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_add_one, getElem?_pos,
  List.getElem_cons_zero, Option.some.injEq, Nat.succ_ne_self] at hk
    · simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_add_one, getElem?_pos,
  List.getElem_cons_zero, Nat.reduceAdd, Nat.zero_lt_succ, Option.some.injEq, List.getElem_cons_succ] at hk hv hn
      subst hv
      subst hn
      rcases hf with rfl | rfl
      · exact zbQ_W1 0
      · exact absurd rfl hne
  | succ k => simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_one_iff, Nat.add_eq_zero_iff,
  Nat.succ_ne_self, and_false, not_false_eq_true, getElem?_neg, reduceCtorEq] at hk

/-- Every witness thread holds exactly the guard, by computation. -/
theorem zbHaelt (f : Faden) (hf : f ∈ zbJ.faeden) :
    refD.haelt (zbCode f) = [()] := by
  rw [zbJ_faeden] at hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl <;> rfl

/-- The writer writes the table; the reader writes nothing. -/
theorem zbSchreibtEin : refD.schreibt (zbCode 1) () = true := by rfl

/-- The writer writes the table; the reader writes nothing. -/
theorem zbSchreibtLies : refD.schreibt (zbCode 0) () = false := by rfl

/-- Slot-level dependence of `Q`: slots 0 and 1 fix both sides. (The
    global agreement is carried for shape; `refD` has no globals.) -/
theorem zbDep : ∀ f ∈ zbJ.faeden, ∀ σ σ' : World refD,
    (∀ (t : refD.Tab) (k : Int) (fld : refD.Feld t),
      zbSf f t k fld → σ'.slots t k fld = σ.slots t k fld) →
    (∀ x : refD.Glob, zbGf f x = true → σ'.globs x = σ.globs x) →
    (zbQ f σ ↔ zbQ f σ') := by
  intro f _ σ σ' hs hGlob
  constructor
  · intro h
    show σ'.slots () 0 () = σ'.slots () 1 ()
    rw [hs () 0 () ⟨rfl, Or.inl rfl⟩, hs () 1 () ⟨rfl, Or.inr rfl⟩]
    exact h
  · intro h
    show σ.slots () 0 () = σ.slots () 1 ()
    rw [← hs () 0 () ⟨rfl, Or.inl rfl⟩, ← hs () 1 () ⟨rfl, Or.inr rfl⟩]
    exact h

/-- The table footprint: the whole shared table. -/
def zbWf : Faden → refD.Tab → Bool := fun _ _ => true

/-- Every read slot lies in the footprint table. -/
theorem zbCover : ∀ f ∈ zbJ.faeden, ∀ (t : refD.Tab) (k : Int) (fld : refD.Feld t),
    zbSf f t k fld → zbWf f t = true := by
  intro f _ t k fld _
  rfl

/-- Static guarantee on the witness chain: the only writer of `Q`'s
    table is thread 1, writing under the guard both threads hold. (The
    disequality and the slot index are carried for shape.) -/
theorem zbWacheT : ∀ (f g : Faden), f ∈ zbJ.faeden → g ∈ zbJ.faeden → g ≠ f →
    ∀ (t : refD.Tab) (k : Int) (fld : refD.Feld t),
      zbSf f t k fld → refD.schreibt (zbCode g) t = true →
      ∃ L : refD.Lock, Bewacht (D := refD) (.inl t) L ∧ L ∈ refD.haelt (zbCode f) ∧
        L ∈ refD.haelt (zbCode g) := by
  intro f g hf hg hne t k fld hSf hwrite
  rw [zbJ_faeden] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · cases t
    rw [zbSchreibtLies] at hwrite
    simp only [Bool.false_eq_true] at hwrite
  · obtain ⟨rfl, _⟩ := hSf
    refine ⟨(), List.Mem.head _, ?_, ?_⟩
    · rw [zbHaelt f hf]
      exact List.mem_singleton.mpr rfl
    · have hg1 : (1 : Faden) ∈ zbJ.faeden := by simp only [zbJ_faeden, List.mem_cons, Nat.succ_ne_self, List.not_mem_nil, or_false, or_true]
      rw [zbHaelt 1 hg1]
      exact List.mem_singleton.mpr rfl

/-- No globals exist, so the global guard holds vacuously. (Premises
    carried for shape.) -/
theorem zbWacheG : ∀ (f g : Faden), f ∈ zbJ.faeden → g ∈ zbJ.faeden → g ≠ f →
    ∀ x : refD.Glob, zbGf f x = true → refD.gschreibt (zbCode g) x = true →
      ∃ L : refD.Lock, Bewacht (D := refD) (.inr x) L ∧ L ∈ refD.haelt (zbCode f) ∧
        L ∈ refD.haelt (zbCode g) := by
  intro f hf g hg hne x hx hwrite
  exact nomatch x

end Gabbro.Grammatik
