module

public import Grammatik.Bausteine.Kernzelle.Verlauf
public import Grammatik.Bausteine.Kernzelle.KernAbfrageBindung
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiOrte
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtMehrfaden

@[expose] public section



namespace Gabbro.Grammatik.Kernzelle

open Gabbro.Grammatik Gabbro.Grammatik.Isabelle.AccumulatesMonoid

variable {D : Deklaration}

/-! ## 1. Decidable schema checks -/

/-- The schema validity, decided. -/
def akkuGueltigB : AccOperator → Int → Int → Nat → Bool
  | .max, lo, hi, _ => decide (lo ≤ hi)
  | .min, lo, hi, _ => decide (lo ≤ hi)
  | .add, lo, hi, _ => decide (lo ≤ hi) && decide (lo ≤ 0) && decide (0 ≤ hi)
  | .or, lo, hi, w =>
      decide (lo ≤ hi) && decide (1 ≤ w) && decide (lo ≤ 0) && decide (0 ≤ hi) &&
      decide (0 ≤ lo) && decide (hi < 2 ^ w)
  | .and, lo, hi, w =>
      decide (lo ≤ hi) && decide (1 ≤ w) && decide (0 ≤ lo) && decide (hi < 2 ^ w) &&
      decide (lo ≤ ((2 ^ w - 1 : Nat) : Int)) && decide (((2 ^ w - 1 : Nat) : Int) ≤ hi)

/-- The Bool decides the schema validity. -/
theorem akkuGueltigB_iff {op : AccOperator} {lo hi : Int} {w : Nat} :
    akkuGueltigB op lo hi w = true ↔ akkuGueltig op lo hi w := by
  cases op with
  | max => simp only [akkuGueltigB, akkuGueltig, decide_eq_true_eq]
  | min => simp only [akkuGueltigB, akkuGueltig, decide_eq_true_eq]
  | add => simp only [akkuGueltigB, akkuGueltig, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  | or => simp only [akkuGueltigB, akkuGueltig, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  | and => simp only [akkuGueltigB, akkuGueltig, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-- The width fit, decided. -/
def akkuBreitePasstB (v : Bool) (lo hi : Int) (w : Nat) : Bool :=
  if v then decide (-(2 ^ (w - 1) : Int) ≤ lo) && decide (hi < 2 ^ (w - 1))
  else decide (0 ≤ lo) && decide (hi < 2 ^ w)

/-- The Bool decides the width fit. -/
theorem akkuBreitePasstB_iff {v : Bool} {lo hi : Int} {w : Nat} :
    akkuBreitePasstB v lo hi w = true ↔ akkuBreitePasst v lo hi w := by
  unfold akkuBreitePasstB akkuBreitePasst
  split <;> simp only [Bool.and_eq_true, decide_eq_true_eq]

/-- Finite injectivity, decided by pairwise comparison. -/
def injFinB {n : Nat} {α : Type} [DecidableEq α] (f : Fin n → α) : Bool :=
  (List.finRange n).all fun i =>
    (List.finRange n).all fun j => decide (i = j) || decide (f i ≠ f j)

/-- The Bool decides injectivity. -/
theorem injFinB_iff {n : Nat} {α : Type} [DecidableEq α] {f : Fin n → α} :
    injFinB f = true ↔ Function.Injective f := by
  unfold injFinB
  rw [List.all_eq_true]
  constructor
  · intro h i j hij
    have h1 := (List.all_eq_true.mp (h i (List.mem_finRange i))) j (List.mem_finRange j)
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h1
    rcases h1 with heq | hne
    · exact heq
    · exact absurd hij hne
  · intro h i _
    refine List.all_eq_true.mpr fun j _ => ?_
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    by_cases e : i = j
    · exact Or.inl e
    · exact Or.inr (fun heq => e (h heq))

/-- Finite universal quantification over `Fin n`, decided. -/
theorem finRangeAll_iff {n : Nat} {p : Fin n → Bool} :
    (List.finRange n).all p = true ↔ ∀ i, p i = true := by
  rw [List.all_eq_true]
  constructor
  · intro h i
    exact h i (List.mem_finRange i)
  · intro h i _
    exact h i

/-! ## 2. Descriptor admission, decided -/

variable [DecidableEq D.Fn]

variable [DecidableEq D.Ax]

/-- The descriptor validity, decided. -/
def akkuOkB (a : AccumulatorDecl D) : Bool :=
  decide (1 ≤ a.kernZahl) && decide (1 ≤ a.breite) &&
  akkuGueltigB a.op a.lo a.hi a.breite &&
  akkuBreitePasstB a.vorzeichen a.lo a.hi a.breite &&
  (List.finRange a.kernZahl).all (fun i => decide (D.gtyp (a.zellen i) = Ty.int a.lo a.hi)) &&
  injFinB a.zellen && injFinB a.sperren &&
  decide (a.aktualisiere ≠ a.falte)

/-- The Bool decides descriptor validity. -/
theorem akkuOkB_iff {a : AccumulatorDecl D} : akkuOkB a = true ↔ akkuOk D a := by
  unfold akkuOkB akkuOk
  simp only [Bool.and_eq_true, decide_eq_true_eq, akkuGueltigB_iff, akkuBreitePasstB_iff,
    finRangeAll_iff, injFinB_iff, and_assoc]

/-! ## 3. Lock-rank order for the index-order fold -/

/-- **Rank order of the cell locks**: ranks grow strictly with the cell
    index, so the reduction's index-order acquisition cannot deadlock. -/
def akkuRangOrdnung (a : AccumulatorDecl D) : Prop :=
  ∀ i j : Fin a.kernZahl, i.val < j.val → D.rang (a.sperren i) < D.rang (a.sperren j)

/-- The rank order, decided. -/
def akkuRangOrdnungB (a : AccumulatorDecl D) : Bool :=
  (List.finRange a.kernZahl).all fun i =>
    (List.finRange a.kernZahl).all fun j =>
      decide (i.val < j.val → D.rang (a.sperren i) < D.rang (a.sperren j))

/-- The Bool decides the rank order. -/
theorem akkuRangOrdnungB_iff {a : AccumulatorDecl D} :
    akkuRangOrdnungB a = true ↔ akkuRangOrdnung a := by
  unfold akkuRangOrdnungB akkuRangOrdnung
  constructor
  · intro h i j hij
    have h1 := (finRangeAll_iff).mp ((finRangeAll_iff).mp h i) j
    simp only [decide_eq_true_eq] at h1
    exact h1 hij
  · intro h
    exact (finRangeAll_iff).mpr fun i => (finRangeAll_iff).mpr fun j => by
      simp only [decide_eq_true_eq]
      exact h i j

/-! ## 4. The admission -/

/-- **Per-declaration admission**: descriptor validity, one exclusive lock
    per private cell, storage privacy (no other body reads or writes a
    cell), the exact core-query shape, the update's queried core with its
    confined and floored call graph, the reduction's read-only floored
    graph, the connected core query (shape, hardware provenance and the
    wrapper's foreign bind) and the lock-rank order for the index-order
    fold. Complete call graphs are the global `abgAlleB` (already in
    `Akzeptiert`) together with these per-graph body checks; semantic query,
    range and quiescence facts are source-derived user duties, not Bool
    checks. -/
def akkuZulaessig (P : Programm D) (fs : List D.Fn) (a : AccumulatorDecl D) : Prop :=
  akkuOk D a ∧
  (∀ i, D.gbraucht (a.zellen i) = [Sum.inl (a.sperren i)]) ∧
  (∀ f, f ≠ a.aktualisiere → f ≠ a.falte → ∀ i,
    TraegerSchreibt f (.inr (a.zellen i)) = false ∧
    .inr (a.zellen i) ∉ fussOrteG P f) ∧
  (D.params a.kernAbfrage = [] ∧
    D.erg a.kernAbfrage = some (Ty.int 0 ((a.kernZahl : Int) - 1)) ∧
    D.gruende a.kernAbfrage = 0 ∧
    ∀ c, TraegerSchreibt a.kernAbfrage c = false) ∧
  (reachB P fs a.aktualisiere a.kernAbfrage = true ∧
    (∀ f, reachB P fs a.aktualisiere f = true →
      (∀ c, TraegerSchreibt f c = true → ∃ i, c = .inr (a.zellen i)) ∧
      mE (bodenM f) (P.rumpf f) = true) ∧
    D.params a.aktualisiere = [Ty.int a.lo a.hi] ∧ D.erg a.aktualisiere = none) ∧
  (D.params a.falte = [] ∧ D.erg a.falte = some (Ty.int a.lo a.hi) ∧
    ∀ f, reachB P fs a.falte f = true →
      (∀ c, TraegerSchreibt f c = false) ∧
      mE (bodenM f) (P.rumpf f) = true) ∧
  (∃ q, KernAbfrageVerbunden P a q) ∧
  akkuRangOrdnung a

/-- All cells of the admission, as one list. -/
def alleZellen (A : List (AccumulatorDecl D)) : List D.Glob :=
  A.flatMap fun a => (List.finRange a.kernZahl).map a.zellen

/-- All locks of the admission, as one list. -/
def alleSperren (A : List (AccumulatorDecl D)) : List D.Lock :=
  A.flatMap fun a => (List.finRange a.kernZahl).map a.sperren

/-- **The accumulator admission**: every declaration is admitted, and cells
    and locks are globally distinct (each carrier its own private cell and
    lock, across all accumulators). -/
def AccumulatorAdmission (P : Programm D) (fs : List D.Fn)
    (A : List (AccumulatorDecl D)) : Prop :=
  (∀ a ∈ A, akkuZulaessig P fs a) ∧ (alleZellen A).Nodup ∧ (alleSperren A).Nodup

/-- Admission of the empty list holds vacuously. -/
theorem accumulatorAdmission_leer (P : Programm D) (fs : List D.Fn) :
    AccumulatorAdmission P fs [] := by
  refine ⟨fun a ha => absurd ha List.not_mem_nil, ?_, ?_⟩ <;> simp only [alleZellen, alleSperren,
    List.flatMap_nil, List.nodup_nil]

/-! ## 5. The Bool -/

/-- One declaration, decided (over the member lists `fs`/`tabs`/`globs` and
    the listed query axioms `qs`). -/
def akkuEinzelB (P : Programm D) (fs : List D.Fn) (tabs : List D.Tab)
    (globs : List D.Glob) (qs : List D.Ax) (a : AccumulatorDecl D) : Bool :=
  akkuOkB a &&
  (List.finRange a.kernZahl).all
    (fun i => decide (D.gbraucht (a.zellen i) = [Sum.inl (a.sperren i)])) &&
  fs.all (fun f => decide (f = a.aktualisiere) || decide (f = a.falte) ||
    ((List.finRange a.kernZahl).all fun i =>
      decide (TraegerSchreibt f (.inr (a.zellen i)) = false) &&
      decide (.inr (a.zellen i) ∉ fussOrteG P f))) &&
  (decide (D.params a.kernAbfrage = []) &&
    decide (D.erg a.kernAbfrage = some (Ty.int 0 ((a.kernZahl : Int) - 1))) &&
    decide (D.gruende a.kernAbfrage = 0) &&
    tabs.all (fun t => decide (TraegerSchreibt a.kernAbfrage (.inl t) = false)) &&
    globs.all (fun g => decide (TraegerSchreibt a.kernAbfrage (.inr g) = false))) &&
  (reachB P fs a.aktualisiere a.kernAbfrage &&
    fs.all (fun f => !(reachB P fs a.aktualisiere f) ||
      (tabs.all (fun t => decide (TraegerSchreibt f (.inl t) = false)) &&
      globs.all (fun g => !(TraegerSchreibt f (.inr g)) ||
        (List.finRange a.kernZahl).any fun i =>
          decide ((.inr g : D.Tab ⊕ D.Glob) = .inr (a.zellen i))) &&
      mE (bodenM f) (P.rumpf f))) &&
    decide (D.params a.aktualisiere = [Ty.int a.lo a.hi]) &&
    decide (D.erg a.aktualisiere = none)) &&
  (decide (D.params a.falte = []) &&
    decide (D.erg a.falte = some (Ty.int a.lo a.hi)) &&
    fs.all (fun f => !(reachB P fs a.falte f) ||
      (tabs.all (fun t => decide (TraegerSchreibt f (.inl t) = false)) &&
      globs.all (fun g => decide (TraegerSchreibt f (.inr g) = false)) &&
      mE (bodenM f) (P.rumpf f)))) &&
  qs.any (fun q => kernAbfrageEinzelB P tabs globs a q) &&
  akkuRangOrdnungB a

/-- One declaration: the Bool decides the admission and the listed query. -/
theorem akkuEinzelB_iff {P : Programm D} {fs : List D.Fn} {tabs : List D.Tab}
    {globs : List D.Glob} {qs : List D.Ax} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hT : ∀ t : D.Tab, t ∈ tabs) (hG : ∀ g : D.Glob, g ∈ globs)
    {a : AccumulatorDecl D} : akkuEinzelB P fs tabs globs qs a = true ↔
      (akkuZulaessig P fs a ∧ ∃ q ∈ qs, KernAbfrageVerbunden P a q) := by
  unfold akkuEinzelB akkuZulaessig
  constructor
  · intro h
    rw [Bool.and_eq_true] at h; obtain ⟨h, h7⟩ := h
    rw [Bool.and_eq_true] at h; obtain ⟨h, h6⟩ := h
    rw [Bool.and_eq_true] at h; obtain ⟨h, h5⟩ := h
    rw [Bool.and_eq_true] at h; obtain ⟨h, h4⟩ := h
    rw [Bool.and_eq_true] at h; obtain ⟨h, h3⟩ := h
    rw [Bool.and_eq_true] at h; obtain ⟨h, h2⟩ := h
    rw [Bool.and_eq_true] at h; obtain ⟨h0, h1⟩ := h
    obtain ⟨q, hmem, hqB⟩ := List.any_eq_true.mp h6
    have hq : KernAbfrageVerbunden P a q := (kernAbfrageEinzelB_iff hT hG).mp hqB
    refine ⟨⟨(akkuOkB_iff).mp h0, fun i => ?_, fun f hf1 hf2 i => ?_, ?_, ?_, ?_,
      ⟨q, hq⟩, (akkuRangOrdnungB_iff).mp h7⟩, q, hmem, hq⟩
    · have := (finRangeAll_iff).mp h1 i
      simp only [decide_eq_true_eq] at this
      exact this
    · have h2f := (List.all_eq_true.mp h2) f (hvoll f)
      simp only [Bool.or_eq_true, decide_eq_true_eq] at h2f
      rcases h2f with (rfl | rfl) | h2f
      · exact absurd rfl hf1
      · exact absurd rfl hf2
      · have h2i := (finRangeAll_iff).mp h2f i
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h2i
        exact h2i
    · simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h3
      obtain ⟨h31, h32, h33, h34, h35⟩ := h3
      refine ⟨h31, h32, h33, fun c => ?_⟩
      cases c with
      | inl t =>
        have := (List.all_eq_true.mp h34) t (hT t)
        simp only [decide_eq_true_eq] at this
        exact this
      | inr g =>
        have := (List.all_eq_true.mp h35) g (hG g)
        simp only [decide_eq_true_eq] at this
        exact this
    · simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h4
      obtain ⟨h41, h42, h43, h44⟩ := h4
      refine ⟨h41, fun f hf => ?_, h43, h44⟩
      · have h := (List.all_eq_true.mp h42) f (hvoll f)
        rw [hf] at h
        simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at h
        obtain ⟨⟨hct, hcg⟩, hm⟩ := h
        refine ⟨fun c hcc => ?_, hm⟩
        cases c with
        | inl t =>
          have ht := (List.all_eq_true.mp hct) t (hT t)
          simp only [decide_eq_true_eq] at ht
          rw [hcc] at ht
          exact absurd ht (by decide)
        | inr g =>
          have hg := (List.all_eq_true.mp hcg) g (hG g)
          rw [hcc] at hg
          simp only [Bool.not_true, Bool.false_or] at hg
          obtain ⟨i, _, heq⟩ := List.any_eq_true.mp hg
          simp only [decide_eq_true_eq] at heq
          exact ⟨i, heq⟩
    · simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h5
      obtain ⟨h51, h52, h53⟩ := h5
      refine ⟨h51, h52, fun f hf => ?_⟩
      have h := (List.all_eq_true.mp h53) f (hvoll f)
      rw [hf] at h
      simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at h
      obtain ⟨⟨hct, hcg⟩, hm⟩ := h
      refine ⟨fun c => ?_, hm⟩
      cases c with
      | inl t =>
        have := (List.all_eq_true.mp hct) t (hT t)
        simp only [decide_eq_true_eq] at this
        exact this
      | inr g =>
        have := (List.all_eq_true.mp hcg) g (hG g)
        simp only [decide_eq_true_eq] at this
        exact this
  · rintro ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7⟩, q, hmem, hq⟩
    have b0 : akkuOkB a = true := (akkuOkB_iff).mpr h0
    have b1 : (List.finRange a.kernZahl).all
        (fun i => decide (D.gbraucht (a.zellen i) = [Sum.inl (a.sperren i)])) = true :=
      (finRangeAll_iff).mpr fun i => by
        simp only [decide_eq_true_eq]
        exact h1 i
    have b2 : fs.all (fun f => decide (f = a.aktualisiere) || decide (f = a.falte) ||
        ((List.finRange a.kernZahl).all fun i =>
          decide (TraegerSchreibt f (.inr (a.zellen i)) = false) &&
          decide (.inr (a.zellen i) ∉ fussOrteG P f))) = true := by
      refine List.all_eq_true.mpr fun f _ => ?_
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      by_cases he1 : f = a.aktualisiere
      · exact Or.inl (Or.inl he1)
      · by_cases he2 : f = a.falte
        · exact Or.inl (Or.inr he2)
        · exact Or.inr ((finRangeAll_iff).mpr fun i => by
            simp only [Bool.and_eq_true, decide_eq_true_eq]
            exact h2 f he1 he2 i)
    have b3 : (decide (D.params a.kernAbfrage = []) &&
        decide (D.erg a.kernAbfrage = some (Ty.int 0 ((a.kernZahl : Int) - 1))) &&
        decide (D.gruende a.kernAbfrage = 0) &&
        tabs.all (fun t => decide (TraegerSchreibt a.kernAbfrage (.inl t) = false)) &&
        globs.all (fun g => decide (TraegerSchreibt a.kernAbfrage (.inr g) = false))) = true := by
      obtain ⟨h31, h32, h33, h34⟩ := h3
      have e1 : decide (D.params a.kernAbfrage = []) = true := by simpa using h31
      have e2 : decide (D.erg a.kernAbfrage =
        some (Ty.int 0 ((a.kernZahl : Int) - 1))) = true := by simpa using h32
      have e3 : decide (D.gruende a.kernAbfrage = 0) = true := by simpa using h33
      rw [e1, e2, e3]
      simp only [Bool.true_and, Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · exact List.all_eq_true.mpr fun t _ => by
          simp only [decide_eq_true_eq]
          exact h34 (.inl t)
      · exact List.all_eq_true.mpr fun g _ => by
          simp only [decide_eq_true_eq]
          exact h34 (.inr g)
    have b4 : (reachB P fs a.aktualisiere a.kernAbfrage &&
        fs.all (fun f => !(reachB P fs a.aktualisiere f) ||
          (tabs.all (fun t => decide (TraegerSchreibt f (.inl t) = false)) &&
          globs.all (fun g => !(TraegerSchreibt f (.inr g)) ||
            (List.finRange a.kernZahl).any fun i =>
              decide ((.inr g : D.Tab ⊕ D.Glob) = .inr (a.zellen i))) &&
          mE (bodenM f) (P.rumpf f))) &&
        decide (D.params a.aktualisiere = [Ty.int a.lo a.hi]) &&
        decide (D.erg a.aktualisiere = none)) = true := by
      obtain ⟨h41, h42, h43, h44⟩ := h4
      have e3 : decide (D.params a.aktualisiere = [Ty.int a.lo a.hi]) = true := by
        simpa using h43
      have e4 : decide (D.erg a.aktualisiere = none) = true := by simpa using h44
      rw [e3, e4]
      simp only [Bool.and_eq_true, and_true]
      refine ⟨h41, ?_⟩
      refine List.all_eq_true.mpr fun f _ => ?_
      simp only [Bool.or_eq_true]
      cases hf' : reachB P fs a.aktualisiere f with
      | false => exact Or.inl rfl
      | true =>
        obtain ⟨hcc, hm⟩ := h42 f hf'
        apply Or.inr
        simp only [Bool.and_eq_true]
        refine ⟨⟨?_, ?_⟩, hm⟩
        · refine List.all_eq_true.mpr fun t _ => ?_
          simp only [decide_eq_true_eq]
          cases hw : TraegerSchreibt f (.inl t) with
          | true =>
            obtain ⟨i, hi⟩ := hcc (.inl t) hw
            cases hi
          | false => rfl
        · refine List.all_eq_true.mpr fun g _ => ?_
          simp only [Bool.or_eq_true]
          cases hT' : TraegerSchreibt f (.inr g) with
          | false => exact Or.inl rfl
          | true =>
            obtain ⟨i, hi⟩ := hcc _ hT'
            exact Or.inr (List.any_eq_true.mpr ⟨i, List.mem_finRange i, decide_eq_true hi⟩)
    have b5 : (decide (D.params a.falte = []) &&
        decide (D.erg a.falte = some (Ty.int a.lo a.hi)) &&
        fs.all (fun f => !(reachB P fs a.falte f) ||
          (tabs.all (fun t => decide (TraegerSchreibt f (.inl t) = false)) &&
          globs.all (fun g => decide (TraegerSchreibt f (.inr g) = false)) &&
          mE (bodenM f) (P.rumpf f)))) = true := by
      obtain ⟨h51, h52, h53⟩ := h5
      have e1 : decide (D.params a.falte = []) = true := by simpa using h51
      have e2 : decide (D.erg a.falte = some (Ty.int a.lo a.hi)) = true := by
        simpa using h52
      rw [e1, e2]
      simp only [Bool.true_and]
      refine List.all_eq_true.mpr fun f _ => ?_
      simp only [Bool.or_eq_true]
      cases hf' : reachB P fs a.falte f with
      | false => exact Or.inl rfl
      | true =>
        obtain ⟨hcc, hm⟩ := h53 f hf'
        apply Or.inr
        simp only [Bool.and_eq_true]
        exact ⟨⟨List.all_eq_true.mpr fun t _ => decide_eq_true (hcc _),
          List.all_eq_true.mpr fun g _ => decide_eq_true (hcc _)⟩, hm⟩
    have b6 : qs.any (fun q => kernAbfrageEinzelB P tabs globs a q) = true :=
      List.any_eq_true.mpr ⟨q, hmem, (kernAbfrageEinzelB_iff hT hG).mpr hq⟩
    have b7 : akkuRangOrdnungB a = true := (akkuRangOrdnungB_iff).mpr h7
    rw [b0, b1, b2, b3, b4, b5, b6, b7]
    rfl

/-! ## 6. The admission Bool -/

/-- **The accumulator admission, decided** (over the member lists and the
    listed query axioms). -/
def accumulatorB (P : Programm D) (fs : List D.Fn) (tabs : List D.Tab)
    (globs : List D.Glob) (qs : List D.Ax) (A : List (AccumulatorDecl D)) : Bool :=
  A.all (fun a => akkuEinzelB P fs tabs globs qs a) &&
  decide ((alleZellen A).Nodup) && decide ((alleSperren A).Nodup)

/-- The Bool decides the admission and the listed queries. -/
theorem accumulatorB_iff {P : Programm D} {fs : List D.Fn} {tabs : List D.Tab}
    {globs : List D.Glob} {qs : List D.Ax} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hT : ∀ t : D.Tab, t ∈ tabs) (hG : ∀ g : D.Glob, g ∈ globs)
    {A : List (AccumulatorDecl D)} :
    accumulatorB P fs tabs globs qs A = true ↔
      (AccumulatorAdmission P fs A ∧
        ∀ a ∈ A, ∃ q ∈ qs, KernAbfrageVerbunden P a q) := by
  unfold accumulatorB AccumulatorAdmission
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨fun a ha => ((akkuEinzelB_iff hvoll hT hG).mp
      ((List.all_eq_true.mp h1) a ha)).1, h2, h3⟩, fun a ha => ?_⟩
    exact ((akkuEinzelB_iff hvoll hT hG).mp ((List.all_eq_true.mp h1) a ha)).2
  · rintro ⟨⟨h1, h2, h3⟩, hq⟩
    exact ⟨⟨List.all_eq_true.mpr fun a ha => (akkuEinzelB_iff hvoll hT hG).mpr
      ⟨h1 a ha, hq a ha⟩, h2⟩, h3⟩

/-- Admission of the empty list is decided. -/
theorem accumulatorB_leer {P : Programm D} {fs : List D.Fn} {tabs : List D.Tab}
    {globs : List D.Glob} {qs : List D.Ax} :
    accumulatorB P fs tabs globs qs [] = true := by
  unfold accumulatorB
  simp only [List.all_nil, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
  constructor <;> simp only [alleZellen, alleSperren, List.flatMap_nil, List.nodup_nil]

#print axioms Gabbro.Grammatik.Kernzelle.akkuGueltigB_iff
#print axioms Gabbro.Grammatik.Kernzelle.akkuBreitePasstB_iff
#print axioms Gabbro.Grammatik.Kernzelle.injFinB_iff
#print axioms Gabbro.Grammatik.Kernzelle.finRangeAll_iff
#print axioms Gabbro.Grammatik.Kernzelle.akkuOkB_iff
#print axioms Gabbro.Grammatik.Kernzelle.akkuEinzelB_iff
#print axioms Gabbro.Grammatik.Kernzelle.accumulatorB_iff
#print axioms Gabbro.Grammatik.Kernzelle.accumulatorB_leer
#print axioms Gabbro.Grammatik.Kernzelle.accumulatorAdmission_leer

end Gabbro.Grammatik.Kernzelle
