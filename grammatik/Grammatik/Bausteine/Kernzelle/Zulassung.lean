module

public import Grammatik.Bausteine.Kernzelle.Verlauf
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiOrte
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtMehrfaden

@[expose] public section



namespace Gabbro.Grammatik.Kernzelle

open Gabbro.Grammatik Gabbro.Grammatik.Isabelle.AccumulatesMonoid Gabbro.Grammatik.Zielsatz

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
  | add => simp only [akkuGueltigB, akkuGueltig, Bool.and_eq_true, decide_eq_true_eq]
  | or => simp only [akkuGueltigB, akkuGueltig, Bool.and_eq_true, decide_eq_true_eq]
  | and => simp only [akkuGueltigB, akkuGueltig, Bool.and_eq_true, decide_eq_true_eq]

/-- The width fit, decided. -/
def akkuBreitePasstB (v : Bool) (lo hi : Int) (w : Nat) : Bool :=
  if v then decide (-(2 ^ (w - 1) : Int) ≤ lo) && decide (hi < 2 ^ (w - 1))
  else decide (0 ≤ lo) && decide (hi < 2 ^ w)

/-- The Bool decides the width fit. -/
theorem akkuBreitePasstB_iff {v : Bool} {lo hi : Int} {w : Nat} :
    akkuBreitePasstB v lo hi w = true ↔ akkuBreitePasst v lo hi w := by
  cases v with
  | true => simp only [akkuBreitePasstB, akkuBreitePasst, Bool.and_eq_true, decide_eq_true_eq]
  | false => simp only [akkuBreitePasstB, akkuBreitePasst, Bool.and_eq_true, decide_eq_true_eq]

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
    have h1 := h i (List.mem_finRange i) j (List.mem_finRange j)
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h1
    rcases h1 with heq | hne
    · exact heq
    · exact absurd hij hne
  · intro h i _ j _
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
    finRangeAll_iff, injFinB_iff]

/-! ## 3. The admission -/

/-- **Per-declaration admission**: descriptor validity, one exclusive lock
    per private cell, storage privacy (no other body reads or writes a
    cell), the exact core-query shape, the update's queried core with its
    confined and floored call graph, and the reduction's read-only floored
    graph. Complete call graphs are the global `abgAlleB` (already in
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
      mE (bodenM f) (P.rumpf f) = true)

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

/-! ## 4. The Bool -/

/-- One declaration, decided (over the member lists `fs`/`cs`). -/
def akkuEinzelB (P : Programm D) (fs : List D.Fn) (cs : List (D.Tab ⊕ D.Glob))
    (a : AccumulatorDecl D) : Bool :=
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
    cs.all (fun c => decide (TraegerSchreibt a.kernAbfrage c = false))) &&
  (reachB P fs a.aktualisiere a.kernAbfrage &&
    fs.all (fun f => !(reachB P fs a.aktualisiere f) ||
      (cs.all (fun c => !(TraegerSchreibt f c) ||
        (List.finRange a.kernZahl).any fun i => decide (c = .inr (a.zellen i))) &&
      mE (bodenM f) (P.rumpf f))) &&
    decide (D.params a.aktualisiere = [Ty.int a.lo a.hi]) &&
    decide (D.erg a.aktualisiere = none)) &&
  (decide (D.params a.falte = []) &&
    decide (D.erg a.falte = some (Ty.int a.lo a.hi)) &&
    fs.all (fun f => !(reachB P fs a.falte f) ||
      (cs.all (fun c => decide (TraegerSchreibt f c = false)) &&
      mE (bodenM f) (P.rumpf f))))

/-- One declaration: the Bool decides the admission. -/
theorem akkuEinzelB_iff {P : Programm D} {fs : List D.Fn} {cs : List (D.Tab ⊕ D.Glob)}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs)
    {a : AccumulatorDecl D} : akkuEinzelB P fs cs a = true ↔ akkuZulaessig P fs a := by
  unfold akkuEinzelB akkuZulaessig
  constructor
  · intro h
    rw [Bool.and_eq_true] at h; obtain ⟨h0, h⟩ := h
    rw [Bool.and_eq_true] at h; obtain ⟨h1, h⟩ := h
    rw [Bool.and_eq_true] at h; obtain ⟨h2, h⟩ := h
    rw [Bool.and_eq_true] at h; obtain ⟨h3, h⟩ := h
    rw [Bool.and_eq_true] at h; obtain ⟨h4, h5⟩ := h
    refine ⟨(akkuOkB_iff).mp h0, fun i => ?_, fun f hf1 hf2 i => ?_, ?_, ?_, ?_⟩
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
    · obtain ⟨h31, h32, h33, h34⟩ := h3
      simp only [decide_eq_true_eq] at h31 h32 h33
      refine ⟨h31, h32, h33, fun c => ?_⟩
      have := (List.all_eq_true.mp h34) c (hcs c)
      simp only [decide_eq_true_eq] at this
      exact this
    · rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h4
      obtain ⟨h41, h42, h43, h44⟩ := h4
      refine ⟨h41, fun f hf => ?_, h43, h44⟩
      · simp only [decide_eq_true_eq] at h43 h44
        have h := (List.all_eq_true.mp h42) f (hvoll f)
        rw [hf] at h
        simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at h
        obtain ⟨hc, hm⟩ := h
        refine ⟨fun c hcc => ?_, hm⟩
        have hcc' := (List.all_eq_true.mp hc) c (hcs c)
        rw [hcc] at hcc'
        simp only [Bool.not_true, Bool.false_or] at hcc'
        obtain ⟨i, _, heq⟩ := List.any_eq_true.mp hcc'
        simp only [decide_eq_true_eq] at heq
        exact ⟨i, heq⟩
    · obtain ⟨h51, h52, h53⟩ := h5
      simp only [decide_eq_true_eq] at h51 h52
      refine ⟨h51, h52, fun f hf => ?_⟩
      have h := (List.all_eq_true.mp h53) f (hvoll f)
      rw [hf] at h
      simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at h
      obtain ⟨hc, hm⟩ := h
      refine ⟨fun c => ?_, hm⟩
      have := (List.all_eq_true.mp hc) c (hcs c)
      simp only [decide_eq_true_eq] at this
      exact this
  · rintro ⟨h0, h1, h2, h3, h4, h5⟩
    have b0 : akkuOkB a = true := (akkuOkB_iff).mpr h0
    have b1 : (List.finRange a.kernZahl).all
        (fun i => decide (D.gbraucht (a.zellen i) = [Sum.inl (a.sperren i)])) = true :=
      (finRangeAll_iff).mpr fun i => by simp only [decide_eq_true_eq]; exact h1 i
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
        cs.all (fun c => decide (TraegerSchreibt a.kernAbfrage c = false))) = true := by
      obtain ⟨h31, h32, h33, h34⟩ := h3
      have e1 : decide (D.params a.kernAbfrage = []) = true := by simpa using h31
      have e2 : decide (D.erg a.kernAbfrage =
        some (Ty.int 0 ((a.kernZahl : Int) - 1))) = true := by simpa using h32
      have e3 : decide (D.gruende a.kernAbfrage = 0) = true := by simpa using h33
      rw [e1, e2, e3]
      simp only [Bool.true_and]
      exact List.all_eq_true.mpr fun c _ => h34 c
    have b4 : (reachB P fs a.aktualisiere a.kernAbfrage &&
        fs.all (fun f => !(reachB P fs a.aktualisiere f) ||
          (cs.all (fun c => !(TraegerSchreibt f c) ||
            (List.finRange a.kernZahl).any fun i => decide (c = .inr (a.zellen i))) &&
          mE (bodenM f) (P.rumpf f))) &&
        decide (D.params a.aktualisiere = [Ty.int a.lo a.hi]) &&
        decide (D.erg a.aktualisiere = none)) = true := by
      obtain ⟨h41, h42, h43, h44⟩ := h4
      have e3 : decide (D.params a.aktualisiere = [Ty.int a.lo a.hi]) = true := by
        simpa using h43
      have e4 : decide (D.erg a.aktualisiere = none) = true := by simpa using h44
      rw [e3, e4]
      simp only [Bool.true_and, Bool.and_eq_true]
      refine ⟨h41, ?_⟩
      refine List.all_eq_true.mpr fun f _ => ?_
      simp only [Bool.or_eq_true]
      cases hf' : reachB P fs a.aktualisiere f with
      · exact Or.inl rfl
      · obtain ⟨hcc, hm⟩ := h42 f hf'
        refine Or.inr ⟨?_, hm⟩
        refine List.all_eq_true.mpr fun c _ => ?_
        simp only [Bool.or_eq_true]
        cases hT : TraegerSchreibt f c with
        · exact Or.inl rfl
        · obtain ⟨i, hi⟩ := hcc c hT
          exact Or.inr (List.any_eq_true.mpr ⟨i, List.mem_finRange i, decide_eq_true hi⟩)
    have b5 : (decide (D.params a.falte = []) &&
        decide (D.erg a.falte = some (Ty.int a.lo a.hi)) &&
        fs.all (fun f => !(reachB P fs a.falte f) ||
          (cs.all (fun c => decide (TraegerSchreibt f c = false)) &&
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
      · exact Or.inl rfl
      · obtain ⟨hcc, hm⟩ := h53 f hf'
        exact Or.inr ⟨List.all_eq_true.mpr fun c _ => hcc c, hm⟩
    rw [b0, b1, b2, b3, b4, b5]

/-- **The accumulator admission, decided** (over the member lists). -/
def accumulatorB (P : Programm D) (fs : List D.Fn) (cs : List (D.Tab ⊕ D.Glob))
    (A : List (AccumulatorDecl D)) : Bool :=
  A.all (fun a => akkuEinzelB P fs cs a) &&
  decide ((alleZellen A).Nodup) && decide ((alleSperren A).Nodup)

/-- The Bool decides the admission. -/
theorem accumulatorB_iff {P : Programm D} {fs : List D.Fn} {cs : List (D.Tab ⊕ D.Glob)}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs)
    {A : List (AccumulatorDecl D)} :
    accumulatorB P fs cs A = true ↔ AccumulatorAdmission P fs A := by
  unfold accumulatorB AccumulatorAdmission
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun a ha => (akkuEinzelB_iff hvoll hcs).mp ((List.all_eq_true.mp h1) a ha), h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨List.all_eq_true.mpr fun a ha => (akkuEinzelB_iff hvoll hcs).mpr (h1 a ha), h2, h3⟩

/-- Admission of the empty list is decided. -/
theorem accumulatorB_leer {P : Programm D} {fs : List D.Fn} {cs : List (D.Tab ⊕ D.Glob)} :
    accumulatorB P fs cs [] = true := by
  unfold accumulatorB
  simp only [List.all_nil, Bool.true_and, decide_eq_true_eq]
  constructor <;> simp only [alleZellen, alleSperren, List.flatMap_nil, List.nodup_nil]

/-! ## 5. Neutral initialization at the start memory -/

/-- A cell value at the start memory, checked against the accumulator's
    type and neutral element (refused outside the declared type). -/
def spGlobIntB (sp : Speicher D) (g : D.Glob) (op : AccOperator) (lo hi : Int)
    (w : Nat) : Bool :=
  if h : D.gtyp g = Ty.int lo hi then
    decide ((h ▸ sp.globs g).n = neutralInt op lo hi w)
  else false

/-- **Neutral initialization**: every cell holds the neutral element in the
    declared start memory (checked beside `AkzeptiertSpecX`, like
    `BesitzStart`). -/
def AkkuStart (E : Einheit D) (A : List (AccumulatorDecl D)) : Prop :=
  ∀ a ∈ A, ∀ hok : akkuOk D a, ∀ i : Fin a.kernZahl,
    (akkuZellTyp hok i ▸ E.sp0.globs (a.zellen i)).n =
      neutralInt a.op a.lo a.hi a.breite

/-- Neutral initialization, decided. -/
def akkuStartB (E : Einheit D) (A : List (AccumulatorDecl D)) : Bool :=
  A.all fun a => akkuOkB a &&
    (List.finRange a.kernZahl).all fun i =>
      spGlobIntB E.sp0 (a.zellen i) a.op a.lo a.hi a.breite

/-- The Bool decides neutral initialization. -/
theorem akkuStartB_sound {E : Einheit D} {A : List (AccumulatorDecl D)}
    (h : akkuStartB E A = true) : AkkuStart E A := by
  intro a ha hok i
  have h1 := (List.all_eq_true.mp h) a ha
  simp only [Bool.and_eq_true] at h1
  obtain ⟨_, hcells⟩ := h1
  have h2 := (finRangeAll_iff).mp hcells i
  unfold spGlobIntB at h2
  rw [dif_pos (akkuZellTyp hok i)] at h2
  simp only [decide_eq_true_eq] at h2
  exact h2

/-- On the empty list, neutral initialization holds vacuously. -/
theorem akkuStartB_leer (E : Einheit D) : akkuStartB E [] = true := by
  simp only [akkuStartB, List.all_nil]

/-! ## 6. The idle-root transfer -/

/-- Signature facts ride `some` (types shift by `tyR`, which fixes `int`). -/
theorem params_mitRuhe_some (f : D.Fn) :
    D.mitRuhe.params (some f) = (D.params f).map tyR := rfl

theorem erg_mitRuhe_some (f : D.Fn) :
    D.mitRuhe.erg (some f) = (D.erg f).map tyR := rfl

theorem gruende_mitRuhe_some (f : D.Fn) :
    D.mitRuhe.gruende (some f) = D.gruende f := rfl

theorem gtyp_mitRuhe (g : D.Glob) : D.mitRuhe.gtyp g = tyR (D.gtyp g) := rfl

/-- The idle root writes nothing. -/
theorem traegerSchreibt_mitRuhe_ruhe (P : Programm D) (c : D.mitRuhe.Tab ⊕ D.mitRuhe.Glob) :
    TraegerSchreibt P.mitRuhe none c = false := by
  cases c <;> rfl

/-- Transfer of one declaration's admission to the idle-root program. -/
theorem akkuZulaessig_mitRuhe (P : Programm D) {fs : List D.Fn}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (hAbg : ∀ w, AbgK P fs (reachB P fs w))
    {a : AccumulatorDecl D} (h : akkuZulaessig P fs a) :
    akkuZulaessig P.mitRuhe (fsRuhe fs) (AccumulatorDecl.mitRuhe a) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, fun i => ?_, fun f' hf1 hf2 i => ?_, ?_, ?_, ?_⟩
  · refine ⟨h0.1, h0.2.1, h0.2.2.1, h0.2.2.2.1, fun i => ?_,
      fun i j hij => h0.2.2.2.2.2.1 hij, fun i j hij => h0.2.2.2.2.2.2.1 hij,
      fun hcon => h0.2.2.2.2.2.2.2 (Option.some_injective hcon)⟩
    show D.mitRuhe.gtyp (a.zellen i) = Ty.int a.lo a.hi
    rw [gtyp_mitRuhe, h0.2.2.2.2.1 i]
  · show D.mitRuhe.gbraucht (a.zellen i) = [Sum.inl (a.sperren i)]
    exact h1 i
  · cases f' with
    | none =>
        refine ⟨traegerSchreibt_mitRuhe_ruhe P _, ?_⟩
        rw [fussOrteG_mitRuhe_ruhe P]
        exact List.not_mem_nil _
    | some f =>
        have hf1' : f ≠ a.aktualisiere := fun hcon => hf1 (congrArg some hcon)
        have hf2' : f ≠ a.falte := fun hcon => hf2 (congrArg some hcon)
        obtain ⟨hw, hf⟩ := h2 f hf1' hf2' i
        refine ⟨?_, ?_⟩
        · show TraegerSchreibt P.mitRuhe (some f) _ = false
          simpa only [traegerSchreibt_mitRuhe] using hw
        · show _ ∉ fussOrteG P.mitRuhe (some f)
          rw [fussOrteG_mitRuhe]
          exact hf
  · obtain ⟨h31, h32, h33, h34⟩ := h3
    refine ⟨?_, ?_, ?_, fun c => ?_⟩
    · show D.mitRuhe.params (some a.kernAbfrage) = []
      rw [params_mitRuhe_some, h31]
    · show D.mitRuhe.erg (some a.kernAbfrage) = some (Ty.int 0 _)
      rw [erg_mitRuhe_some, h32]
    · show D.mitRuhe.gruende (some a.kernAbfrage) = 0
      rw [gruende_mitRuhe_some, h33]
    · show TraegerSchreibt P.mitRuhe (some a.kernAbfrage) c = false
      rw [traegerSchreibt_mitRuhe]
      exact h34 c
  · obtain ⟨h41, h42, h43, h44⟩ := h4
    refine ⟨?_, fun f' hf' => ?_, ?_, ?_⟩
    · show reachB P.mitRuhe (fsRuhe fs) (some a.aktualisiere) (some a.kernAbfrage) = true
      rw [reachB_mitRuhe P hvoll hAbg]
      exact h41
    · cases f' with
      | none =>
          rw [reachB_mitRuhe_nicht_ruhe P hAbg] at hf'
          cases hf'
      | some f =>
          obtain ⟨g, rfl, hg⟩ := reach_mitRuhe_cases P hvoll hAbg hf'
          obtain ⟨hcc, hm⟩ := h42 g hg
          refine ⟨fun c hc => ?_, ?_⟩
          · have hc' : TraegerSchreibt P g c = true := by
              simpa only [traegerSchreibt_mitRuhe] using hc
            obtain ⟨i, hi⟩ := hcc c hc'
            exact ⟨i, hi⟩
          · show mE (bodenM (some g)) (P.mitRuhe.rumpf (some g)) = true
            rw [rumpf_mitRuhe_mE]
            exact hm
    · show D.mitRuhe.params (some a.aktualisiere) = _
      rw [params_mitRuhe_some, h43]
    · show D.mitRuhe.erg (some a.aktualisiere) = _
      rw [erg_mitRuhe_some, h44]
  · obtain ⟨h51, h52, h53⟩ := h5
    refine ⟨?_, ?_, fun f' hf' => ?_⟩
    · show D.mitRuhe.params (some a.falte) = []
      rw [params_mitRuhe_some, h51]
    · show D.mitRuhe.erg (some a.falte) = _
      rw [erg_mitRuhe_some, h52]
    · cases f' with
      | none =>
          rw [reachB_mitRuhe_nicht_ruhe P hAbg] at hf'
          cases hf'
      | some f =>
          obtain ⟨g, rfl, hg⟩ := reach_mitRuhe_cases P hvoll hAbg hf'
          obtain ⟨hcc, hm⟩ := h53 g hg
          refine ⟨fun c => ?_, ?_⟩
          · have hc' : TraegerSchreibt P g c = false := by
              simpa only [traegerSchreibt_mitRuhe] using hcc c
            exact hc'
          · show mE (bodenM (some g)) (P.mitRuhe.rumpf (some g)) = true
            rw [rumpf_mitRuhe_mE]
            exact hm

/-- Transfer of the admission to the idle-root program. -/
theorem accumulatorAdmission_mitRuhe (P : Programm D) {fs : List D.Fn}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (hAbg : ∀ w, AbgK P fs (reachB P fs w))
    {A : List (AccumulatorDecl D)} (h : AccumulatorAdmission P fs A) :
    AccumulatorAdmission P.mitRuhe (fsRuhe fs) (A.map AccumulatorDecl.mitRuhe) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro a' ha'
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
    exact akkuZulaessig_mitRuhe P hvoll hAbg (h1 a ha)
  · -- cells ride the identity map
    have e : alleZellen (A.map AccumulatorDecl.mitRuhe) = alleZellen A := by
      simp only [alleZellen, List.flatMap_map, Function.comp_apply, mitRuhe_kernZahl,
        mitRuhe_zellen]
    rw [e]
    exact h2
  · have e : alleSperren (A.map AccumulatorDecl.mitRuhe) = alleSperren A := by
      simp only [alleSperren, List.flatMap_map, Function.comp_apply, mitRuhe_kernZahl,
        mitRuhe_sperren]
    rw [e]
    exact h3

#print axioms Gabbro.Grammatik.Kernzelle.akkuGueltigB_iff
#print axioms Gabbro.Grammatik.Kernzelle.akkuBreitePasstB_iff
#print axioms Gabbro.Grammatik.Kernzelle.injFinB_iff
#print axioms Gabbro.Grammatik.Kernzelle.finRangeAll_iff
#print axioms Gabbro.Grammatik.Kernzelle.akkuOkB_iff
#print axioms Gabbro.Grammatik.Kernzelle.akkuEinzelB_iff
#print axioms Gabbro.Grammatik.Kernzelle.accumulatorB_iff
#print axioms Gabbro.Grammatik.Kernzelle.accumulatorB_leer
#print axioms Gabbro.Grammatik.Kernzelle.accumulatorAdmission_leer
#print axioms Gabbro.Grammatik.Kernzelle.akkuStartB_sound
#print axioms Gabbro.Grammatik.Kernzelle.akkuStartB_leer
#print axioms Gabbro.Grammatik.Kernzelle.akkuZulaessig_mitRuhe
#print axioms Gabbro.Grammatik.Kernzelle.accumulatorAdmission_mitRuhe

end Gabbro.Grammatik.Kernzelle
