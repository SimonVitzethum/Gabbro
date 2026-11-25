/-
  File:      core/Core/Ast/Semantik/Runtime/Praedikat.lean
  Subject:   THE DECIDABLE INVARIANT LANGUAGE (MK-19 design step 2): comparisons and arithmetic over
             named cells and integer constants, closed under conjunction, disjunction and negation.

  A unit declares invariants as expressions of this language (`Praedikat`) instead of a free
  `Zustand → Prop` field. The denotation `Praedikat.gilt : Praedikat → Zustand → Prop` reads the
  unit's memory content (`s.initial`); every command of the current set is frame-only, so the
  denotation is preserved by every command step and the checker's footprint rule
  (`pruefeBefehlErhalt` in `Core/Ast/Semantik/Runtime/UnitInvarianten.lean`) decides preservation
  by disjointness of observed cells and write footprint. Memory commands (MK-04) populate
  `Befehl.schreibFussabdruck`; the stability lemma `haelt_stabil` already carries the rule.

  Evaluation `werteAus` is a plain `Bool` function and `werteAus_richtig` ties it to `haelt`;
  `pruefeStart`/`pruefeNeustart` decide the loader and crash-recovery premises of the safety
  induction on the memory plan. No Prop-valued field, no function parameter, no legacy.
-/
module

public import Core.Ast.Semantik.Runtime.Frame
public import Core.Ast.Semantik.Runtime.Speicherplan.Zelle
public import Core.Ast.Semantik.Runtime.Befehl
public import Core.Ast.Semantik.Runtime.Atom.Fussabdruck

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

/-- Arithmetic over named cells and integer constants. A cell `zelle z` reads the unit's memory
    content at `z`; the operators are the exact integer operations. -/
inductive Ausdruck where
  | konst (v : Int)
  | zelle (z : Zelle)
  | add (a b : Ausdruck)
  | sub (a b : Ausdruck)
  | mul (a b : Ausdruck)
  deriving DecidableEq, Repr

/-- The comparisons of the language. -/
inductive Vergleich where
  | eq
  | lt
  | le
  deriving DecidableEq, Repr

/-- Invariant predicates: one comparison, closed under conjunction, disjunction and negation. -/
inductive Praedikat where
  | vgl (op : Vergleich) (a b : Ausdruck)
  | und (a b : Praedikat)
  | oder (a b : Praedikat)
  | nicht (a : Praedikat)
  deriving DecidableEq, Repr

/-- The cells an expression reads. -/
def Ausdruck.zellen : Ausdruck → List Zelle
  | .konst _ => []
  | .zelle z => [z]
  | .add a b => a.zellen ++ b.zellen
  | .sub a b => a.zellen ++ b.zellen
  | .mul a b => a.zellen ++ b.zellen

/-- The cells a predicate observes: only writes to these cells can break it. -/
def Praedikat.beobachtet : Praedikat → List Zelle
  | .vgl _ a b => a.zellen ++ b.zellen
  | .und x y => x.beobachtet ++ y.beobachtet
  | .oder x y => x.beobachtet ++ y.beobachtet
  | .nicht x => x.beobachtet

/-- Evaluation of an expression against a memory content function. -/
def Ausdruck.wert : Ausdruck → (Zelle → Int) → Int
  | .konst v, _ => v
  | .zelle z, f => f z
  | .add a b, f => a.wert f + b.wert f
  | .sub a b, f => a.wert f - b.wert f
  | .mul a b, f => a.wert f * b.wert f

/-- The meaning of a comparison. -/
def Vergleich.haelt : Vergleich → Int → Int → Prop
  | .eq, x, y => x = y
  | .lt, x, y => x < y
  | .le, x, y => x ≤ y

/-- Decidable evaluation of a comparison. -/
def Vergleich.entcheidet : Vergleich → Int → Int → Bool
  | .eq, x, y => decide (x = y)
  | .lt, x, y => decide (x < y)
  | .le, x, y => decide (x ≤ y)

/-- The Boolean test agrees with the meaning, per comparison. -/
theorem Vergleich.entcheidet_richtig (op : Vergleich) (x y : Int) :
    op.entcheidet x y = true ↔ op.haelt x y := by
  cases op with
  | eq => simp only [entcheidet, haelt, decide_eq_true_eq]
  | lt => simp only [entcheidet, haelt, decide_eq_true_eq]
  | le => simp only [entcheidet, haelt, decide_eq_true_eq]

/-- The meaning of a predicate over a memory content function. -/
def Praedikat.haelt : Praedikat → (Zelle → Int) → Prop
  | .vgl op a b, f => op.haelt (a.wert f) (b.wert f)
  | .und x y, f => x.haelt f ∧ y.haelt f
  | .oder x y, f => x.haelt f ∨ y.haelt f
  | .nicht x, f => ¬ x.haelt f

/-- Decidable evaluation of a predicate over a memory content function. -/
def Praedikat.werteAus : Praedikat → (Zelle → Int) → Bool
  | .vgl op a b, f => op.entcheidet (a.wert f) (b.wert f)
  | .und x y, f => x.werteAus f && y.werteAus f
  | .oder x y, f => x.werteAus f || y.werteAus f
  | .nicht x, f => !(x.werteAus f)

/-- Evaluation agrees with the meaning. -/
theorem Praedikat.werteAus_richtig (q : Praedikat) (f : Zelle → Int) :
    q.werteAus f = true ↔ q.haelt f := by
  induction q with
  | vgl op a b => exact op.entcheidet_richtig _ _
  | und x y ihx ihy =>
    simp only [werteAus, haelt, ihx, ihy, Bool.and_eq_true]
  | oder x y ihx ihy =>
    simp only [werteAus, haelt, ihx, ihy, Bool.or_eq_true]
  | nicht x ih =>
    simp only [werteAus, haelt]
    constructor
    · intro h hc
      have hx : x.werteAus f = true := ih.mpr hc
      rw [hx] at h
      exact Bool.false_ne_true h
    · intro hc
      cases hb : x.werteAus f with
      | true =>
        have hp : x.haelt f := ih.mp hb
        exact (hc hp).elim
      | false =>
        rfl

/-- An expression depends only on the cells it reads. -/
theorem Ausdruck.wert_kongruent (e : Ausdruck) : ∀ (f₁ f₂ : Zelle → Int),
    (∀ z ∈ e.zellen, f₁ z = f₂ z) → e.wert f₁ = e.wert f₂ := by
  induction e with
  | konst _ =>
    intro _ _ _
    rfl
  | zelle z =>
    intro f₁ f₂ h
    exact h z (List.mem_singleton.mpr rfl)
  | add a b iha ihb =>
    intro f₁ f₂ h
    simp only [wert, zellen] at h ⊢
    rw [iha f₁ f₂ (fun z mem => h z (List.mem_append_left _ mem)),
      ihb f₁ f₂ (fun z mem => h z (List.mem_append_right _ mem))]
  | sub a b iha ihb =>
    intro f₁ f₂ h
    simp only [wert, zellen] at h ⊢
    rw [iha f₁ f₂ (fun z mem => h z (List.mem_append_left _ mem)),
      ihb f₁ f₂ (fun z mem => h z (List.mem_append_right _ mem))]
  | mul a b iha ihb =>
    intro f₁ f₂ h
    simp only [wert, zellen] at h ⊢
    rw [iha f₁ f₂ (fun z mem => h z (List.mem_append_left _ mem)),
      ihb f₁ f₂ (fun z mem => h z (List.mem_append_right _ mem))]

/-- A predicate depends only on the cells it observes: agreeing contents agree on it.
    This is the footprint rule — the stability certificate of the checker. -/
theorem Praedikat.haelt_stabil (q : Praedikat) : ∀ (f₁ f₂ : Zelle → Int),
    (∀ z ∈ q.beobachtet, f₁ z = f₂ z) → q.haelt f₁ → q.haelt f₂ := by
  induction q with
  | vgl op a b =>
    intro f₁ f₂ h hq
    simp only [haelt, beobachtet] at h hq ⊢
    have ea : a.wert f₁ = a.wert f₂ :=
      a.wert_kongruent f₁ f₂ (fun z mem => h z (List.mem_append_left _ mem))
    have eb : b.wert f₁ = b.wert f₂ :=
      b.wert_kongruent f₁ f₂ (fun z mem => h z (List.mem_append_right _ mem))
    rw [ea, eb] at hq
    exact hq
  | und x y ihx ihy =>
    intro f₁ f₂ h hq
    simp only [haelt, beobachtet] at h hq ⊢
    exact ⟨ihx f₁ f₂ (fun z mem => h z (List.mem_append_left _ mem)) hq.1,
      ihy f₁ f₂ (fun z mem => h z (List.mem_append_right _ mem)) hq.2⟩
  | oder x y ihx ihy =>
    intro f₁ f₂ h hq
    simp only [haelt, beobachtet] at h hq ⊢
    cases hq with
    | inl hx =>
      exact Or.inl (ihx f₁ f₂ (fun z mem => h z (List.mem_append_left _ mem)) hx)
    | inr hy =>
      exact Or.inr (ihy f₁ f₂ (fun z mem => h z (List.mem_append_right _ mem)) hy)
  | nicht x ih =>
    intro f₁ f₂ h hq
    simp only [haelt, beobachtet] at h hq ⊢
    intro hc
    exact hq (ih f₂ f₁ (fun z mem => (h z mem).symm) hc)

/-- The checker decides the loader premise on the memory plan. -/
def pruefeStart (f : Zelle → Int) (ps : List Praedikat) : Bool :=
  ps.all fun q => q.werteAus f

/-- The loader check agrees with the meaning. -/
theorem pruefeStart_richtig (f : Zelle → Int) (ps : List Praedikat) :
    pruefeStart f ps = true ↔ ∀ q ∈ ps, q.haelt f := by
  simp only [pruefeStart, List.all_eq_true, Praedikat.werteAus_richtig]

/-- The checker decides the crash-recovery premise: the restart content is constantly `0`
    (`einrichtung` sets `Wiederanlauf.initial` to `fun _ _ => 0`). -/
def pruefeNeustart (ps : List Praedikat) : Bool :=
  pruefeStart (fun _ => 0) ps

/-- The restart check agrees with the meaning. -/
theorem pruefeNeustart_richtig (ps : List Praedikat) :
    pruefeNeustart ps = true ↔ ∀ q ∈ ps, q.haelt (fun _ => 0) :=
  pruefeStart_richtig _ _

/-- The denotation `⟦·⟧ : Praedikat → Zustand → Prop`: the predicate holds of the unit's
    memory content. -/
def Praedikat.gilt (q : Praedikat) (s : Zustand) : Prop :=
  q.haelt s.initial

/-- Equal memory content gives equal denotation. -/
theorem Praedikat.gilt_of_initial (q : Praedikat) (s₁ s₂ : Zustand)
    (h : s₁.initial = s₂.initial) : q.gilt s₁ → q.gilt s₂ :=
  q.haelt_stabil _ _ (fun z _ => congrFun h z)

/-- The checker decides preservation per command: accept iff the command writes no observed
    cell of any declared predicate. -/
def pruefeBefehlErhalt (ps : List Praedikat) (b : Befehl) : Bool :=
  ps.all fun q => q.beobachtet.all fun z => b.schreibtMoeglich z == false

/-- An accepted command writes no cell observed by the checked predicates. -/
theorem pruefeBefehlErhalt_richtig (ps : List Praedikat) (b : Befehl) (q : Praedikat)
    (hmem : q ∈ ps) (ok : pruefeBefehlErhalt ps b = true) (z : Zelle)
    (hm : z ∈ q.beobachtet) : b.schreibtMoeglich z = false := by
  simp only [pruefeBefehlErhalt, List.all_eq_true] at ok
  have hdec := ok q hmem z hm
  simpa only [beq_iff_eq] using hdec

end Gabbro.Core.Ast.Semantik
