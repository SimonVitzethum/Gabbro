module

public import Grammatik.Logik.Invarianten.VC.Scalar
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtInv

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.VC

open Frag Elim Elim.Korrekt Modell

variable {D : Deklaration}

/-- The only reusable callee assertions are declared invariants. There is no
    ensures expression, contract label, or arbitrary postcondition in this API. -/
structure InvariantFormula (program : Programm D) (items : List D.Inv) where
  formula : QF (Observation D)
  correct : ∀ world, formula.denote (assignment world) ↔
    ∀ item ∈ items, InvHaelt program item world

def invariantFormula (program : Programm D) :
    (items : List D.Inv) → Except Frag.Refusal (InvariantFormula program items)
  | [] => .ok
      { formula := .tru
        correct := fun _ => by simp [QF.denote] }
  | item :: rest => do
      match translated : translateDeclared program item with
      | .error cause => .error cause
      | .ok head => do
          let tail ← invariantFormula program rest
          return {
              formula := conj (lower head) tail.formula
              correct := fun world => by
                rw [conj_denote, lower_denote, tail.correct world]
                have evaluated := translateDeclared_sound program item head translated world
                constructor
                · intro h current member
                  rcases List.mem_cons.mp member with same | member
                  · subst current
                    exact (evaluated).mpr h.1
                  · exact h.2 current member
                · intro h
                  exact ⟨(evaluated).mp (h item (by simp)),
                    fun current member => h current (List.mem_cons_of_mem _ member)⟩ }

/-- Verification order is supplied by P20. These are proofs about the ACTUAL
    call answers, not assumptions extracted from unproved contract text. Empty
    lists recover the existing frame-only handler class. -/
structure CallEvidence (program : Programm D) (checked : D.Fn → List D.Inv)
    (calls : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) : Prop where
  frame : ∀ f world args next value, calls f world args = .ok next value →
    Rahmen (D.schreibt f) (D.gschreibt f) world next
  invariants : ∀ f world args next value, calls f world args = .ok next value →
    ∀ item ∈ checked f, InvHaelt program item next

theorem frameOnlyEvidence (program : Programm D)
    (calls : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (respects : RespektiertRahmen program calls) : CallEvidence program (fun _ => []) calls where
  frame := fun f world args next value success => (respects.2 f world args next value success).1
  invariants := fun _ _ _ _ _ _ _ member => by simp at member

def writtenObservation (f : D.Fn) : Observation D → Bool
  | .glob name => D.gschreibt f name
  | .slot table _ _ => D.schreibt f table

theorem frame_observation (f : D.Fn) (world next : World D)
    (frame : Rahmen (D.schreibt f) (D.gschreibt f) world next)
    (key : Observation D) (unchanged : writtenObservation f key = false) :
    assignment world key = assignment next key := by
  cases key with
  | glob name => exact congrArg (scalarValue (D.gtyp name)) (frame.2 name unchanged).symm
  | slot table field index =>
      exact congrArg (scalarValue (D.typ table field)) (frame.1 table unchanged index field).symm

/-- Unsupported memory types supply no arithmetic fact. Their scalar projection
    being total does not manufacture a value-range assertion. -/
def typeFact (key : Observation D) : LProp (Observation D) :=
  match observationType key with
  | .int lo hi => .and (.le (.konst lo) (.var key)) (.le (.var key) (.konst hi))
  | .str capacity => .and (.le (.konst 0) (.var key)) (.le (.var key) (.konst capacity))
  | .bool => .and (.le (.konst 0) (.var key)) (.le (.var key) (.konst 1))
  | _ => .tru

/-- The range fact of one observation, from the typed value it reads. -/
theorem typeFact_of_value (world : World D) (key : Observation D) (τ : Ty) (value : Wert D τ)
    (kind : observationType key = τ) (reads : assignment world key = scalarValue τ value) :
    (typeFact key).denote (assignment world) := by
  unfold typeFact
  rw [kind]
  cases τ with
  | int lo hi =>
      simp only [LProp.denote, LTerm.denote, reads, scalarValue]
      exact ⟨value.lo_le, value.le_hi⟩
  | str capacity =>
      simp only [LProp.denote, LTerm.denote, reads, scalarValue]
      exact ⟨Int.natCast_nonneg _, by exact_mod_cast value.property⟩
  | bool =>
      simp only [LProp.denote, LTerm.denote, reads, scalarValue]
      cases value <;> simp [wahr?]
  | _ => trivial

theorem typeFact_sound (key : Observation D) (world : World D) :
    (typeFact key).denote (assignment world) := by
  cases key with
  | glob name => exact typeFact_of_value world _ (D.gtyp name) (world.globs name) rfl rfl
  | slot table field index =>
      exact typeFact_of_value world _ (D.typ table field) (world.slots table index field) rfl rfl

def typeFacts (keys : List (Observation D)) : LProp (Observation D) :=
  keys.eraseDups.foldr (fun key rest => .and (typeFact key) rest) .tru

private theorem foldedTypeFacts_denote (keys : List (Observation D))
    (values : Assignment (Observation D)) :
    (keys.foldr (fun key rest => LProp.and (typeFact key) rest) LProp.tru).denote values ↔
      ∀ key ∈ keys, (typeFact key).denote values := by
  induction keys with
  | nil => exact ⟨fun _ _ member => False.elim (List.not_mem_nil member), fun _ => trivial⟩
  | cons key keys ih =>
      change ((typeFact key).denote values ∧ _) ↔ _
      rw [ih]
      constructor
      · intro valid current member
        rcases List.mem_cons.mp member with same | member
        · subst current; exact valid.1
        · exact valid.2 current member
      · intro valid
        exact ⟨valid key List.mem_cons_self,
          fun current member => valid current (List.mem_cons_of_mem key member)⟩

/-- Every original observation keeps its decoded range constraint. Repeating
    the same constraint has no effect on any arithmetic assignment. -/
theorem typeFacts_denote (keys : List (Observation D)) (values : Assignment (Observation D)) :
    (typeFacts keys).denote values ↔ ∀ key ∈ keys, (typeFact key).denote values := by
  simp only [typeFacts, foldedTypeFacts_denote, List.mem_eraseDups]

theorem typeFacts_sound (keys : List (Observation D)) (world : World D) :
    (typeFacts keys).denote (assignment world) :=
  (typeFacts_denote keys _).mpr (fun key _ => typeFact_sound key world)

/-- Written carriers are universally havoced. Only decode ranges, the frame,
    and checked invariant formulas constrain their result. -/
def callWP (f : D.Fn) (facts post : QF (Observation D)) : QF (Observation D) :=
  let keys := qfKeys facts ++ qfKeys post
  havoc (writtenObservation f)
    (lower (.imp (.and (typeFacts keys) (quoteQF facts)) (quoteQF post)))

theorem callWP_sound (f : D.Fn) (facts post : QF (Observation D)) (world next : World D)
    (valid : (callWP f facts post).denote (assignment world))
    (frame : Rahmen (D.schreibt f) (D.gschreibt f) world next)
    (checked : facts.denote (assignment next)) : post.denote (assignment next) := by
  have result := havoc_sound (writtenObservation f) _ (assignment world) (assignment next)
    valid (fun key _ unchanged => frame_observation f world next frame key unchanged)
  exact (quoteQF_denote post _).mp
    (((lower_denote _ _).mp result) ⟨typeFacts_sound _ next, (quoteQF_denote facts _).mpr checked⟩)

end Gabbro.Grammatik.Invarianten.VC
