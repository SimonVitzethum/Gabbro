module

public import Grammatik.Logik.Invarianten.VC.Formula
public import Grammatik.Logik.Invarianten.Frag.Translation

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.VC

open Frag Elim Elim.Korrekt Modell

variable {D : Deklaration}

/-- The generated formula carries a proof about the existing semantics, erased
    by compilation. No client supplies a preservation proof to the generator. -/
structure Precondition (target : World D → Prop) where
  formula : QF (Observation D)
  sound : ∀ world, formula.denote (assignment world) → target world

theorem assignment_lese (world : World D) (resources : List (Res D))
    (carriers : List (D.Tab ⊕ D.Glob)) :
    assignment (world.lese resources carriers) = assignment world := by
  funext key
  cases key <;> rfl

theorem assignment_schreibGlob (world : World D) (name : D.Glob)
    (resources : List (Res D)) (value : Wert D (D.gtyp name)) :
    assignment (world.schreibGlob name resources value) =
      (assignment world).bind (.glob name) (scalarValue (D.gtyp name) value) := by
  funext key
  cases key with
  | slot table field index => rfl
  | glob other =>
      by_cases same : other = name
      · subst other
        simp [assignment, World.schreibGlob, World.storeGlob, World.merke,
          ↓reduceDIte, Assignment.bind, ↓reduceIte]
      · simp [assignment, World.schreibGlob, World.storeGlob, World.merke,
          Assignment.bind, same]

theorem assignment_schreibSlot (world : World D) (table : D.Tab) (field : D.Feld table)
    (index : Int) (resources : List (Res D)) (value : Wert D (D.typ table field)) :
    assignment (world.schreibSlot table resources index field value) =
      (assignment world).bind (.slot table field index) (scalarValue (D.typ table field) value) := by
  funext key
  cases key with
  | glob name => rfl
  | slot other otherField otherIndex =>
      by_cases sameTable : other = table
      · subst other
        by_cases sameField : otherField = field
        · subst otherField
          by_cases sameIndex : otherIndex = index
          · subst otherIndex
            simp [assignment, World.schreibSlot, World.storeSlot, World.merke, Assignment.bind]
          · simp [assignment, World.schreibSlot, World.storeSlot, World.merke,
              Assignment.bind, sameIndex]
        · simp [assignment, World.schreibSlot, World.storeSlot, World.merke,
            Assignment.bind, sameField]
      · simp [assignment, World.schreibSlot, World.storeSlot, World.merke,
          Assignment.bind, sameTable]

structure ScalarEncoding (value : World D → Int) where
  term : LTerm (Observation D)
  correct : ∀ world, term.denote (assignment world) = value world

def translateScalar (expression : Expr D Γ Λ τ) (locals : Env D Γ) :
    Except Frag.Refusal (ScalarEncoding (fun world => scalarValue τ (eval world expression world locals))) :=
  match τ with
  | .int _ _ => do
      let encoded ← translate expression locals
      return {
          term := encoded.payload
          correct := encoded.correct }
  | .str _ => do
      let encoded ← translate expression locals
      return {
          term := encoded.payload
          correct := encoded.correct }
  | _ => .error (.unsupported "writer stores a non-scalar value")

/-- Backward substitution for stores, including the model's explicit narrowing
    fallback. Both arms are checked. The fallback is never treated as unreachable
    merely because the source author intended it to be. -/
def scalarWP (expression : Expr D Γ Λ τ) (locals : Env D Γ)
    (key : Observation D) (post : QF (Observation D)) :
    Except Frag.Refusal (Precondition (fun world =>
      post.denote ((assignment world).bind key (scalarValue τ (eval world expression world locals))))) :=
  match expression with
  | .eng value lo hi fallback => do
      let encoded ← translateScalar value locals
      let yes ← scalarWP value locals key post
      let no ← scalarWP fallback locals key post
      let guard : LProp (Observation D) :=
        .and (.le (.konst lo) encoded.term) (.le encoded.term (.konst hi))
      return {
          formula := lower (.and (.imp guard (quoteQF yes.formula))
            (.imp (.not guard) (quoteQF no.formula)))
          sound := fun world valid => by
            have branches := (lower_denote _ (assignment world)).mp valid
            have guardCorrect : guard.denote (assignment world) ↔
                lo ≤ (eval world value world locals).n ∧
                  (eval world value world locals).n ≤ hi := by
              change lo ≤ encoded.term.denote _ ∧ encoded.term.denote _ ≤ hi ↔ _
              rw [encoded.correct world]
              rfl
            by_cases fits : lo ≤ (eval world value world locals).n ∧
                (eval world value world locals).n ≤ hi
            · have selected := yes.sound world
                ((quoteQF_denote _ _).mp (branches.1 (guardCorrect.mpr fits)))
              dsimp only [eval]
              rw [dif_pos fits]
              exact selected
            · have selected := no.sound world
                ((quoteQF_denote _ _).mp (branches.2 (fun h => fits (guardCorrect.mp h))))
              dsimp only [eval]
              rw [dif_neg fits]
              exact selected }
  | .wenn condition yes no => do
      let guard ← translate condition locals
      let yesVC ← scalarWP yes locals key post
      let noVC ← scalarWP no locals key post
      return {
          formula := lower (.and (.imp guard.payload (quoteQF yesVC.formula))
            (.imp (.not guard.payload) (quoteQF noVC.formula)))
          sound := fun world valid => by
            have branches := (lower_denote _ (assignment world)).mp valid
            cases tested : eval world condition world locals with
            | true =>
                have selected := yesVC.sound world
                  ((quoteQF_denote _ _).mp (branches.1 ((guard.correct world).mp tested)))
                simpa only [eval, tested, wahr?, ↓reduceIte] using selected
            | false =>
                have absent : ¬ guard.payload.denote (assignment world) := by
                  intro h
                  have := (guard.correct world).mpr h
                  rw [tested] at this
                  exact Bool.noConfusion this
                have selected := noVC.sound world
                  ((quoteQF_denote _ _).mp (branches.2 absent))
                simpa only [eval, tested, wahr?, Bool.false_eq_true, ↓reduceIte] using selected }
  | expression => do
      let encoded ← translateScalar expression locals
      return {
          formula := post.subst key encoded.term
          sound := fun world valid => by
            have selected := (subst_denote key encoded.term post (assignment world)).mp valid
            rw [encoded.correct world] at selected
            exact selected }

/-- Reading an expression changes the trace, but no scalar observation. -/
def readPrecondition (resources : List (Res D)) (carriers : List (D.Tab ⊕ D.Glob))
    {target : World D → Prop} (pre : Precondition target) :
    Precondition (fun world => target (world.lese resources carriers)) where
  formula := pre.formula
  sound := fun world valid => pre.sound _ (by rw [assignment_lese]; exact valid)

end Gabbro.Grammatik.Invarianten.VC
