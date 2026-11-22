module

public import Stage0.Senke.Bild.Mehr.Goal
import Grammatik.Parser.Elab.UebersetzeAllg3.Memo

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg

variable {src : String} {reserve : Nat} {options : Profil.Options}

/-- Take the declarations from the expansion retained by this compilation.
    This includes instantiated modules under their canonical resolved names. -/
def imageAccumulatorItems (output : Emitted src reserve options) : List SItemTief :=
  (uMembers output.compiled.expanded).filter fun item =>
    match item with
    | .accT .. => true
    | _ => false

/-- Resolve each generated name in the actual canonical declaration
    table, keeping its typed position. -/
def imageNamedIndex {α : Type} (entries : List α) (name : α → String) (expected : String) :
    Except String (Fin entries.length) :=
  match (List.finRange entries.length).find? (fun index => name (entries.get index) == expected) with
  | some position => .ok position
  | none => .error ("ir: generated declaration missing: " ++ expected)

/-- A successful lookup refers to the exact named declaration in the
    canonical table, even when its position changes during expansion. -/
theorem imageNamedIndex_sound {α : Type} {entries : List α} {name : α → String}
    {expected : String} {position : Fin entries.length}
    (found : imageNamedIndex entries name expected = .ok position) :
    name (entries.get position) = expected := by
  unfold imageNamedIndex at found
  cases result : (List.finRange entries.length).find? (fun index => name (entries.get index) == expected) with
  | none => rw [result] at found; cases found
  | some selected =>
    rw [result] at found
    cases found
    have sameName : (name (entries.get position) == expected) = true :=
      List.find?_some (p := fun index => name (entries.get index) == expected) result
    exact beq_iff_eq.mp sameName

theorem imageNamedIndex_complete {α : Type} {entries : List α} {name : α → String}
    {expected : String} (declared : ∃ entry ∈ entries, name entry = expected) :
    ∃ position, imageNamedIndex entries name expected = .ok position := by
  obtain ⟨entry, listed, named⟩ := declared
  obtain ⟨index, inRange, exactEntry⟩ := List.mem_iff_getElem.mp listed
  let position : Fin entries.length := ⟨index, inRange⟩
  have equal : name (entries.get position) = expected := (congrArg name exactEntry).trans named
  unfold imageNamedIndex
  cases found : (List.finRange entries.length).find? (fun index => name (entries.get index) == expected) with
  | some selected => exact ⟨selected, rfl⟩
  | none =>
    exact False.elim ((List.find?_eq_none.mp found position (List.mem_finRange position)) (beq_iff_eq.mpr equal))

def imageAccumulatorMembers (output : Emitted src reserve options) (name : String)
    (k : Nat) : Except String (Fin k → (declOf output.compiled.unit).Glob) :=
  sammle k _ (fun i => imageNamedIndex output.compiled.unit.globs UGlob.name (name ++ "#zelle" ++ toString i.val))

def imageAccumulatorLocks (output : Emitted src reserve options) (name : String)
    (k : Nat) : Except String (Fin k → (declOf output.compiled.unit).Lock) :=
  sammle k _ (fun i => imageNamedIndex output.compiled.unit.locks ULock.name (name ++ "#sperre" ++ toString i.val))

/-- Use the canonical accumulator elaborator with exactly the generated
    cells, locks and functions selected in the compiled program. -/
def lowerImageAccumulator (output : Emitted src reserve options) (item : SItemTief) :
    Except String (Kernzelle.AccumulatorDecl (declOf output.compiled.unit)) := do
  let .accT name .. := item | throw "ir: expected an accumulator declaration"
  let unit := output.compiled.unit
  let scopes := output.compiled.source.scopes
  let query ← imageNamedIndex unit.fns UFn.name (name ++ "#query")
  let update ← imageNamedIndex unit.fns UFn.name (name ++ "#aktualisiere")
  let fold ← imageNamedIndex unit.fns UFn.name (name ++ "#falte")
  uAkkuDeclWith scopes.values scopes.types item
    (imageAccumulatorMembers output name) (imageAccumulatorLocks output name) query update fold

/-- Each descriptor comes from its expanded source declaration and the
    corresponding generated entries in the compiled unit. -/
def ImageAccumulator (output : Emitted src reserve options) (item : SItemTief)
    (acc : Kernzelle.AccumulatorDecl (declOf output.compiled.unit)) : Prop :=
  lowerImageAccumulator output item = .ok acc

def collectImageAccumulators (output : Emitted src reserve options) :
    (items : List SItemTief) → Except String
      {descriptors : List (Kernzelle.AccumulatorDecl (declOf output.compiled.unit)) //
        List.Forall₂ (ImageAccumulator output) items descriptors}
  | [] => .ok ⟨[], .nil⟩
  | item :: tail => do
    match lowered : lowerImageAccumulator output item with
    | .error error => throw error
    | .ok first =>
      let rest ← collectImageAccumulators output tail
      pure ⟨first :: rest.val, .cons lowered rest.property⟩

theorem collectImageAccumulators_empty (output : Emitted src reserve options)
    {items : List SItemTief} (empty : items = []) :
    collectImageAccumulators output items = .ok ⟨[], by rw [empty]; exact .nil⟩ := by
  subst items
  rfl

end Gabbro.Stage0
