module

public import Stage0.Senke.Bild.Mehr.Goal
import Grammatik.Parser.Elab.UebersetzeAllg3.Memo

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {src : String} {reserve : Nat} {options : Profil.Options}

/-- These are the original accumulator declarations selected by this
    exact compilation. Generated cells never add another declaration. -/
def imageAccumulatorItems (output : Emitted src reserve options) : List SItemTief :=
  (uMembers (pre108 output.compiled.source.prepared.elaborierbar)).filter fun item =>
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

/-- Each descriptor is exactly the result of the exporter for its original
    source item, including the generated declarations in the compiled unit. -/
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

end Gabbro.Stage0
