module

public import Grammatik.Logik.Invarianten.Frag.Admission

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Frag

variable {D : Deklaration}

/-- Conjoin a statically finite family, preserving the model's Boolean `all`
    semantics. The translator calls this only after checking the entire body.
    A later VC pass can retain a local template instead of expanding a large table;
    this implementation has no hidden bound or unverified quantifier oracle. -/
def encodeAll (items : List α) (predicate : α → World D → Bool)
    (compile : ∀ item, Except Refusal (Encoded D .bool (predicate item))) :
    Except Refusal (Encoded D .bool (fun world => items.all (fun item => predicate item world))) :=
  match items with
  | [] => .ok
      { payload := .tru
        correct := fun _ => ⟨fun _ => trivial, fun _ => rfl⟩
        supported := by simp [PayloadSupported, payloadObservations, LProp.freeVariables] }
  | item :: rest => do
      let head ← located "slot" (compile item)
      let tail ← encodeAll rest predicate compile
      return {
          payload := .and head.payload tail.payload
          correct := fun world => by
            change (wahr? (D := D) (predicate item world) &&
                wahr? (D := D) (rest.all (fun entry => predicate entry world))) = true ↔
              LProp.denote (assignment world) head.payload ∧
                LProp.denote (assignment world) tail.payload
            exact Bool.and_eq_true_iff.trans
              (and_congr (head.bool_iff world) (tail.bool_iff world))
          supported := by
            simpa only [PayloadSupported, payloadObservations, LProp.freeVariables,
              List.forall_mem_append] using And.intro head.supported tail.supported }

end Gabbro.Grammatik.Invarianten.Frag
