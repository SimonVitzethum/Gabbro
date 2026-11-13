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
        correct := fun _ => by simp [Represents, LProp.denote]
        supported := by simp [PayloadSupported, payloadObservations, LProp.freeVariables] }
  | item :: rest => do
      let head ← located "slot" (compile item)
      let tail ← encodeAll rest predicate compile
      return
        { payload := .and head.payload tail.payload
          correct := fun world => by
            change ((predicate item world && rest.all (fun entry => predicate entry world)) = true) ↔
              head.payload.denote (assignment world) ∧ tail.payload.denote (assignment world)
            rw [Bool.and_eq_true, head.correct world, tail.correct world]
          supported := by
            simpa only [PayloadSupported, payloadObservations, LProp.freeVariables,
              List.forall_mem_append] using And.intro head.supported tail.supported }

end Gabbro.Grammatik.Invarianten.Frag
