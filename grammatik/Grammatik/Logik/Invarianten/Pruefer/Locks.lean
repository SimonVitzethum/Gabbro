module

public import Grammatik.Logik.Invarianten.VC.Extended

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Pruefer

open Frag Elim VC Modell

variable {D : Deklaration}

/-- Optional source evidence for a semantic lock predicate. This is part of
    the model value, not a proof submitted to or checked by the compiler.
    Without reification the lock predicate remains user duty (b). -/
structure ReifiedLock (S : SperrInv D) (lock : D.Lock) where
  resources : List (Res D)
  expression : Expr D [] resources .bool
  correct : ∀ world, eval world expression world .nil = S.inv lock world.speicher

abbrev LockSources (S : SperrInv D) := ∀ lock, Option (ReifiedLock S lock)

def lockFormula (S : SperrInv D) (sources : LockSources S) (lock : D.Lock) :
    Except Frag.Refusal (LockFormula S lock) := do
  let some source := sources lock
    | .error (.unsupported "semantic lock invariant has no reified source formula; user duty")
  let encoded ← translateInvariant (S.orte lock) source.expression
  return {
      formula := lower encoded.payload
      correct := fun world => by
        rw [lower_denote, ← encoded.bool_iff world, source.correct world] }

/-- Enumerate parameter values, with a proof of completeness. No arbitrary
    sample or supplied proof of a function contract participates in checking. -/
structure Environments (D : Deklaration) (context : Ctx) where
  values : List (Env D context)
  complete : ∀ locals, locals ∈ values

def environments (budget : Nat) : (context : Ctx) → Except Frag.Refusal (Environments D context)
  | [] => .ok { values := [.nil], complete := fun locals => by cases locals; simp }
  | kind :: context => do
      let head ← localDomain (D := D) budget kind
      let tail ← environments budget context
      if head.values.length * tail.values.length ≤ budget then
        return {
            values := head.values.flatMap fun value => tail.values.map (Env.cons value)
            complete := fun locals => by
              cases locals with
              | cons value locals =>
                  exact List.mem_flatMap.mpr ⟨value, head.complete value,
                    List.mem_map.mpr ⟨locals, tail.complete locals, rfl⟩⟩ }
      else .error (.unsupported "writer parameter product exceeds the VC expansion budget")

/-- Conjoin certificates for a finite complete domain without evaluating proof
    fields. This is shared by parameter and function enumeration. -/
def collect (items : List α) (property : α → Prop)
    (check : ∀ item, Except Frag.Refusal (PLift (property item))) :
    Except Frag.Refusal (PLift (∀ item ∈ items, property item)) :=
  match items with
  | [] => .ok ⟨fun _ member => False.elim (List.not_mem_nil member)⟩
  | item :: rest => do
      let head ← check item
      let tail ← collect rest property check
      return ⟨fun current member => by
        rcases List.mem_cons.mp member with same | member
        · subst current; exact head.down
        · exact tail.down current member⟩

end Gabbro.Grammatik.Invarianten.Pruefer
