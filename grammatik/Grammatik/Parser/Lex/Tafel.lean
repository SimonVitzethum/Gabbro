/-
  A name table: a list for the kernel, a hash map for compiled code.

  `Tafel.finde` is `List.find?` by name, so every definition that uses a table means a list scan
  and the kernel never touches the map. Compiled code reads the map (`finde_eq_schnell`); the
  field `treu` states that both agree.
-/
module
public import Std.Data.HashMap.Lemmas
public import Grammatik.Parser.Lex.Lexer.Teil1
@[expose] public section

namespace Gabbro.Grammatik.Parser

/-- Named entries with a map of the same entries; the first entry of a name wins in both. -/
structure Tafel (α : Type) (key : α → String) where
  liste : List α
  karte : Std.HashMap String α
  treu : ∀ name, karte[name]? = liste.find? (fun x => strEq (key x) name)

namespace Tafel

variable {α : Type} {key : α → String}

/-- Inserting from the right leaves the first entry of every name in the map. -/
theorem foldr_get (xs : List α) (name : String) :
    (xs.foldr (fun x m => m.insert (key x) x) (∅ : Std.HashMap String α))[name]? =
      xs.find? (fun x => strEq (key x) name) := by
  induction xs with
  | nil => simp only [List.foldr_nil, Std.HashMap.getElem?_empty, List.find?_nil]
  | cons x xs ih =>
    rw [List.foldr_cons, Std.HashMap.getElem?_insert, List.find?_cons, ih,
      congrFun (congrFun strEq_eq_schnell (key x)) name]
    unfold strEqSchnell
    by_cases same : key x = name
    · simp only [same, beq_self_eq_true, if_true, decide_true]
    · simp only [beq_iff_eq, same, if_false, decide_false]

/-- The table of a list. -/
def von (key : α → String) (xs : List α) : Tafel α key :=
  ⟨xs, xs.foldr (fun x m => m.insert (key x) x) ∅, foldr_get xs⟩

@[simp] theorem von_liste (xs : List α) : (von key xs).liste = xs := rfl

/-- The first entry of a name. -/
def finde (t : Tafel α key) (name : String) : Option α :=
  t.liste.find? (fun x => strEq (key x) name)

/-- The same entry from the map. -/
def findeSchnell (t : Tafel α key) (name : String) : Option α := t.karte[name]?

/-- **The map answers as the list scan does.** -/
@[csimp] theorem finde_eq_schnell : @finde = @findeSchnell := by
  funext α key t name
  exact (t.treu name).symm

end Tafel

end Gabbro.Grammatik.Parser
