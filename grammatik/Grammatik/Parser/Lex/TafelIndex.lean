module
public import Grammatik.Parser.Lex.Tafel
@[expose] public section

namespace Gabbro.Grammatik.Parser.Tafel

/-- The same list/map boundary as `Tafel`, for structural keys such as namespace paths.
    In particular, paths are never flattened with a separator that source names could contain. -/
structure Index (κ α : Type) [BEq κ] [Hashable κ] (key : α → κ) where
  liste : List α
  karte : Std.HashMap κ α
  treu : ∀ name, karte[name]? = liste.find? (fun x => key x == name)

namespace Index

variable {κ α : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] [LawfulHashable κ]
  {key : α → κ}

theorem foldr_get (xs : List α) (name : κ) :
    (xs.foldr (fun x m => m.insert (key x) x) (∅ : Std.HashMap κ α))[name]? =
      xs.find? (fun x => key x == name) := by
  induction xs with
  | nil => simp only [List.foldr_nil, Std.HashMap.getElem?_empty, List.find?_nil]
  | cons x xs ih =>
    rw [List.foldr_cons, Std.HashMap.getElem?_insert, List.find?_cons, ih]
    cases key x == name <;> rfl

def von (key : α → κ) (xs : List α) : Index κ α key :=
  ⟨xs, xs.foldr (fun x m => m.insert (key x) x) ∅, foldr_get xs⟩

/-- Specification lookup: kernel witnesses only evaluate the list. -/
def finde (table : Index κ α key) (name : κ) : Option α :=
  table.liste.find? (fun x => key x == name)

def findeSchnell (table : Index κ α key) (name : κ) : Option α := table.karte[name]?

@[csimp] theorem finde_eq_schnell : @finde = @findeSchnell := by
  funext κ α _ _ key table name
  exact (table.treu name).symm

end Index

/-- Counts with the same kernel/executable separation as the entry tables. -/
structure Counts where
  liste : List String
  karte : Std.HashMap String Nat
  treu : ∀ name, karte.getD name 0 = (liste.filter (fun x => strEq x name)).length

namespace Counts

def von (xs : List String) : Counts := ⟨xs, zaehle xs, zaehle_getD xs⟩

def count (table : Counts) (name : String) : Nat :=
  (table.liste.filter (fun x => strEq x name)).length

def countSchnell (table : Counts) (name : String) : Nat := table.karte.getD name 0

@[csimp] theorem count_eq_schnell : count = countSchnell := by
  funext table name
  exact (table.treu name).symm

end Counts
end Gabbro.Grammatik.Parser.Tafel
