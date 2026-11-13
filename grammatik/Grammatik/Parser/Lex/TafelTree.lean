module
public import Grammatik.Parser.Lex.TafelIndex
public import Std.Data.TreeMap.Lemmas
public import Init.Data.Ord.String
@[expose] public section
namespace Gabbro.Grammatik.Parser.Tafel

/-- The persistent counterpart of `Index`: extending a shared scope copies a logarithmic
    tree path, never a hash map's bucket array. Immutable unit tables still use `Tafel`. -/
structure Tree (κ α : Type) [Ord κ] [BEq κ] (key : α → κ) where
  liste : List α
  tree : Std.TreeMap κ α
  treu : ∀ name, tree[name]? = liste.find? (fun x => key x == name)

namespace Tree

def empty {κ α : Type} [Ord κ] [BEq κ] [Std.TransOrd κ]
    (key : α → κ) : Tree κ α key :=
  ⟨[], ∅, by intro name; exact Std.TreeMap.getElem?_emptyc⟩

def cons {κ α : Type} [Ord κ] [BEq κ] [Std.TransOrd κ] [Std.LawfulBEqOrd κ]
    {key : α → κ} (x : α) (table : Tree κ α key) : Tree κ α key :=
  ⟨x :: table.liste, table.tree.insert (key x) x, by
    intro name
    rw [Std.TreeMap.getElem?_insert, List.find?_cons, table.treu]
    by_cases same : compare (key x) name = Ordering.eq
    · have equal := Std.LawfulBEqOrd.compare_eq_iff_beq.mp same
      simp only [if_pos same, equal]
    · have different := Std.LawfulBEqOrd.not_compare_eq_iff_beq_eq_false.mp same
      simp only [if_neg same, different]⟩

def finde {κ α : Type} [Ord κ] [BEq κ] {key : α → κ}
    (table : Tree κ α key) (name : κ) : Option α :=
  table.liste.find? (fun x => key x == name)

def findeFast {κ α : Type} [Ord κ] [BEq κ] {key : α → κ}
    (table : Tree κ α key) (name : κ) : Option α := table.tree[name]?

@[csimp] theorem finde_eq_fast : @finde = @findeFast := by
  funext κ α _ _ key table name
  exact (table.treu name).symm

theorem cons_finde {κ α : Type} [Ord κ] [BEq κ] [Std.TransOrd κ] [Std.LawfulBEqOrd κ]
    {key : α → κ} (x : α) (table : Tree κ α key) (name : κ) :
    (cons x table).finde name = if key x == name then some x else table.finde name := by
  unfold finde cons
  rw [List.find?_cons]
  cases key x == name <;> rfl

end Tree
end Gabbro.Grammatik.Parser.Tafel
