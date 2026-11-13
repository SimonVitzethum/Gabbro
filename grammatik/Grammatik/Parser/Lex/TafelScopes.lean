module
public import Grammatik.Parser.Lex.TafelTree
@[expose] public section

namespace Gabbro.Grammatik.Parser.Tafel

/-- Persistent numbered stack. Levels count from the oldest entry, so pushing does not
    renumber existing entries. The kernel still reads the original list. -/
structure Stack (α : Type) where
  liste : List α
  size : Nat
  size_eq : size = liste.length
  table : Tree Nat (Nat × α) Prod.fst
  treu : ∀ j, (if j < size then (table.finde (size - 1 - j)).map Prod.snd else none) = liste[j]?

namespace Stack

/-- Keep the caller's actual list object as the validation key. Reconstructing an equal
    cons cell would miss the pointer test and compare the entire scope on every read. -/
def rebase {α : Type} (stack : Stack α) (xs : List α) (same : xs = stack.liste) : Stack α :=
  { stack with
    liste := xs
    size_eq := (by rw [same]; exact stack.size_eq)
    treu := (by intro j; rw [same]; exact stack.treu j) }

def empty {α : Type} : Stack α := ⟨[], 0, rfl, Tree.empty Prod.fst, by intro j; rfl⟩

def cons {α : Type} (x : α) (stack : Stack α) : Stack α :=
  ⟨x :: stack.liste, stack.size + 1, by rw [List.length_cons, stack.size_eq],
    Tree.cons (stack.size, x) stack.table, by
      intro j
      cases j with
      | zero =>
        simp only [Nat.zero_lt_succ, if_true, Nat.add_sub_cancel, Nat.sub_zero,
          Tree.cons_finde, beq_self_eq_true, Option.map_some, List.getElem?_cons_zero]
      | succ j =>
        by_cases inside : j < stack.size
        · have less : j + 1 < stack.size + 1 := by omega
          have number : stack.size + 1 - 1 - (j + 1) = stack.size - 1 - j := by omega
          have different : (stack.size == stack.size - 1 - j) = false := by
            simp only [beq_eq_false_iff_ne]
            omega
          simp only [less, if_true, number, Tree.cons_finde, different, Bool.false_eq_true,
            if_false, List.getElem?_cons_succ]
          simpa only [inside, if_true] using stack.treu j
        · have outside : ¬ j + 1 < stack.size + 1 := by omega
          simp only [outside, if_false, List.getElem?_cons_succ]
          exact (by simpa only [inside, if_false] using stack.treu j)⟩

def von {α : Type} : List α → Stack α
  | [] => empty
  | x :: xs => cons x (von xs)

theorem von_liste {α : Type} (xs : List α) : (von xs).liste = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (x :: ·) ih

def get {α : Type} (stack : Stack α) (j : Nat) : Option α := stack.liste[j]?

def getFast {α : Type} (stack : Stack α) (j : Nat) : Option α :=
  if j < stack.size then (stack.table.finde (stack.size - 1 - j)).map Prod.snd else none

@[csimp] theorem get_eq_fast : @get = @getFast := by
  funext α stack j
  exact (stack.treu j).symm

/-- Retain a shared stack after an unrelated record update; rebuild only stale data. -/
@[inline] def fit {α : Type} [DecidableEq α] (xs : List α) (stack : Stack α) : Stack α :=
  match withPtrEqDecEq stack.liste xs (fun _ => inferInstance) with
  | isTrue _ => stack
  | isFalse _ => von xs

theorem fit_liste {α : Type} [DecidableEq α] (xs : List α) (stack : Stack α) :
    (fit xs stack).liste = xs := by
  unfold fit
  split
  · assumption
  · exact von_liste xs

end Stack

/-- A name's stable level and the stack's length. Shadowing inserts one entry; no
    old level changes. The bounds make decoding to a de Bruijn position exact. -/
structure Positions where
  names : List String
  size : Nat
  size_eq : size = names.length
  table : Tree String (String × Nat) Prod.fst
  treu : ∀ name, (table.finde name).map (fun entry => size - 1 - entry.2) = names.findIdx? (strEq · name)
  bounded : ∀ name entry, table.finde name = some entry → entry.2 < size

namespace Positions

def rebase (index : Positions) (names : List String) (same : names = index.names) : Positions :=
  { index with
    names := names
    size_eq := (by rw [same]; exact index.size_eq)
    treu := (by intro name; rw [same]; exact index.treu name) }

def empty : Positions :=
  ⟨[], 0, rfl, Tree.empty Prod.fst, by intro name; rfl, by intro name entry h; cases h⟩

private theorem string_beq (a b : String) : (a == b) = strEq a b :=
  calc
    (a == b) = strEqSchnell a b := by
      apply Bool.eq_iff_iff.mpr
      simp only [strEqSchnell, beq_iff_eq, decide_eq_true_eq]
    _ = strEq a b := (congrFun (congrFun strEq_eq_schnell a) b).symm

def cons (name : String) (index : Positions) : Positions :=
  ⟨name :: index.names, index.size + 1, by rw [List.length_cons, index.size_eq],
    Tree.cons (name, index.size) index.table, by
      intro query
      rw [Tree.cons_finde, List.findIdx?_cons, string_beq]
      cases same : strEq name query with
      | true => simp only [if_true, Option.map_some]; congr 1; omega
      | false =>
        simp only [Bool.false_eq_true, if_false]
        have old := index.treu query
        cases found : index.table.finde query with
        | none =>
          simp only [found, Option.map_none] at old ⊢
          rw [← old]
          rfl
        | some entry =>
          have bound := index.bounded query entry found
          simp only [found, Option.map_some] at old ⊢
          rw [← old]
          simp only [Option.map_some]
          congr 1
          omega,
    by
      intro query entry found
      rw [Tree.cons_finde, string_beq] at found
      cases same : strEq name query with
      | true =>
        simp only [same, if_true, Option.some.injEq] at found
        cases found
        exact Nat.lt_succ_self _
      | false =>
        simp only [same, Bool.false_eq_true, if_false] at found
        exact Nat.lt_trans (index.bounded query entry found) (Nat.lt_succ_self _)⟩

def von : List String → Positions
  | [] => empty
  | name :: names => cons name (von names)

theorem von_names (names : List String) : (von names).names = names := by
  induction names with
  | nil => rfl
  | cons name names ih => exact congrArg (name :: ·) ih

def find (index : Positions) (name : String) : Option Nat := index.names.findIdx? (strEq · name)

def findFast (index : Positions) (name : String) : Option Nat :=
  (index.table.finde name).map (fun entry => index.size - 1 - entry.2)

@[csimp] theorem find_eq_fast : find = findFast := by
  funext index name
  exact (index.treu name).symm

@[inline] def fit (names : List String) (index : Positions) : Positions :=
  match withPtrEqDecEq index.names names (fun _ => inferInstance) with
  | isTrue _ => index
  | isFalse _ => von names

theorem fit_names (names : List String) (index : Positions) :
    (fit names index).names = names := by
  unfold fit
  split
  · assumption
  · exact von_names names

end Positions
end Gabbro.Grammatik.Parser.Tafel
