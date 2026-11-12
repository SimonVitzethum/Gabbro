/-
  A table of a dependent family over `Fin n`, filled once.

  A program is a record of functions over the function index, so every access to a body
  runs the elaboration again. `Memo.build` evaluates the family once into an array;
  `Memo.get` reads it. The read is the family itself (`Memo.build_get`), so a definition
  that uses the table equals the one that does not, and only compiled code sees the difference.
-/
module
public import Init.Data.Array.Lemmas
public import Init.Data.Array.OfFn
@[expose] public section

namespace Gabbro.Grammatik.Parser

/-- The entries of a family, each stored with its own index. -/
structure Memo {n : Nat} (T : Fin n → Type) where
  table : Array (Sigma T)
  size : table.size = n
  index : ∀ i : Fin n, (table[i.val]'(by rw [size]; exact i.isLt)).1 = i

namespace Memo

variable {n : Nat} {T : Fin n → Type}

/-- Evaluate the family once. -/
def build (get : (i : Fin n) → T i) : Memo T where
  table := Array.ofFn fun i => (⟨i, get i⟩ : Sigma T)
  size := Array.size_ofFn
  index := fun i => by simp only [Array.getElem_ofFn]

/-- Read one entry. -/
def get (m : Memo T) (i : Fin n) : T i :=
  m.index i ▸ (m.table[i.val]'(by rw [m.size]; exact i.isLt)).2

/-- An entry stored with index `i` reads back as its value. -/
private theorem cast_entry (i : Fin n) (value : T i) :
    ∀ (entry : Sigma T) (same : entry.1 = i), entry = ⟨i, value⟩ → same ▸ entry.2 = value := by
  intro entry same equal
  subst equal
  rfl

/-- **Reading the table is the family.** -/
theorem build_get (get : (i : Fin n) → T i) (i : Fin n) : (build get).get i = get i :=
  cast_entry i (get i) _ _ (by simp only [build, Array.getElem_ofFn])

end Memo

/-- Selection by index without visiting the smaller indices: `Fin.cases` runs an induction up
    to the index, which is exponential for a family built by nested selections. -/
def casesDirekt {n : Nat} {motive : Fin (n + 1) → Type} (zero : motive 0)
    (succ : (i : Fin n) → motive i.succ) : (i : Fin (n + 1)) → motive i
  | ⟨0, _⟩ => zero
  | ⟨i + 1, h⟩ => succ ⟨i, Nat.lt_of_succ_lt_succ h⟩

/-- The direct selection is `Fin.cases`. -/
theorem casesDirekt_eq {n : Nat} {motive : Fin (n + 1) → Type} (zero : motive 0)
    (succ : (i : Fin n) → motive i.succ) : casesDirekt zero succ = Fin.cases zero succ := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ j => rfl

end Gabbro.Grammatik.Parser
