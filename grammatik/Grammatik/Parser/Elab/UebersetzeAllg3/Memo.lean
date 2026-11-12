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


/-- Whether a result is a value. -/
def wertDa {α : Type} : Except String α → Bool
  | .ok _ => true
  | .error _ => false

/-- The error of a result, if it is one. -/
def fehlerVon {α : Type} : Except String α → Option String
  | .ok _ => none
  | .error e => some e

namespace Memo

variable {n : Nat} {T : Fin n → Type}

/-- The values of a table of results that all succeeded. -/
def werte (m : Memo fun i => Except String (T i)) (h : ∀ i, wertDa (m.get i) = true) (i : Fin n) : T i :=
  match hr : m.get i with
  | .ok v => v
  | .error _ => by
    have bad := h i
    rw [hr] at bad
    exact Bool.noConfusion bad

/-- Every entry is its value. -/
theorem werte_get (m : Memo fun i => Except String (T i)) (h : ∀ i, wertDa (m.get i) = true) (i : Fin n) :
    m.get i = .ok (m.werte h i) := by
  unfold werte
  split
  · next v hr => exact hr
  · next e hr =>
    have bad := h i
    rw [hr] at bad
    exact Bool.noConfusion bad

end Memo

/-- Evaluate a dependent family of results once: the first error, or every value at its own index. -/
def sammle : (n : Nat) → (T : Fin n → Type) → ((i : Fin n) → Except String (T i)) →
    Except String ((i : Fin n) → T i)
  | 0, _, _ => pure (fun i => nomatch i)
  | n + 1, T, get => do
      let head ← get 0
      let tail ← sammle n (fun i => T i.succ) (fun i => get i.succ)
      pure (Fin.cases head tail)

/-- A family whose entries all succeed collects to its values. -/
theorem sammle_ok : ∀ (n : Nat) (T : Fin n → Type) (get : (i : Fin n) → Except String (T i))
    (v : (i : Fin n) → T i), (∀ i, get i = .ok (v i)) → sammle n T get = .ok v
  | 0, _, _, _, _ => congrArg Except.ok (funext fun i => nomatch i)
  | n + 1, T, get, v, h => by
    have ht := sammle_ok n (fun i => T i.succ) (fun i => get i.succ) (fun i => v i.succ)
      (fun i => h i.succ)
    simp only [sammle, h 0, ht, bind, Except.bind, pure, Except.pure]
    exact congrArg Except.ok (funext fun i => by
      cases i using Fin.cases with
      | zero => rfl
      | succ j => rfl)

/-- A family collects to its first error. -/
theorem sammle_fehler : ∀ (n : Nat) (T : Fin n → Type) (get : (i : Fin n) → Except String (T i))
    (e : String), (List.finRange n).findSome? (fun i => fehlerVon (get i)) = some e →
    sammle n T get = .error e
  | 0, _, _, _, h => by
    simp only [List.finRange_zero, List.findSome?_nil, reduceCtorEq] at h
  | n + 1, T, get, e, h => by
    rw [List.finRange_succ, List.findSome?_cons] at h
    cases h0 : get 0 with
    | error e0 =>
      simp only [h0, fehlerVon, Option.some.injEq] at h
      simp only [sammle, h0, h, bind, Except.bind]
    | ok v0 =>
      simp only [h0, fehlerVon, List.findSome?_map, Function.comp_def] at h
      have ht := sammle_fehler n (fun i => T i.succ) (fun i => get i.succ) e h
      simp only [sammle, h0, ht, bind, Except.bind]

/-- The collected family read from a table of the results. `sonst` is asked only when the table
    shows neither every value nor an error, which never happens (`sammle_eq_schnell`). -/
def sammleAus {n : Nat} {T : Fin n → Type} (table : Memo fun i => Except String (T i))
    (sonst : Unit → Except String ((i : Fin n) → T i)) : Except String ((i : Fin n) → T i) :=
  if h : (List.finRange n).all (fun i => wertDa (table.get i)) = true then
    .ok (table.werte fun i => List.all_eq_true.mp h i (List.mem_finRange i))
  else match (List.finRange n).findSome? (fun i => fehlerVon (table.get i)) with
    | some e => .error e
    | none => sonst ()

/-- `sammle` over a table filled once: every entry is evaluated at its own index and read directly.
    (The recursion passes `get i.succ` down, so entry `i` was reached through `i` closures.) -/
def sammleSchnell (n : Nat) (T : Fin n → Type) (get : (i : Fin n) → Except String (T i)) :
    Except String ((i : Fin n) → T i) :=
  sammleAus (Memo.build get) (fun _ => sammle n T get)

/-- **The table changes no collected family.** -/
@[csimp] theorem sammle_eq_schnell : @sammle = @sammleSchnell := by
  funext n T get
  unfold sammleSchnell sammleAus
  split
  · next h =>
    exact sammle_ok n T get _ fun i => by
      rw [← Memo.werte_get, Memo.build_get]
  · split
    · next e he =>
      simp only [Memo.build_get] at he
      exact sammle_fehler n T get e he
    · rfl
end Gabbro.Grammatik.Parser
