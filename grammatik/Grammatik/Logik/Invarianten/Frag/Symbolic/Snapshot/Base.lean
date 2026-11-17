module

public import Grammatik.Logik.Invarianten.Frag.Symbolic.Scope

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Frag.Symbolic.Snapshot

structure Region (D : Deklaration) (bound : Nat) where
  start : Nat
  names : List (Observation D)
  within : start + names.length ≤ bound

def regionNames (region : Option (Region D bound)) : List (Observation D) :=
  match region with | none => [] | some value => value.names

def regionStart (region : Option (Region D bound)) : Nat :=
  match region with | none => 0 | some value => value.start

/-- Entry observations occupy a fresh immutable interval. Repeated reads use
    the first matching key; separate entries can never alias by allocation. -/
def lookup (start : Nat) : List (Observation D) → Observation D → Option Nat
  | [], _ => none
  | head :: tail, key => if key = head then some start else lookup (start + 1) tail key

def Realizes (start : Nat) : List (Observation D) → Assignment Nat → World D → Prop
  | [], _, _ => True
  | head :: tail, valuation, world =>
      valuation start = assignment world head ∧ Realizes (start + 1) tail valuation world

def extend (start : Nat) : List (Observation D) → Assignment Nat → World D → Assignment Nat
  | [], valuation, _ => valuation
  | head :: tail, valuation, world =>
      extend (start + 1) tail (valuation.bind start (assignment world head)) world

theorem extend_preserves (names : List (Observation D)) (start : Nat)
    (valuation : Assignment Nat) (world : World D) (key : Nat)
    (outside : key < start ∨ start + names.length ≤ key) :
    extend start names valuation world key = valuation key := by
  induction names generalizing start valuation with
  | nil => rfl
  | cons head tail ih =>
      have different : key ≠ start := by simp only [List.length_cons] at outside; omega
      have later : key < start + 1 ∨ start + 1 + tail.length ≤ key := by
        simp only [List.length_cons] at outside
        omega
      change extend (start + 1) tail _ world key = _
      rw [ih (start + 1) _ later]
      simp only [Assignment.bind, different, ↓reduceIte]

theorem extend_realizes (names : List (Observation D)) (start : Nat)
    (valuation : Assignment Nat) (world : World D) :
    Realizes start names (extend start names valuation world) world := by
  induction names generalizing start valuation with
  | nil => trivial
  | cons head tail ih =>
      change extend (start + 1) tail _ world start = assignment world head ∧ _
      constructor
      · rw [extend_preserves tail (start + 1) _ world start (Or.inl (Nat.lt_succ_self start))]
        exact Elim.Korrekt.bind_same valuation start (assignment world head)
      · exact ih (start + 1) _

theorem realizes_congr (names : List (Observation D)) (start : Nat)
    (valuation other : Assignment Nat) (world : World D)
    (agree : ∀ key, start ≤ key → key < start + names.length → valuation key = other key) :
    Realizes start names valuation world ↔ Realizes start names other world := by
  induction names generalizing start with
  | nil => rfl
  | cons head tail ih =>
      change (_ ∧ _) ↔ (_ ∧ _)
      have first := agree start (Nat.le_refl _) (by simp only [List.length_cons]; omega)
      rw [first]
      exact and_congr Iff.rfl (ih (start + 1) (fun key lower upper =>
        agree key (by omega) (by simp only [List.length_cons]; omega)))

theorem lookup_sound (names : List (Observation D)) (start : Nat)
    (key : Observation D) (index : Nat) (found : lookup start names key = some index)
    (valuation : Assignment Nat) (world : World D) (realized : Realizes start names valuation world) :
    valuation index = assignment world key := by
  induction names generalizing start with
  | nil => cases found
  | cons head tail ih =>
      by_cases same : key = head
      · simp only [lookup, same, ↓reduceIte, Option.some.injEq] at found
        subst index
        exact same ▸ realized.1
      · exact ih (start + 1) (by simpa only [lookup, same, ↓reduceIte] using found) realized.2

def equations (start : Nat) : List (Observation D) → LProp (Key D Nat)
  | [] => .tru
  | head :: tail => .and (.eq (.var (.inr start)) (.var (.inl head))) (equations (start + 1) tail)

theorem equations_denote (names : List (Observation D)) (start : Nat)
    (valuation : Assignment Nat) (world : World D) :
    (equations start names).denote (values valuation world) ↔ Realizes start names valuation world := by
  induction names generalizing start with
  | nil => rfl
  | cons head tail ih => exact and_congr Iff.rfl (ih (start + 1))

end Gabbro.Grammatik.Invarianten.Frag.Symbolic.Snapshot
