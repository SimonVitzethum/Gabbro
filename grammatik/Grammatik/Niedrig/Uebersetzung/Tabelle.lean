/-
  File:      Grammatik/Niedrig/Uebersetzung/Tabelle.lean
  Subject:   TABLES AS ABSTRACT DATA (L6a): permissions, entries, the `walk`
    over the index list, the visited list, and one-entry updates
    (map/unmap/protect).

  Leaves live only at the last level: `walkAux` faults (`Option.none`) on
  `Entry.absent`, on a leaf before the last level, and on a `table` entry at
  the last level. Table and frame identities are abstract `Nat`s, never
  pointers. Revocation note (LOW-LEVEL-SYNTAX-PLAN): "Remapping, reuse and
  revocation require quiescence of all affected references and cores, with
  epoch changes and proved TLB synchronization." This package proves the
  alias half of that reason (in `Eigenschaften.lean`): unmapping one path
  leaves an alias translating, so revocation needs more than one unmap.
-/
module

public import Grammatik.Niedrig.Uebersetzung.Regime

@[expose] public section


namespace Gabbro.Grammatik.Niedrig.Uebersetzung

/-- Read/write/execute permissions of a leaf. -/
structure Perm where
  read : Bool
  write : Bool
  exec : Bool
  deriving DecidableEq

/-- Fewer permissions: every set bit of the first is set in the second. -/
def Perm.le (a b : Perm) : Prop :=
  (a.read = true → b.read = true) ∧
  (a.write = true → b.write = true) ∧
  (a.exec = true → b.exec = true)

/-- The meet of two permissions, bit by bit. -/
def Perm.meet (a b : Perm) : Perm :=
  { read := a.read && b.read
    write := a.write && b.write
    exec := a.exec && b.exec }

/-- A table entry: absent, a table link, or a last-level leaf. -/
inductive Entry where
  | absent : Entry
  | table : Nat → Entry
  | leaf : Nat → Perm → Entry
  deriving DecidableEq

/-- Tables: a table identity and an index give an entry. -/
abbrev Tables :=
  Nat → Nat → Entry

/-- The walk over the index list. Leaves answer only at the last level. -/
def walkAux (T : Tables) : List Nat → Nat → Option (Nat × Perm)
  | [], _ => Option.none
  | i :: rest, cur =>
    match T cur i with
    | Entry.absent => Option.none
    | Entry.table nxt =>
      match rest with
      | [] => Option.none
      | _ :: _ => walkAux T rest nxt
    | Entry.leaf f p =>
      match rest with
      | [] => Option.some (f, p)
      | _ :: _ => Option.none

/-- The walk of an address from a root table. -/
def walk (R : Regime) (T : Tables) (root a : Nat) : Option (Nat × Perm) :=
  walkAux T (R.indices a) root

/-- The visited (table, index) pairs, head first, by the same recursion. -/
def visitedAux (T : Tables) : List Nat → Nat → List (Nat × Nat)
  | [], _ => []
  | i :: rest, cur =>
    (cur, i) :: (match T cur i with
      | Entry.table nxt =>
        match rest with
        | [] => []
        | _ :: _ => visitedAux T rest nxt
      | Entry.absent => []
      | Entry.leaf _ _ => [])

/-- The visited pairs of an address walk. -/
def visited (R : Regime) (T : Tables) (root a : Nat) : List (Nat × Nat) :=
  visitedAux T (R.indices a) root

/-- Set ONE entry. -/
def setEntry (T : Tables) (tbl idx : Nat) (e : Entry) : Tables :=
  fun t i => if t = tbl then (if i = idx then e else T t i) else T t i

/-- `map`: set one entry to a leaf. -/
def mapEntry (T : Tables) (tbl idx frame : Nat) (p : Perm) : Tables :=
  setEntry T tbl idx (Entry.leaf frame p)

/-- `unmap`: set one entry to absent. -/
def unmapEntry (T : Tables) (tbl idx : Nat) : Tables :=
  setEntry T tbl idx Entry.absent

/-- `protect`: meet the leaf permissions at one entry, keep the rest. -/
def protectEntry (T : Tables) (tbl idx : Nat) (q : Perm) : Tables :=
  fun t i =>
    if t = tbl then
      (if i = idx then
        (match T t i with
        | Entry.leaf f p => Entry.leaf f (Perm.meet p q)
        | e => e)
      else T t i)
    else T t i

/-- One `&&` never yields `true` without its left side. -/
theorem bool_and_le_left (x y : Bool) :
    ((x && y) = true → x = true) := by
  intro h
  cases hx : x with
  | true =>
    rfl
  | false =>
    rw [hx] at h
    cases h

/-- One `&&` never yields `true` without its right side. -/
theorem bool_and_le_right (x y : Bool) :
    ((x && y) = true → y = true) := by
  intro h
  cases hx : x with
  | true =>
    rw [hx] at h
    exact h
  | false =>
    rw [hx] at h
    cases h

/-- The meet never yields more than the left permissions. -/
theorem Perm.meet_le_left (a b : Perm) : (Perm.meet a b).le a := by
  unfold Perm.meet Perm.le
  exact ⟨bool_and_le_left _ _, bool_and_le_left _ _, bool_and_le_left _ _⟩

/-- The meet never yields more than the right permissions. -/
theorem Perm.meet_le_right (a b : Perm) : (Perm.meet a b).le b := by
  unfold Perm.meet Perm.le
  exact ⟨bool_and_le_right _ _, bool_and_le_right _ _, bool_and_le_right _ _⟩

/-- Permissions imply themselves. -/
theorem Perm.le_refl (a : Perm) : a.le a := by
  unfold Perm.le
  exact ⟨fun h => h, fun h => h, fun h => h⟩

/-- The set entry answers at its own address. -/
theorem setEntry_hit (T : Tables) (tbl idx : Nat) (e : Entry) :
    setEntry T tbl idx e tbl idx = e := by
  unfold setEntry
  rw [if_pos rfl, if_pos rfl]

/-- The set entry keeps other tables. -/
theorem setEntry_miss_table (T : Tables) (tbl idx : Nat) (e : Entry)
    (t i : Nat) (h : t ≠ tbl) :
    setEntry T tbl idx e t i = T t i := by
  unfold setEntry
  rw [if_neg h]

/-- The set entry keeps other indices. -/
theorem setEntry_miss_index (T : Tables) (tbl idx : Nat) (e : Entry)
    (i : Nat) (h2 : i ≠ idx) :
    setEntry T tbl idx e tbl i = T tbl i := by
  unfold setEntry
  rw [if_pos rfl, if_neg h2]

#print axioms Gabbro.Grammatik.Niedrig.Uebersetzung.Perm.meet_le_left
#print axioms Gabbro.Grammatik.Niedrig.Uebersetzung.setEntry_hit

end Gabbro.Grammatik.Niedrig.Uebersetzung
