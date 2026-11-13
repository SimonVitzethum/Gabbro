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

/-- The table of a list, as a type with one inhabitant: a structure field of this type caches the table
    and leaves equality and printing of the structure to its other fields. -/
structure Fest (key : α → String) (xs : List α) where
  tafel : Tafel α key
  treu : tafel = von key xs

/-- The table of a list. -/
def fest (key : α → String) (xs : List α) : Fest key xs := ⟨von key xs, rfl⟩

instance (xs : List α) : DecidableEq (Fest key xs) := fun a b => isTrue (by
  cases a with
  | mk ta ha =>
    cases b with
    | mk tb hb =>
      subst ha
      subst hb
      rfl)

instance (xs : List α) : Repr (Fest key xs) := ⟨fun _ _ => "_"⟩

/-- The first entry of a name in a cached table is the first of its list. -/
theorem Fest.finde_eq {xs : List α} (t : Fest key xs) (name : String) :
    t.tafel.finde name = xs.find? (fun x => strEq (key x) name) := by
  rw [t.treu]
  rfl

end Tafel

/-- A cache: a value compiled code may read and no statement can tell from any other, because all
    values of the type are equal. A structure field of this type never enters an equality of the
    structure, and a record update that keeps a cache of other data stays correct: every reader
    answers the same for every cache (`Merk.lies`). -/
def Merk (α : Type) : Type := Quot (fun (_ _ : α) => True)

namespace Merk

variable {α β : Type}

/-- The cache holding a value. -/
def von (a : α) : Merk α := Quot.mk _ a

/-- All caches are equal. -/
theorem gleich (a b : Merk α) : a = b := by
  induction a using Quot.ind
  induction b using Quot.ind
  exact Quot.sound trivial

/-- Transform a cache; its contents remain unobservable except through a faithful reader. -/
def map (f : α → β) (m : Merk α) : Merk β :=
  Quot.lift (fun a => von (f a)) (fun _ _ _ => gleich _ _) m

instance : DecidableEq (Merk α) := fun a b => isTrue (gleich a b)

instance : Repr (Merk α) := ⟨fun _ _ => "_"⟩

/-- Read a cache with a function that answers the same for every value. -/
def lies (m : Merk α) (f : α → β) (h : ∀ a b, f a = f b) : β :=
  Quot.lift f (fun a b _ => h a b) m

/-- A reader that always answers `y` reads `y`. -/
theorem lies_eq (m : Merk α) (f : α → β) (h : ∀ a b, f a = f b) (y : β) (hy : ∀ a, f a = y) :
    m.lies f h = y := by
  induction m using Quot.ind
  exact hy _

end Merk

/-- How often each name occurs. -/
def zaehle (xs : List String) : Std.HashMap String Nat :=
  xs.foldr (fun s m => m.insert s (m.getD s 0 + 1)) ∅

/-- **The count of a name is the length of its occurrences.** -/
theorem zaehle_getD (xs : List String) (s : String) :
    (zaehle xs).getD s 0 = (xs.filter (fun t => strEq t s)).length := by
  induction xs with
  | nil => simp only [zaehle, List.foldr_nil, Std.HashMap.getD_empty, List.filter_nil, List.length_nil]
  | cons x xs ih =>
    unfold zaehle at ih ⊢
    rw [List.foldr_cons, Std.HashMap.getD_insert, List.filter_cons,
      congrFun (congrFun strEq_eq_schnell x) s]
    unfold strEqSchnell
    by_cases same : x = s
    · simp only [same, beq_self_eq_true, if_true, decide_true, List.length_cons, ih]
    · simp only [beq_iff_eq, same, if_false, decide_false, ih, Bool.false_eq_true]

end Gabbro.Grammatik.Parser
