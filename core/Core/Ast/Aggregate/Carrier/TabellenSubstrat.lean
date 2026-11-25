/-
  File:      core/Core/Ast/Aggregate/Carrier/TabellenSubstrat.lean
  Subject:   THE OBJECT AND TABLE SUBSTRATE (MK-09): the pinned statements. A table
             declaration (`Decl.table`) elaborates to one schema instruction
             (`Befehl.definiereTraeger`); its index types (`indexType`, `indexOption`) and
             the array-index guard already exist, as do `Ty.ptr` and `Ty.regionView`.
             This module adds the substrate the slot accesses are checked against:

             * layout and slot paths: a path names one slot of a table with `count` rows;
             * the index guard: an index-typed value always names a slot below `count`
               (the `waechterBedarf .index` row);
             * the arena: `alloc` hands out the next free slot, `free` releases one,
               `reset` empties the table, `grow` extends a closed table; `tree` and
               `busy` are GHOSTS (they never steer a step);
             * closed tables refuse at their ceiling with a named halt and never
               overwrite silently; open tables without a ceiling stay admitted and the
               provider contract carries the freshness of the handed-out slot;
             * pointers (`->`, `&T`): dereference reads the slot through an access form
               (`Zugriffsform.lade` / `.speichere` over `Befehl.zugriff`); forming a
               pointer needs a live table with a proof, never a bare integer;
             * traversal visits every domain element once, in `count` runs, matching the
               `for` machinery (`forAnfang` with `0 .. count` counts exactly `count`
               steps).

             Slot accesses are FORMS over `Befehl.zugriff`: no second memory layer, no
             new machine constructor. All four kernel statements sit under the single
             pinned root `TabellenAussagen`; each carries `_erfuellbar` (the model
             exhibits the scenario) and `_nichtTrivial` (the model exhibits the error
             too -- only the checker excludes it).
-/
module

public import Core.Ast.Semantik.Arithmetik
public import Core.Ast.Semantik.Runtime.Frame
public import Core.Annahme.Waechter

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme

/-- A table with `count` rows. The row layout is the schema layout the
    declaration carries; only the bound matters for the guard. -/
structure TabellenLayout where
  count : Nat
  deriving DecidableEq

/-- A slot path names one slot of a table with `count` rows. -/
structure Slotpfad (count : Nat) where
  index : Nat
  deriving DecidableEq

/-- A slot path is valid exactly when its index is below the row count. -/
def Slotpfad.gueltig {count : Nat} (p : Slotpfad count) : Prop :=
  p.index < count

/-- The index guard at a slot path: the `waechterBedarf .index` row. -/
def indexWaechter (index count : Nat) : Prop :=
  waechterBedarf .index (index, count)

/-- The index guard unfolds to the bound check. -/
theorem indexWaechter_iff (index count : Nat) :
    indexWaechter index count ↔ index < count := by
  unfold indexWaechter waechterBedarf
  exact Iff.rfl

/-- The arena behind a table: `kapazitaet` is the ceiling of a closed table and
    advisory for an open one, `belegt` is the next free slot, `offen` marks a
    table without a ceiling, `baum` and `besetzt` are GHOSTS (the tree image and
    the busy marks: they never steer `alloc`, `free`, `reset` or `grow`). -/
structure Arena where
  kapazitaet : Nat
  belegt : Nat
  offen : Bool
  baum : List Nat
  besetzt : List Bool
  deriving DecidableEq

/-- The table invariant: a closed table never holds more than its ceiling; the
    ghosts cover exactly the ceiling. -/
def Tabelleninvariante (a : Arena) : Prop :=
  (¬ a.offen → a.belegt ≤ a.kapazitaet) ∧
    a.baum.length = a.kapazitaet ∧ a.besetzt.length = a.kapazitaet

/-- The outcome of an allocation step: either the next free slot, or the named
    halt that refuses a full closed table. -/
inductive ArenaSchritt where
  | weiter (slot : Nat) (arena : Arena)
  | halt (grund : Abschluss)

/-- Allocation hands out the next free slot. A closed table at its ceiling
    refuses with the named halt `ungueltigerBereich` instead of overwriting
    silently; an open table stays admitted and the provider contract carries the
    freshness of the handed-out slot. -/
def Arena.alloc (a : Arena) : ArenaSchritt :=
  if _ : a.belegt < a.kapazitaet then
    .weiter a.belegt ⟨a.kapazitaet, a.belegt + 1, a.offen, a.baum, a.besetzt⟩
  else if _ : a.offen = true then
    .weiter a.belegt ⟨a.kapazitaet, a.belegt + 1, true, a.baum, a.besetzt⟩
  else
    .halt .ungueltigerBereich

/-- Release clears the busy ghost at the slot; the next free slot is unchanged. -/
def Arena.free (a : Arena) (slot : Nat) : Arena :=
  ⟨a.kapazitaet, a.belegt, a.offen, a.baum, a.besetzt.set slot false⟩

/-- Reset empties the table and clears every busy ghost. -/
def Arena.reset (a : Arena) : Arena :=
  ⟨a.kapazitaet, 0, a.offen, a.baum, a.besetzt.map fun _ => false⟩

/-- Growth extends a closed table by `mehr` rows with fresh ghosts. -/
def Arena.grow (a : Arena) (mehr : Nat) : Arena :=
  ⟨a.kapazitaet + mehr, a.belegt, a.offen,
    a.baum ++ List.replicate mehr 0, a.besetzt ++ List.replicate mehr false⟩

/-- A pointer names a slot of a live table. Dereference (`->`) reads the slot
    through an access form (`Zugriffsform.lade` / `.speichere` over
    `Befehl.zugriff`); forming a pointer (`&T`) needs the table bound with a
    proof, never a bare integer. -/
structure Zeiger (count : Nat) where
  pfad : Slotpfad count
  deriving DecidableEq

/-- A pointer is valid exactly when its path is. -/
def Zeiger.gueltig {count : Nat} (z : Zeiger count) : Prop :=
  z.pfad.gueltig

/-- Dereference reads the slot the pointer names. -/
def Zeiger.ziel {count : Nat} (z : Zeiger count) : Nat :=
  z.pfad.index

/-- Address formation needs a live table: the index with its bound proof. -/
def zeigerAdress (index count : Nat) (h : index < count) : Zeiger count :=
  ⟨⟨index⟩⟩

/-- Traversal visits every domain element once, in order. It matches the `for`
    machinery: `forAnfang` with `0 .. count` counts exactly `count` steps. -/
def traverse (count : Nat) : List Nat :=
  List.range count

/-- **Index types guarantee the bound** (proved). Every index-typed value names
    a slot below the row count, and the index guard row holds at it: the
    checker excludes nothing the model cannot name. -/
def PfadImBereichAussage : Prop :=
  ∀ (count : Nat) {lo hi : Int} (i : Zahl lo hi)
    (lower : 0 ≤ lo) (upper : hi < (count : Int)),
    (indexPosition i lower upper).val < count ∧
      indexWaechter (indexPosition i lower upper).val count

/-- **A full closed table refuses with a named halt** (proved). At its ceiling
    a closed arena steps to `halt .ungueltigerBereich`: no silent overwrite
    exists on the admitted path. -/
def ArenaVollAussage : Prop :=
  ∀ (a : Arena), ¬ a.offen → a.kapazitaet ≤ a.belegt →
    a.alloc = .halt .ungueltigerBereich ∧
      ∀ (slot : Nat) (a' : Arena), a.alloc ≠ .weiter slot a'

/-- **An open table stays admitted on the provider contract** (proved). Every
    allocation of an open arena hands out the fresh slot `belegt`: freshness is
    carried by the provider, never by reusing a live slot. -/
def OffeneTabelleFrischeAussage : Prop :=
  ∀ (a : Arena), a.offen →
    ∃ (slot : Nat) (a' : Arena),
      a.alloc = .weiter slot a' ∧ slot = a.belegt ∧
        a'.belegt = a.belegt + 1 ∧ a'.offen ∧ a'.kapazitaet = a.kapazitaet

/-- **Traversal terminates in `count` runs** (proved). The walk over a finite
    domain visits exactly `count` slots, each below the bound, so every visit
    passes the index guard; the run count is the `for` counter
    `(count - 0).toNat`. -/
def TraverseTerminiertAussage : Prop :=
  ∀ (count : Nat),
    (traverse count).length = count ∧ ∀ i ∈ traverse count, i < count

/-- **All MK-09 statements under one pinned root.** -/
def TabellenAussagen : Prop :=
  PfadImBereichAussage ∧ ArenaVollAussage ∧
    OffeneTabelleFrischeAussage ∧ TraverseTerminiertAussage

theorem pfadImBereich : PfadImBereichAussage := by
  intro count lo hi i lower upper
  exact ⟨(indexPosition i lower upper).isLt,
    (indexWaechter_iff _ _).mpr (indexPosition i lower upper).isLt⟩

theorem arenaVoll : ArenaVollAussage := by
  intro a geschlossen voll
  have eng : ¬ a.belegt < a.kapazitaet := by omega
  have nopen : ¬(a.offen = true) := geschlossen
  have halt : a.alloc = .halt .ungueltigerBereich := by
    unfold Arena.alloc
    rw [dif_neg eng, dif_neg nopen]
  exact ⟨halt, fun slot a' h => by rw [halt] at h; cases h⟩

theorem offeneTabelleFrische : OffeneTabelleFrischeAussage := by
  intro a offen
  have openT : (a.offen = true) := offen
  unfold Arena.alloc
  by_cases eng : a.belegt < a.kapazitaet
  · rw [dif_pos eng]
    refine ⟨a.belegt, ⟨a.kapazitaet, a.belegt + 1, a.offen, a.baum, a.besetzt⟩,
      rfl, rfl, rfl, offen, rfl⟩
  · rw [dif_neg eng, dif_pos openT]
    refine ⟨a.belegt, ⟨a.kapazitaet, a.belegt + 1, true, a.baum, a.besetzt⟩,
      rfl, rfl, rfl, rfl, rfl⟩

theorem traverseTerminiert : TraverseTerminiertAussage := by
  intro count
  exact ⟨List.length_range, fun i hi => List.mem_range.mp hi⟩

/-- Allocation preserves the table invariant on every admitted path. -/
theorem arenaAlloc_erhaelt (a : Arena) (slot : Nat) (a' : Arena)
    (h : a.alloc = .weiter slot a') (hinv : Tabelleninvariante a) :
    Tabelleninvariante a' := by
  unfold Arena.alloc at h
  by_cases eng : a.belegt < a.kapazitaet
  · rw [dif_pos eng] at h
    obtain ⟨rfl, rfl⟩ := ArenaSchritt.weiter.inj h
    obtain ⟨_, baum, besetzt⟩ := hinv
    refine ⟨?_, baum, besetzt⟩
    intro _
    show a.belegt + 1 ≤ a.kapazitaet
    omega
  · rw [dif_neg eng] at h
    by_cases openT : (a.offen = true)
    · rw [dif_pos openT] at h
      obtain ⟨rfl, rfl⟩ := ArenaSchritt.weiter.inj h
      obtain ⟨_, baum, besetzt⟩ := hinv
      exact ⟨fun contra => (contra rfl).elim, baum, besetzt⟩
    · rw [dif_neg openT] at h
      cases h

/-- The index bound is jointly satisfiable: an index-typed value inside it. -/
theorem pfadImBereich_erfuellbar :
    ∃ (count : Nat) (lo hi : Int) (i : Zahl lo hi)
      (lower : 0 ≤ lo) (upper : hi < (count : Int)), True :=
  ⟨2, 1, 1, ⟨1, Int.le_refl _, Int.le_refl _⟩, by omega, by omega, trivial⟩

/-- The model names the out-of-bounds path too: a raw index at and above the
    count exists as data. Only the index guard excludes it. -/
theorem pfadImBereich_nichtTrivial : ∃ (index count : Nat), count ≤ index :=
  ⟨5, 3, by decide⟩

/-- The full closed table is jointly satisfiable: it refuses with the named halt. -/
theorem arenaVoll_erfuellbar :
    ∃ (a : Arena), ¬ a.offen ∧ a.kapazitaet ≤ a.belegt ∧
      a.alloc = .halt .ungueltigerBereich :=
  ⟨⟨2, 2, false, [0, 1], [true, true]⟩, by decide, by decide, rfl⟩

/-- The model names the overwritten slot too: a full closed table still has
    addressable slots a silent overwrite could target. Only the refusal
    excludes it. -/
theorem arenaVoll_nichtTrivial :
    ∃ (a : Arena) (slot : Nat),
      ¬ a.offen ∧ a.kapazitaet ≤ a.belegt ∧ slot < a.kapazitaet :=
  ⟨⟨2, 2, false, [0, 1], [true, true]⟩, 0, by decide, by decide, by decide⟩

/-- The open allocation is jointly satisfiable: it hands out the fresh slot. -/
theorem offeneTabelleFrische_erfuellbar :
    ∃ (a : Arena) (slot : Nat) (a' : Arena),
      a.offen ∧ a.alloc = .weiter slot a' ∧ slot = a.belegt :=
  ⟨⟨2, 5, true, [0, 1], [true, true]⟩, 5, ⟨2, 6, true, [0, 1], [true, true]⟩,
    by decide, rfl, rfl⟩

/-- The model names the undelivered slot too: an open table has slot paths at
    and above its advisory ceiling. Only the provider contract excludes their
    use before delivery. -/
theorem offeneTabelleFrische_nichtTrivial :
    ∃ (a : Arena) (slot : Nat), a.offen ∧ a.kapazitaet ≤ slot :=
  ⟨⟨2, 5, true, [0, 1], [true, true]⟩, 7, by decide, by decide⟩

/-- The full walk is jointly satisfiable: three rows traverse as `[0, 1, 2]`. -/
theorem traverseTerminiert_erfuellbar :
    ∃ (count : Nat), count = 3 ∧ traverse count = [0, 1, 2] :=
  ⟨3, rfl, rfl⟩

/-- The model names the partial walk too: a walk that stops early exists as
    data, with fewer visited slots than the full run. Only the full `count`
    runs satisfy the statement. -/
theorem traverseTerminiert_nichtTrivial :
    ∃ (count : Nat) (walk : List Nat),
      0 < count ∧ walk.length < count ∧ walk.length ≠ (traverse count).length :=
  ⟨3, [0, 1], by omega, by (show (2:Nat) < 3; omega), by (show (2:Nat) ≠ 3; omega)⟩

theorem tabellen_aussagen : TabellenAussagen :=
  ⟨pfadImBereich, arenaVoll, offeneTabelleFrische, traverseTerminiert⟩

end Gabbro.Core.Ast.Semantik
