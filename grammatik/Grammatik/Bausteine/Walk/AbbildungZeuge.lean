module

public import Grammatik.Bausteine.Walk.Abbildung

@[expose] public section

/-
  File:       Grammatik/Bausteine/Walk/AbbildungZeuge.lean
  Subject:    WITNESSES of `Walk/Abbildung.lean`: a two-level walk of arity two whose root holds a descendable
              non-leaf, and a leaf that is also `dwhen` with a child table (the leaf wins, the descent stops).
-/

namespace Gabbro.Grammatik

/-- Entries are numbers: `1` and `10` are leaves; `0` and `1` are `dwhen`; `0` and `1` have a child table. -/
def zeugeWalkKinder : Fin 2 → Nat := fun k => 10 + k.val

def zeugeWalk : WalkTree Nat 2 where
  leaf := fun e => e == 1 || e == 10
  dwhen := fun e => e == 0 || e == 1
  down := fun e => if e == 0 || e == 1 then some zeugeWalkKinder else none

def zeugeWalkWurzel : Fin 2 → Nat := fun k => k.val

/-- Entry `0` is descended into and yields `10` at the path `[0, 0]` (entry `11` is a non-leaf without `dwhen`);
    entry `1` is a leaf and a `dwhen` entry with a child table, and still yields exactly one mapping, at `[1]`. -/
theorem zeugeWalk_besuche :
    visitT zeugeWalk 1 zeugeWalkWurzel = [([0, 0], 10), ([1], 1)] := by decide

/-- The same list through the exact enumeration theorem: the mapping `10` at `[0, 0]` is a hit. -/
theorem zeugeWalk_treffer : WalkHit zeugeWalk 1 zeugeWalkWurzel [0, 0] 10 :=
  (visitT_mem_iff zeugeWalk 1 zeugeWalkWurzel [0, 0] 10).mp (by rw [zeugeWalk_besuche]; decide)

/-- No child of the leaf entry `1` is visited. -/
theorem zeugeWalk_blatt_stoppt : ¬ WalkHit zeugeWalk 1 zeugeWalkWurzel [1, 0] 10 := fun h =>
  absurd ((visitT_mem_iff zeugeWalk 1 zeugeWalkWurzel [1, 0] 10).mpr h)
    (by rw [zeugeWalk_besuche]; decide)

/-- The shape of the fixture mapping: two entry fields, three levels of arity four. -/
def zeugeForm : WalkShape where
  levels := 3
  arity := 4
  entry := [.int 0 255, .bool]
  levels_pos := by decide

theorem zeugeForm_felder : zeugeForm.mappingFields.length = 5 := by decide

/-- The path `[1, 2]` (root entry 1, then entry 2) lies at level 1 and has the radix prefix 6, so `va = 6 * 4`. -/
theorem zeugeForm_va : walkVa 3 4 [(1 : Fin 4), (2 : Fin 4)] = 24 := by decide

theorem zeugeForm_va_klein : walkVa 3 4 [(1 : Fin 4), (2 : Fin 4)] < 4 ^ 3 :=
  walkVa_lt 3 4 _ (by decide) (by decide)

/-- Below the entry's level the `index` array is zero and the active suffix carries the path. -/
theorem zeugeForm_index :
    walkIndexAt 3 [(1 : Fin 4), (2 : Fin 4)] 0 = 0 ∧ walkIndexAt 3 [(1 : Fin 4), (2 : Fin 4)] 1 = 2 ∧
    walkIndexAt 3 [(1 : Fin 4), (2 : Fin 4)] 2 = 1 := by decide

end Gabbro.Grammatik
