/-
  File:      Grammatik/Niedrig/Uebersetzung/Zeuge.lean
  Subject:   WITNESS FOR THE NEUTRAL WALK (L6a): a two-level regime with 2
    bits per level and 4 offset bits, one second-level table, two leaves of
    one frame (an alias), faults, a map frame instance, and alias survival.

  The accepted walks and the fault compute by `rfl`; the map frame instance
  and the alias survival after `unmap` are `rfl` equalities on these small
  terms. Both leaves name frame 42, so address 0 and address 64 are aliases;
  unmapping the leaf of address 0 leaves address 64 translating.
-/
module

public import Grammatik.Niedrig.Uebersetzung.Eigenschaften

@[expose] public section


namespace Gabbro.Grammatik.Niedrig.Uebersetzung

/-- The witness regime: two levels, two index bits, four offset bits. -/
def wRegime : Regime :=
  { levels := 2
    levels_pos := by decide
    bits := 2
    bits_pos := by decide
    offsetBits := 4 }

/-- Full permissions. -/
def wPermFull : Perm :=
  { read := true
    write := true
    exec := false }

/-- Read-only permissions. -/
def wPermRead : Perm :=
  { read := true
    write := false
    exec := false }

/-- No permissions. -/
def wPermNone : Perm :=
  { read := false
    write := false
    exec := false }

/-- The witness tables: root 0 links index 0 to table 1; table 1 holds two
    leaves of frame 42 at indices 0 and 1. -/
def wTables : Tables :=
  fun t i =>
    if t = 0 then
      if i = 0 then Entry.table 1
      else Entry.absent
    else if t = 1 then
      if i = 0 then Entry.leaf 42 wPermFull
      else if i = 1 then Entry.leaf 42 wPermRead
      else Entry.absent
    else Entry.absent

/-- Address 0 walks to frame 42 with full permissions. -/
theorem w_walk_a1 :
    walk wRegime wTables 0 0 = Option.some (42, wPermFull) := by
  rfl

/-- Address 64 walks to frame 42 with read-only permissions. -/
theorem w_walk_a2 :
    walk wRegime wTables 0 64 = Option.some (42, wPermRead) := by
  rfl

/-- Address 128 faults: the second index names no leaf. -/
theorem w_fault_absent :
    walk wRegime wTables 0 128 = Option.none := by
  rfl

/-- Address 16 faults: the root index names no table. -/
theorem w_fault_root :
    walk wRegime wTables 0 16 = Option.none := by
  rfl

/-- Addresses 0 and 64 are aliases: both name frame 42. -/
theorem w_alias : Alias wRegime wTables 0 0 64 :=
  ⟨42, wPermFull, wPermRead, w_walk_a1, w_walk_a2⟩

/-- Mapping the unvisited entry (1, 2) keeps the walk of address 0. -/
theorem w_frame_map :
    walk wRegime (mapEntry wTables 1 2 99 wPermFull) 0 0 =
      Option.some (42, wPermFull) := by
  rfl

/-- Unmapping the leaf of address 0 leaves the alias translating. -/
theorem w_alias_survives :
    walk wRegime (unmapEntry wTables 1 0) 0 64 =
      Option.some (42, wPermRead) := by
  rfl

/-- Protecting entry (1, 1) with execute-only meets to no permissions. -/
theorem w_protect_weaker :
    walk wRegime
      (protectEntry wTables 1 1
        { read := false
          write := false
          exec := true }) 0 64 =
      Option.some (42, wPermNone) := by
  rfl

#print axioms Gabbro.Grammatik.Niedrig.Uebersetzung.w_walk_a1
#print axioms Gabbro.Grammatik.Niedrig.Uebersetzung.w_alias
#print axioms Gabbro.Grammatik.Niedrig.Uebersetzung.w_alias_survives

end Gabbro.Grammatik.Niedrig.Uebersetzung
