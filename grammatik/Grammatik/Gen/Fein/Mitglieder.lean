/-
  File:      Grammatik/Gen/Fein/Mitglieder.lean
  Subject:   THE DECLARATIONS OF THE FINE CELLS: a child of an expression position of any type needs a carrier, a
             parameter, a register of every type class. They are built from one representative type per class
             (`vertreter`, one per constructor of `Ty`), not written per cell.
-/
import Grammatik.Gen.Abdeckung.Waehlen
import Grammatik.Gen.Fein.Zellen

namespace Gabbro.Grammatik.Gen.Fein

open Gabbro.Grammatik Gabbro.Grammatik.Gen

/-- One representative type per type class, in the order of `Ty.kopf`. -/
def vertreter : List Ty :=
  [.int 0 0, .bool, .opt 1, .sum [none, some (0, 1)], .why 2, .never, .fl (0, 1) (1, 1), .fnptr 0, .ptr 0 true]

theorem vertreter_koepfe : vertreter.map Ty.kopf = List.range 9 := by decide

/-- The carrier types in three groups (the generator is quadratic in what one declaration offers): the
    integers with the ranges the operators need exactly (`int 0 0` for a literal `0`, `int 0 1` for a shift of width
    one, a byte for `getBytes`), the finite classes, the rest. -/
def gruppen : List (List Ty) :=
  [[.int 0 0, .int 0 1, .int 0 255], [.bool, .opt 1, .sum [none, some (0, 1)], .why 2],
   [.never, .fl (0, 1) (1, 1), .fnptr 0, .ptr 0 true]]

theorem gruppen_vertreter : vertreter ⊆ gruppen.flatten := by decide

/-- Expressions: a table and statics of the group, parameters of the group (a second table with a chain field and a
    byte for `reaches` and the bytes). -/
def ausdruck (g : List Ty) : Spez where
  tabs := [{ count := 1, felder := g.map fun τ => { typ := τ } },
           { count := 2, felder := [{ typ := .opt 2 }, { typ := .int 0 255 }] }]
  globs := g.map fun τ => { typ := τ }
  sigs := [{ params := g, schreibt := [0, 1], gschreibt := List.range g.length }]

/-- Registers of the group. -/
def register (g : List Ty) : Spez where
  tabs := [{ count := 1, felder := g.map fun τ => { typ := τ } }]
  regs := g.map fun τ => { typ := τ, klasse := .rw }
  sigs := [{ params := g, schreibt := [0] }]

/-- Atomics of the group: exchanged, awaited, published with a payload. -/
def atomar (g : List Ty) : Spez where
  tabs := [{ count := 1, felder := g.map fun τ => { typ := τ } }]
  globs := g.map (fun τ => { typ := τ, atomar := true, nutzlast := [g.length] }) ++ [{ typ := .int 0 0 }]
  sigs := [{ params := g, gschreibt := List.range (g.length + 1) }]

/-- **The fine members**: for every group the three declarations. -/
def feinMitglieder : List Spez :=
  (gruppen.flatMap fun g => [ausdruck g, register g, atomar g]).map Spez.einzeln

end Gabbro.Grammatik.Gen.Fein
