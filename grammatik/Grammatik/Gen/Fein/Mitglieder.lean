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
    byte for `reaches` and the bytes); for every type of the group a callee that takes the group and answers that
    type, and one that may fail with a reason (calls, arguments and results of every class). -/
def ausdruck (g : List Ty) : Spez where
  tabs := [{ count := 1, felder := g.map fun τ => { typ := τ } },
           { count := 2, felder := [{ typ := .opt 2 }, { typ := .int 0 255 }] }]
  globs := g.map fun τ => { typ := τ }
  sigs := [{ params := g, schreibt := [0, 1], gschreibt := List.range g.length }] ++
    g.map (fun τ => { params := g, erg := some τ }) ++ [{ erg := g.head?, gruende := 1 }]
  fns := List.range (g.length + 2)

/-- As `ausdruck`, and the first function also takes a pointer to the first callee (indirect calls with a result). -/
def zeiger (g : List Ty) : Spez :=
  let a := ausdruck g
  { a with sigs := a.sigs.set 0 { a.sigs.getD 0 {} with params := g ++ [.fnptr 1] } }

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

/-- The ranges the divisors need: one that starts at one (a divisor of `div`/`rem`), and an EMPTY one (`int 0 (-1)`):
    over it `band`, `div`, `rem`, `shl`, `shr` have a range below zero and stand as the divisor of `sdiv`/`srem`. A
    program over an empty range is a program; the fine table asks for a valid witness of every cell such a program
    has, or a proof that none has it. -/
def teilerGruppe : List Ty := [.int 1 2, .int 0 (-1), .int 0 1]

/-- The features a combination member joins: a register with a promise, atomics, a function pointer, callees with a
    result (one that cannot fail, one with a reason), floats. -/
inductive Merkmal
  | reg | atom | zeiger | ruf | float
  deriving DecidableEq, Repr

/-- **A combination member**: one function that may read and write a table, and the features `ms` in one declaration,
    so that the block forms each feature brings (`regRead`/`regReadElse`, `awaits`/`exchange`, `bindCallInd`,
    `bindCall`/`bindCallElse`, the float blocks) can follow one another and stand in each other's branches. -/
def kombi (ms : List Merkmal) : Spez :=
  let hat := fun m => ms.contains m
  let rufe := hat .ruf || hat .zeiger
  { tabs := [{ count := 2, felder := [{ typ := .int 0 1 }, { typ := .int 0 255 }] }]
    globs := if hat .atom then [{ typ := .bool, atomar := true }, { typ := .int 0 1, atomar := true }] else []
    regs := if hat .reg then [{ typ := .int 0 1, klasse := .rw }] else []
    sigs := [{ params := [.int 0 1] ++ (if hat .float then [.fl (0, 1) (1, 1)] else []) ++
                 (if hat .zeiger then [.fnptr 1] else []),
               schreibt := [0], gschreibt := if hat .atom then [0, 1] else [] }] ++
      (if rufe then [{ params := [.int 0 1], erg := some (.int 0 1) },
                     { params := [.int 0 1], erg := some (.int 0 1), gruende := 1 }] else [])
    fns := List.range (if rufe then 3 else 1) }

/-- Every feature alone and every pair of features. -/
def kombiListen : List (List Merkmal) :=
  let ms : List Merkmal := [.reg, .atom, .zeiger, .ruf, .float]
  ms.flatMap fun a => (ms.dropWhile (· != a)).map fun b => if a == b then [a] else [a, b]

/-- **A one-class member**: a function with one parameter of the class `τ`, and a callee that takes one value of that
    class and answers one: a call or a result of the class needs one argument, not a whole type group. -/
def einKlasse (τ : Ty) : Spez where
  tabs := [{ count := 1, felder := [{ typ := τ }] }]
  sigs := [{ params := [τ], schreibt := [0] }, { params := [τ], erg := some τ }]
  fns := [0, 1]

/-- **The mark members**: a function that holds a mark of two stages at its start and leaves with the next stage
    (`advances`), and one that gives it back (`retires`, under a named assumption). -/
def marke (weiter : Bool) : Spez where
  marken := [2]
  annahmen := 1
  sigs := [{ konsumiert := [(0, 0)], produziert := if weiter then [(0, 1)] else [] }]

/-- **The fine members**: for every group the three declarations, then for every group the one with a pointer; then
    the divisor group; then the combination members; then a one-class member per class and the two mark members
    (each block appended, so the members before keep their numbers). -/
def feinMitglieder : List Spez :=
  (((gruppen.flatMap fun g => [ausdruck g, register g, atomar g]) ++ gruppen.map zeiger) ++
    [ausdruck teilerGruppe, register teilerGruppe, zeiger teilerGruppe] ++ kombiListen.map kombi ++
    vertreter.map einKlasse ++ [marke true, marke false]).map Spez.einzeln

theorem kombiListen_laenge : kombiListen.length = 15 := by decide

end Gabbro.Grammatik.Gen.Fein
