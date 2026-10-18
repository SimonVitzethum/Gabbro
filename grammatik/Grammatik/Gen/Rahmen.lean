/-
  File:      Grammatik/Gen/Rahmen.lean
  Subject:   Generator, the fixed FRAMES the generated bodies are put into, and the seeds read off them. A
             frame is the declaration part of a unit (statics, tables, locks, a helper function) and the head
             of `main`; the generated part is the body of `main` and nothing else. The frames are plain Gabbro
             text (data, not a grammar). The SEEDS (declared places, integer and truth-value expressions over
             them, lock names) are computed from the frame's elaborated declaration (`UProg`: tables, fields,
             statics, locks), never written by hand.

  `ctorNames% T` is the generic census: the constructor names of an inductive type, read from the
  environment at elaboration time, so a new constructor appears in the report without any edit.
-/
import Lean
import Grammatik.Gen.Lauf
import Grammatik.Parser.Print.Item

namespace Gabbro.Grammatik.Gen

open Lean Elab Term Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

/-- The constructor names of an inductive type, from the environment. -/
elab "ctorNames% " id:ident : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo id
  let info ← getConstInfoInduct n
  return toExpr (info.ctors.map (·.toString))

/-- A frame: a name, the declaration part up to `effects {`, the read and write effects of every
    declared carrier (the checker wants reads as complete as writes; over-declaring is accepted), and the
    locks of the frame. A lock effect is exact (`H011`: declared and never taken is refused), so it is added
    by `Rahmen.text` only for a lock the body takes. -/
structure Rahmen where
  name : String
  kopf : String
  effs : String
  sperren : List String := []
  deriving Inhabited

/-- The source text of a unit of this frame around a printed body (`{ ... }`, a block). -/
def Rahmen.text (r : Rahmen) (rumpf : String) : String :=
  let sp := r.sperren.filter fun l => (rumpf.splitOn ("locks " ++ l ++ " ")).length > 1
  r.kopf ++ " impl fn main() -> u64 effects { " ++ r.effs ++ (sp.map (", locks " ++ ·)).foldl (· ++ ·) "" ++
    " } costs <= 100000000 ops " ++ rumpf ++ " }"

/-- Statics and one table, no lock; a helper. -/
def rahmenA : Rahmen where
  name := "A"
  kopf := "module gen { pub static mut A : u8 = 0; pub static mut B : u8 = 3; pub static mut F : bool = false; pub static mut C : u16 = 0;" ++
    " table T count 4 { slot { v : u8, w : u8, b : bool, x : u16, } }" ++
    " impl fn h(a : u8, b : u8) -> u8 costs <= 10 ops { return b; }"
  effs := "reads A, writes A, reads B, writes B, reads F, writes F, reads C, writes C, reads T.slots, writes T.slots, reads T"

/-- A lock over one table, a second table, statics under no lock. -/
def rahmenB : Rahmen where
  name := "B"
  kopf := "module gen { pub static mut A : u8 = 1; pub static mut B : u8 = 0; pub static mut D : u32 = 0;" ++
    " table T count 3 { slot { v : u8, w : u8, } }" ++
    " table U count 2 { slot { n : u8, b : bool, } }" ++
    " lock L protects { v, w } rank 0 held <= 100 ops;"
  effs := "reads A, writes A, reads B, writes B, reads D, writes D, reads T.slots, writes T.slots, reads U.slots, writes U.slots, reads T, reads U"
  sperren := ["L"]

/-- Narrow ranges, so that sums and products of two places fit the operand width (checker rule `M104`) and
    arithmetic reaches the compiler. -/
def rahmenC : Rahmen where
  name := "C"
  kopf := "module gen { pub static mut A : u8 in 0 .. 40 = 0; pub static mut B : u8 in 0 .. 40 = 3;" ++
    " pub static mut S : i16 = 0;" ++
    " table T count 3 { slot { v : u8 in 0 .. 40, w : i16, b : bool, } }"
  effs := "reads A, writes A, reads B, writes B, reads S, writes S, reads T.slots, writes T.slots, reads T"

def rahmen : List Rahmen := [rahmenA, rahmenB, rahmenC]

/-- The seeds of a frame as expression texts, by role. -/
structure Saat where
  ints : List String := []
  bools : List String := []
  plaetze : List String := []
  sperren : List String := []
  tabellen : List String := []
  /-- the numeric places read together: the digest the program returns (`a ^ b ^ ...`). -/
  digest : String := "0"

/-- Places `T.slots[k].f` of the first slots of a table, split into numeric and truth-valued. -/
def tabPlaetze (t : UTab) : List String × List String :=
  let ks := List.range (min t.count.toNat 3)
  let num := t.cols.filter (fun c => !t.bools.contains c.1)
  ( num.flatMap (fun c => ks.map fun k => s!"{t.name}.slots[{k}].{c.1}"),
    t.bools.flatMap (fun f => ks.map fun k => s!"{t.name}.slots[{k}].{f}") )

/-- The seeds, read off the elaborated declaration of the frame. -/
def saatVon (u : UProg) : Saat :=
  let gi := u.globs.filter (fun g => g.ty != .bool)
  let gb := u.globs.filter (fun g => g.ty == .bool)
  let tp := u.tabs.map tabPlaetze
  let pn := gi.map (·.name) ++ tp.flatMap (·.1)
  let pb := gb.map (·.name) ++ tp.flatMap (·.2)
  let sum := (pn.take 3).flatMap fun p => (pn.take 3).map fun q => s!"{p} + {q}"
  let vgl := (pn.take 3).flatMap fun p => ["0", "7", "200"].map fun c => s!"{p} < {c}"
  { ints := pn ++ ["0", "1", "2", "5", "255"] ++ sum
    bools := pb ++ ["true", "false"] ++ vgl
    plaetze := (gi ++ gb).filter (·.var) |>.map (·.name) |> (· ++ tp.flatMap (fun p => p.1 ++ p.2))
    sperren := u.locks.map (·.name)
    tabellen := u.tabs.map (·.name)
    digest := " ^ ".intercalate (pn.take 24) }

/-- The seeds of each frame. -/
def rahmenSaaten : List Saat :=
  rahmen.map fun r =>
    match uebersetzeToks (rohToks (r.text "{ return 0; }")) with
    | .ok ⟨u, _, _⟩ => saatVon u
    | .error _ => {}

end Gabbro.Grammatik.Gen
