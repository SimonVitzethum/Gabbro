/-
  The binding of a lock's declared hold bound (`lock L … held <= n ops`).

  The export gate admits a literal hold bound. The duty does not disappear: `holds` is the rule K002
  over the lowered program -- every `locks L { … }` section of a lock with a declared bound costs at
  most that bound in own steps of machine G (`kostenBlock`, each call counted at the callee's declared
  cost), and calls only functions that declare a cost. The walker `haltS` … `haltE` is the model's
  (Logik/Fortschritt/Halten/Pruefung.lean); with every lock bounded, the model's Bool `haltPasst` gives
  the hold time of the waiting statement as a theorem (`haltezeit_aus`, Halten/Haltezeit.lean).
-/
module
public import Grammatik.Parser.Elab.Export.CostBinding
public import Grammatik.Logik.Fortschritt.Halten.Pruefung
@[expose] public section

namespace Gabbro.Grammatik.Parser.HeldBinding
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg

/-- The declared literal hold bounds of the source locks, by name. -/
def declared (items : List SItemTief) : Tafel (String × Nat) (·.1) :=
  Tafel.von _ (items.filterMap fun
    | .lockT name _ _ (some (.lit n)) _ _ _ => some (name, n)
    | _ => none)

variable (H C : Tafel (String × Nat) (·.1)) (u : UProg)

/-- The declared hold bound of a lock of the unit. -/
def boundOf (L : Fin u.locks.length) : Option Nat := (H.finde (lockAt u L).name).map (·.2)

/-- **The hold bounds hold** (K002): every lock with a declared bound is a lock of the unit, and
    every section of such a lock, in every function, fits under the bound. -/
def holds (P : Programm (declOf u)) (passes : Nat) : Bool :=
  H.liste.all (fun p => u.locks.any (fun l => strEq l.name p.1)) &&
    (List.finRange u.fns.length).all fun g =>
      haltE (D := declOf u) (boundOf H u) (kostenEpilog P g) (CostBinding.decl C u)
        (fun x => (CostBinding.costOf C u x).isSome)
        passes (P.rumpf g)

/-- The first function with a section over its lock's bound, for the refusal. -/
def failing (P : Programm (declOf u)) (passes : Nat) : Option String :=
  match H.liste.find? (fun p => !u.locks.any (fun l => strEq l.name p.1)) with
  | some p => some p.1
  | none => ((List.finRange u.fns.length).find? fun g =>
      !haltE (D := declOf u) (boundOf H u) (kostenEpilog P g) (CostBinding.decl C u)
        (fun x => (CostBinding.costOf C u x).isSome) passes (P.rumpf g)).map fun g => (fnAt u g).name

end Gabbro.Grammatik.Parser.HeldBinding
