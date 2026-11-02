module

public import Grammatik.Gen.Zeugen.Schluss
public import Grammatik.Parser.Round.RundlaufProgramm
public import Grammatik.Parser.Cover.Mitglieder
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
public import Grammatik.Gen.Text.Delab.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Gen.Text
open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Parser
variable (z : Spez)
variable (V : Vertrag z.deklaration)

/-- The entry of a function the hardware enters. -/
def eintritt (i : Nat) : SItemTief :=
  .entryT { name := "ent" ++ toString i, vektor := some (.lit (32 + i)), regIn := [], regOut := [],
            erhaelt := [], kills := [], perCpu := true, ist := none, dispatch := ["m", nFn i],
            «via» := some "idt", arch := "x86_64", stapel := "stk" ++ toString i, nest := some "never" }

/-- The value a start passes for a parameter: the least value of its type (a start's arguments do not enter
    the checker's verdict; the language needs one value per parameter). -/
def startWert : Ty → Except String SExpr
  | .int lo _ => .ok (zahlE lo)
  | .bool => .ok .fls
  | .opt _ => .ok (.call "None" [])
  | .ptr ⟨_, _, .table t⟩ => .ok (.fnref (nTab t))
  | .fnptr _ => .error "start argument of a function-pointer type"
  | _ => .error "start argument of a type without a value form"

/-- **The delaborator**: a program of the generator as the items of one module. -/
def delab (P : Programm z.deklaration) (ws : List z.deklaration.Fn) : Except String (List SItemTief) := do
  if !z.marken.isEmpty then throw "marks without a spelling"
  if !z.axs.isEmpty then throw "foreign bodies outside the test sets"
  let tabs ← (List.finRange z.tabs.length).mapM (delabTab z)
  let globs ← (List.finRange z.globs.length).mapM (delabGlob z)
  let locks ← (List.finRange z.locks.length).mapM (delabLock z)
  let dev ← delabDev z
  let invs ← (List.finRange z.invs.length).mapM (delabInv z P)
  let fns ← (List.finRange z.fns.length).mapM (delabFn z P (!z.regs.isEmpty))
  let starts ← if ws.isEmpty then pure [] else do
    let ms ← ws.mapM fun f => do
      let as ← (z.deklaration.signatur f).params.mapM startWert
      pure (["m", nFn (show Fin z.fns.length from f).val], as)
    pure [SItemTief.concT ms]
  let eintritte := ((List.finRange z.fns.length).filter fun f => P.unterbricht f).map fun f => eintritt f.val
  pure [.modT "m" (tabs ++ globs ++ locks ++ dev ++ (gruende z).map grundItem ++ invs ++ fns ++ starts ++ eintritte)]

end Gabbro.Grammatik.Gen.Text
