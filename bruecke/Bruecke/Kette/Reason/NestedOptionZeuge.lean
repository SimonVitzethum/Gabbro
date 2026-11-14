module
public import Bruecke.Kette.Formen.OptionZeuge
public import Bruecke.Anweisung.Match.NestedKopf
import all Init.Data.String.Length
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.Repr
import all Init.Data.String.Decode
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
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
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil12
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
import all Grammatik.Parser.Elab.Generic.StaticConformance
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil5
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest1
import all Grammatik.Parser.Elab.UebersetzeAllg3.Body
@[expose] public section

namespace Gabbro.Bruecke.NestedOptionZeuge

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
attribute [local cbv_eval] Nat.log2_def lowEns.eq_def lowCmp.eq_def lowWertE.eq_def

/-- Both option arms end explicitly inside an outer branch. The present arm binds
    an actual index into the two-element table, and the absent arm returns zero. -/
def routine : UFn :=
  { OptionZeuge.test with
    body := [.ifBeg .tru] ++ OptionZeuge.test.body ++
      [.ifElse, .ret (.val (.lit 0)), .blkEnd] }

def unit : UProg := { OptionZeuge.unit with fns := [routine] }

def body : List Gabbro.Body.Stmt :=
  [.ite (.lit (.bool true))
    [.onOption (.name "o") "k" [.ret (some (.lit (.int 1)))] [.ret (some (.lit (.int 0)))]]
    [.ret (some (.lit (.int 0)))], .ret (some (.lit (.int 0)))]

theorem reader_zeuge : zuBodyZ unit routine = some body := by cbv

theorem lowering_zeuge : (lowerAllg unit).toOption.isSome = true := by
  apply Gabbro.Grammatik.Uebersetzung.LibraryFixtureProofs.lowering_ok
  · rfl
  · cbv
  · rintro ⟨index, bound⟩
    have small : index < 1 := bound
    have zero : index = 0 := by omega
    subst index
    constructor <;> cbv

/-- The same nested source body is accepted by both readers; two nonempty arms
    and the bounded table index are present simultaneously. -/
theorem nested_option_zeuge :
    zuBodyZ unit routine = some body ∧ (lowerAllg unit).toOption.isSome = true :=
  ⟨reader_zeuge, lowering_zeuge⟩

end Gabbro.Bruecke.NestedOptionZeuge
