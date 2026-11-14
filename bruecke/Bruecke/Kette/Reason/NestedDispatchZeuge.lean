module
public import Bruecke.Kette.Formen.ReasonZeuge
public import Bruecke.Kette.Formen.TagZeuge
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

namespace Gabbro.Bruecke.NestedDispatchZeuge

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
attribute [local cbv_eval] Nat.log2_def lowEns.eq_def lowCmp.eq_def lowWertE.eq_def

def reasonFn : UFn :=
  { ReasonZeuge.test with body := [.ifBeg .tru] ++ ReasonZeuge.test.body ++
      [.ifElse, .ret (.val (.lit 0)), .blkEnd] }

def reasonUnit : UProg := { ReasonZeuge.unit with fns := [reasonFn] }

def tagFn : UFn :=
  { TagZeuge.test with body := [.ifBeg .tru] ++ TagZeuge.test.body ++
      [.ifElse, .ret (.val (.lit 0)), .blkEnd] }

def tagUnit : UProg := { TagZeuge.unit with fns := [tagFn] }

def reasonBody : List Gabbro.Body.Stmt :=
  [.ite (.lit (.bool true)) (ReasonZeuge.body.take 1) [.ret (some (.lit (.int 0)))],
    .ret (some (.lit (.int 0)))]

def tagBody : List Gabbro.Body.Stmt :=
  [.ite (.lit (.bool true)) (TagZeuge.body.take 1) [.ret (some (.lit (.int 0)))],
    .ret (some (.lit (.int 0)))]

/-- Both alternatives of the two-case reason parameter survive inside an outer branch. -/
theorem nested_reason_reader_zeuge : zuBodyZ reasonUnit reasonFn = some reasonBody := by cbv

/-- Both alternatives of the two-case tag parameter survive inside an outer branch. -/
theorem nested_tag_reader_zeuge : zuBodyZ tagUnit tagFn = some tagBody := by cbv

theorem nested_reason_lowering_zeuge : (lowerAllg reasonUnit).toOption.isSome = true := by
  apply Gabbro.Grammatik.Uebersetzung.LibraryFixtureProofs.lowering_ok
  · rfl
  · cbv
  · rintro ⟨index, bound⟩
    have small : index < 1 := bound
    have zero : index = 0 := by omega
    subst index
    constructor <;> cbv

theorem nested_tag_lowering_zeuge : (lowerAllg tagUnit).toOption.isSome = true := by
  apply Gabbro.Grammatik.Uebersetzung.LibraryFixtureProofs.lowering_ok
  · rfl
  · cbv
  · rintro ⟨index, bound⟩
    have small : index < 1 := bound
    have zero : index = 0 := by omega
    subst index
    constructor <;> cbv

theorem nested_reason_zeuge : zuBodyZ reasonUnit reasonFn = some reasonBody ∧
    (lowerAllg reasonUnit).toOption.isSome = true :=
  ⟨nested_reason_reader_zeuge, nested_reason_lowering_zeuge⟩

theorem nested_tag_zeuge : zuBodyZ tagUnit tagFn = some tagBody ∧
    (lowerAllg tagUnit).toOption.isSome = true :=
  ⟨nested_tag_reader_zeuge, nested_tag_lowering_zeuge⟩

end Gabbro.Bruecke.NestedDispatchZeuge
