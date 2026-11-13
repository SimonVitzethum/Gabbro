module

public import Grammatik.Kern.Syntax.Typen.Produkt

@[expose] public section

/-
  File:       Grammatik/Parser/Elab/Uebersetze/Records/Schema.lean
  Subject:    C01, nominal record schemas of the source export: the declared record with its identity
              and ordered field types, plus the resolved type scope (aliases and record schemas).
-/

namespace Gabbro.Grammatik.Parser.Uebersetze

/-- A nominal record schema. Only runtime fields are admitted until ownership erasure is connected. -/
structure URecord where
  name : String
  identity : Nat
  fields : List (String × Ty)
  /-- Source modifiers are retained even when their transport is refused. -/
  modifiers : List String := []
  /-- Declared integer storage widths, independent of the resolved field intervals. -/
  breiten : List (String × Nat) := []
  deriving DecidableEq, Repr

def URecord.ty (record : URecord) : Ty := Ty.prodOf record.identity (record.fields.map (·.2))

/-- The resolved type scope of a unit: value aliases and nominal record schemas. -/
structure UTypeScope where
  types : List (String × Ty)
  records : List URecord := []
  deriving DecidableEq, Repr

end Gabbro.Grammatik.Parser.Uebersetze
