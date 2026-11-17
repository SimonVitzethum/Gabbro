module

public import Grammatik.Logik.Invarianten.Frag.Symbolic.Scope

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Frag.Symbolic

open Elim Elim.Korrekt

/-- Field positions embed into the flattened observation context. -/
def fieldVariable {tail : Ctx} : FieldAt fields kind → Var (fields ++ tail) kind
  | .head => .here
  | .tail field => .there (fieldVariable field)

/-- Flatten only the actual typed product; no value is sampled or decoded. -/
def flattenProduct (fields : List Ty) (value : ProdVal D.Fn D.passt fields)
    (tail : Env D Γ) : Env D (fields ++ Γ) :=
  match fields with
  | [] => tail
  | _ :: fields => .cons (ProdVal.hd value) (flattenProduct fields (ProdVal.tl value) tail)

theorem flattenProduct_get (field : FieldAt fields kind) (value : ProdVal D.Fn D.passt fields)
    (tail : Env D Γ) :
    (flattenProduct fields value tail).get (fieldVariable field) = prodGetW field value := by
  induction field with
  | head => rfl
  | tail field ih => exact ih (ProdVal.tl value)

def SymEnv.dropPrefix (fields : List Ty) (symbols : SymEnv D α (fields ++ Γ)) : SymEnv D α Γ :=
  match fields, symbols with
  | [], symbols => symbols
  | _ :: fields, .cons _ rest => rest.dropPrefix fields

theorem SymEnv.bounded_dropPrefix (fields : List Ty) (symbols : SymEnv D Nat (fields ++ Γ))
    (bounded : symbols.Bounded next) : (symbols.dropPrefix fields).Bounded next := by
  induction fields with
  | nil => exact bounded
  | cons kind fields ih => cases symbols; exact ih _ bounded.2

theorem SymEnv.realizes_dropPrefix (fields : List Ty) (symbols : SymEnv D α (fields ++ Γ))
    (value : ProdVal D.Fn D.passt fields) (tail : Env D Γ) (valuation : Assignment α) (world : World D)
    (realized : symbols.Realizes valuation world (flattenProduct fields value tail)) :
    (symbols.dropPrefix fields).Realizes valuation world tail := by
  induction fields with
  | nil => exact realized
  | cons kind fields ih => cases symbols; exact ih _ (ProdVal.tl value) realized.2

/-- Reassemble the nominal product while preserving each field's own keys. -/
def SymEnv.packProduct (name : Nat) (fields : List Ty) (symbols : SymEnv D α (fields ++ Γ)) :
    SymEnv D α (.prod name fields :: Γ) :=
  .cons (.product (fun field => symbols.get (fieldVariable field))) (symbols.dropPrefix fields)

theorem SymEnv.bounded_packProduct (name : Nat) (fields : List Ty)
    (symbols : SymEnv D Nat (fields ++ Γ)) (bounded : symbols.Bounded next) :
    (symbols.packProduct name fields).Bounded next :=
  ⟨fun field => symbols.bounded_get next bounded (fieldVariable field),
    symbols.bounded_dropPrefix fields bounded⟩

theorem SymEnv.realizes_packProduct (name : Nat) (fields : List Ty)
    (symbols : SymEnv D α (fields ++ Γ)) (value : Wert D (.prod name fields))
    (tail : Env D Γ) (valuation : Assignment α) (world : World D)
    (realized : symbols.Realizes valuation world (flattenProduct fields value tail)) :
    (symbols.packProduct name fields).Realizes valuation world (.cons value tail) := by
  refine ⟨?_, symbols.realizes_dropPrefix fields value tail valuation world realized⟩
  intro kind field
  have selected := symbols.realizes_get (flattenProduct fields value tail) valuation world
    (fieldVariable field) realized
  rw [flattenProduct_get field value tail] at selected
  exact selected

theorem context_size_append (left right : Ctx) : sizeOf (left ++ right) ≤ sizeOf left + sizeOf right := by
  induction left with
  | nil => simp only [List.nil_append, List.nil.sizeOf_spec]; omega
  | cons kind left ih => simp only [List.cons_append, List.cons.sizeOf_spec]; omega

end Gabbro.Grammatik.Invarianten.Frag.Symbolic
