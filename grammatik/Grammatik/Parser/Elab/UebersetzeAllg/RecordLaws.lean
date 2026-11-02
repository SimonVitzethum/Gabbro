module

public import Grammatik.Parser.Elab.UebersetzeAllg.Teil5
public import Grammatik.Kern.Syntax.Syntax.ProduktZucker

@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg
open Uebersetze

/-- The real expression lowerer emits the nominal constructor over the complete field list. -/
theorem record_lower (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn)
    (er : Option Ty) (identity : Nat) (reordered : Bool) (sides : List (Ty × USide))
    (args : Args (declOf u) Γ Λ (sides.map (·.1)))
    (gate : u.exportGate = .ok ())
    (lowered : lowProductArgs u Γ Λ fn er (lowWertAtE u Γ Λ fn er)
      (sides.map (·.1)) (sides.map (·.2)) = .ok args)
    (schema : { s : URecord // s.ty = .prod identity (sides.map (·.1)) })
    (hschema : uRecordOf u.records (.prod identity (sides.map (·.1))) = .ok schema) :
    lowWertE u Γ Λ fn er (.product identity reordered sides) =
      .ok ⟨.prod identity (sides.map (·.1)), Expr.prod identity args⟩ := by
  simp only [lowWertE, gate, hschema, lowered]

/-- Product projection and replacement use the canonical semantics, with the whole base footprint. -/
theorem record_replace_meaning {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {identity : Nat}
    {fs : List Ty} {field : Ty} (entry state : World D) (env : Env D Γ)
    (value : Expr D Γ Λ (.prod identity fs)) (position : FieldAt fs field)
    (replacement : Expr D Γ Λ field) :
    eval entry (Expr.prodSet value position replacement) state env =
      prodSetW position (eval entry value state env) (eval entry replacement state env) ∧
    (Expr.prodSet value position replacement).orte = value.orte ++ replacement.orte := ⟨rfl, rfl⟩

end Gabbro.Grammatik.Parser.UebersetzeAllg
