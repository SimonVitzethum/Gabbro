module

public import Grammatik.Logik.Invarianten.Frag.Symbolic.Environment
public import Grammatik.Logik.Invarianten.Frag.Witness

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Frag.Symbolic.Witness

open Elim Elim.Korrekt

abbrev declaration := Frag.Witness.declaration
abbrev world := Frag.Witness.initial
abbrev u32 : Ty := .int 0 (2 ^ 32 - 1)

def seven : Wert declaration u32 := ⟨7, by decide, by decide⟩
def symbols : SymEnv declaration Nat [u32] := .cons (.integer (.var 0)) .nil
def actual : Env declaration [u32] := .cons seven .nil
def valuation : Assignment Nat := fun _ => 7

theorem realizes_zeuge : symbols.Realizes valuation world actual := ⟨rfl, trivial⟩

theorem embed_injective_zeuge :
    embed (D := declaration) (.inr (3 : Nat)) ≠ embed (.inr 4) := by
  intro same
  have impossible := embed_injective same
  cases impossible

theorem embed_fresh_zeuge :
    embed (D := declaration) (.inl (.glob false) : Key declaration Nat) ≠ .inr none :=
  embed_fresh _

theorem values_extend_zeuge :
    values (extend valuation 9) world ∘ embed = values valuation world :=
  values_extend valuation world 9

def term : LTerm Nat := .add (.var 0) (.konst 2)
def formula : QF Nat := .atom .lt (.sub (.var 0) (.konst 10))
def quantified : LProp Nat := .all 1 (.imp (.le (.konst 0) (.var 1))
  (.le (.var 0) (.add (.var 0) (.var 1))))

theorem renameTerm_denote_zeuge :
    (renameTerm some term).denote (extend valuation 9) = term.denote valuation :=
  renameTerm_denote some term (extend valuation 9)

theorem renameQF_denote_zeuge :
    (renameQF some formula).denote (extend valuation 9) ↔ formula.denote valuation :=
  renameQF_denote some formula (extend valuation 9)

theorem bind_rename_zeuge :
    (Assignment.bind (extend valuation 9) (some 0) 11) ∘ some =
      Assignment.bind valuation 0 11 :=
  bind_rename some (fun _ _ same => Option.some.inj same) (extend valuation 9) 0 11

theorem renameProp_denote_zeuge :
    (renameProp some quantified).denote (extend valuation 9) ↔ quantified.denote valuation :=
  renameProp_denote some (fun _ _ same => Option.some.inj same) quantified (extend valuation 9)

theorem rename_subst_denote_zeuge :
    (renameQF some (formula.subst 0 term)).denote (extend valuation 9) ↔
      (renameQF some formula).denote
        (Assignment.bind (extend valuation 9) (some 0) 9) :=
  rename_subst_denote some (fun _ _ same => Option.some.inj same) 0 term formula (extend valuation 9)

theorem realizes_ofEnv_zeuge :
    (SymEnv.ofEnv actual).Realizes valuation world actual :=
  SymEnv.realizes_ofEnv actual valuation world

theorem realizes_get_zeuge :
    (symbols.get .here).Realizes valuation world seven :=
  symbols.realizes_get actual valuation world .here realizes_zeuge

theorem realizes_set_zeuge :
    (symbols.set .here (.known seven)).Realizes valuation world (actual.set .here seven) :=
  symbols.realizes_set actual valuation world .here (.known seven) seven realizes_zeuge rfl

theorem realizes_value_lift_zeuge :
    (SymValue.integer (.var 0) : SymValue declaration Nat u32).lift.Realizes
      (extend valuation 9) world seven :=
  (SymValue.realizes_lift _ valuation world 9 seven).mpr rfl

theorem realizes_lift_zeuge : symbols.lift.Realizes (extend valuation 9) world actual :=
  (symbols.realizes_lift actual valuation world 9).mpr realizes_zeuge

theorem extend_integer_zeuge :
    (SymEnv.cons (.integer (.var none)) symbols.lift).Realizes
      (extend valuation seven.n) world (.cons seven actual) :=
  symbols.extend_integer actual valuation world seven realizes_zeuge

end Gabbro.Grammatik.Invarianten.Frag.Symbolic.Witness
