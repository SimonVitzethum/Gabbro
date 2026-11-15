module

public import Grammatik.Logik.Vertraege.Pruefer.Witness.Selection
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtSperreZeuge.T1.Teil1Basis

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz.PoolCertificate

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.VC
open Vertraege.Pruefer Vertraege.Pruefer.SelectionWitness

abbrev scalar := Ty.int 0 100

def domain : LocalDomain zD scalar :=
  (localDomain (D := zD) 128 scalar).toOption.get (by rfl)

theorem domain_result : localDomain (D := zD) 128 scalar = .ok domain := rfl

def post (value : Zahl 0 100) :=
  (postFormula zPB zLies .nil value).toOption.get (by rfl)

theorem post_result (value : Zahl 0 100) :
    postFormula zPB zLies .nil value = .ok (post value) := rfl

theorem post_meaning (value : Zahl 0 100) (values : Assignment (Observation zD)) :
    (post value).val.denote values ↔ value.n = values (.slot () () 0) := by
  exact (lower_denote _ values).trans Iff.rfl

def slotRelation (value : Zahl 0 100) :
    { formula : LProp (Observation zD) // ∀ world,
      formula.denote (assignment world) ↔
        eval world (.slot () () zIdx zDarf) world (.nil : Env zD []) = value } :=
  ⟨.eq (.var (.slot () () 0)) (.konst value.n), fun _ =>
    ⟨fun same => zahl_ext same, fun same => congrArg Zahl.n same⟩⟩

theorem slotRelation_result (value : Zahl 0 100) :
    localEquality (D := zD) (.slot () () zIdx zDarf) .nil value = .ok (slotRelation value) := by
  simp only [localEquality, integerEquality]
  rfl

theorem slotRelation_meaning (value : Zahl 0 100) (values : Assignment (Observation zD)) :
    (slotRelation value).val.denote values ↔ values (.slot () () 0) = value.n := Iff.rfl

abbrev variableExpr : Expr zD [scalar] zL scalar := .var .here

def varRelation (bound value : Zahl 0 100) :
    { formula : LProp (Observation zD) // ∀ world,
      formula.denote (assignment world) ↔
        eval world variableExpr world (.cons bound .nil) = value } :=
  ⟨.eq (.konst bound.n) (.konst value.n), fun _ =>
    ⟨fun same => zahl_ext same, fun same => congrArg Zahl.n same⟩⟩

theorem varRelation_result (bound value : Zahl 0 100) :
    localEquality variableExpr (.cons bound .nil) value =
      .ok (varRelation bound value) := by
  simp only [localEquality, integerEquality, variableExpr]
  rfl

theorem varRelation_meaning (bound value : Zahl 0 100) (values : Assignment (Observation zD)) :
    (varRelation bound value).val.denote values ↔ bound.n = value.n := Iff.rfl

end Gabbro.Grammatik.Zielsatz.PoolCertificate
