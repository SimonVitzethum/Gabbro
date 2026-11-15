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

def slotRelation (value : Zahl 0 100) :=
  (localEquality (D := zD) (.slot () () zIdx zDarf) .nil value).toOption.get (by rfl)

theorem slotRelation_result (value : Zahl 0 100) :
    localEquality (D := zD) (.slot () () zIdx zDarf) .nil value = .ok (slotRelation value) := rfl

theorem slotRelation_meaning (value : Zahl 0 100) (values : Assignment (Observation zD)) :
    (slotRelation value).val.denote values ↔ values (.slot () () 0) = value.n := Iff.rfl

def varRelation (bound value : Zahl 0 100) :=
  (localEquality (D := zD) (Λ := zL) (.var .here) (.cons bound .nil) value).toOption.get (by rfl)

theorem varRelation_result (bound value : Zahl 0 100) :
    localEquality (D := zD) (Λ := zL) (.var .here) (.cons bound .nil) value =
      .ok (varRelation bound value) := rfl

theorem varRelation_meaning (bound value : Zahl 0 100) (values : Assignment (Observation zD)) :
    (varRelation bound value).val.denote values ↔ bound.n = value.n := Iff.rfl

end Gabbro.Grammatik.Zielsatz.PoolCertificate
