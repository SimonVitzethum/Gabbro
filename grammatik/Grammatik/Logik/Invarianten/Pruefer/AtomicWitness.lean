module

public import Grammatik.Logik.Invarianten.Pruefer.Checker
public import Grammatik.Nichtinterferenz.Zeuge.Teil1Basis
import all Batteries.Data.Except

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Pruefer.AtomicWitness

open Zielsatz NIZeuge

/-- The original flag fixture has real atomic readers and a writer. Its true
    contracts are checked against arbitrary typed atomic answers. -/
theorem accepted_zeuge : invariantVCB nP (SperrInv.leer nD) nFs = true := by decide +kernel

theorem checker_accepted_zeuge :
    AkzeptiertX nP (SperrInv.leer nD) nFs [] nCs [.hauptA, .hauptB, .kern] = true := by
  unfold AkzeptiertX
  rw [accepted_zeuge]
  simp only [Bool.and_true, Bool.and_eq_true]
  decide +kernel

theorem actual_atomic_read_zeuge :
    atomicFreeB nP .hauptA = false ∧ nD.atomar .konfig = true := by decide +kernel

theorem duties_zeuge (passes : Nat) (Q : AxEns nD)
    (shared : nD.Tab ⊕ nD.Glob → Prop)
    (subset : ∀ carrier, shared carrier → AtomarAusgenommen carrier) (f : nD.Fn) :
    KoerperGutSA nP passes Q (SperrInv.leer nD) shared f ∧
      InvGutSA nP passes Q (SperrInv.leer nD) shared f ∧
        InvGutGrundA nP passes Q (SperrInv.leer nD) shared f :=
  invariantVCB_sound nFs_voll accepted_zeuge f passes Q shared subset

/-- A false declared contract still refuses; the atomic certificate never
    replaces a nontrivial ensures clause with truth. -/
def falseContract : Programm nD := { nP with ensures := fun _ => .not .tru }

theorem false_contract_refused_zeuge :
    invariantVCB falseContract (SperrInv.leer nD) nFs = false := by decide +kernel

end Gabbro.Grammatik.Invarianten.Pruefer.AtomicWitness
