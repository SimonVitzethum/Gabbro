module

public import Grammatik.Nebenlaeufigkeit.Allgemein.Verklemmung
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtSperre
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtGanz
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtAx
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtRahmen
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVoll
public import Grammatik.Logik.Fortschritt.KostenG
public import Grammatik.Logik.Vertraege.AxiomVertrag
public import Grammatik.Zielsatz.Kern.Akzeptiert
public import Grammatik.Logik.Vertraege.Pruefer.Goal
public import Grammatik.Nebenlaeufigkeit.Allgemein.MehrfadenZeuge.Teil2

@[expose] public section

namespace Gabbro.Grammatik.CheckedMehrfaden

open Zielsatz

instance : DecidableEq mD.Ax := inferInstanceAs (DecidableEq Empty)

/-- A nontrivial local invariant replaces the unsupported cross-slot relation.
    Both active writers, all calls and both lock sections keep their bodies. -/
def localBound : Expr mD [] [] .bool :=
  .forallSlots MTab.privA
    (.le (.slot MTab.privA () (.var .here) (mDarfA [])) (.lit 7)) (mDarfA [])

def program : Programm mD :=
  { mP with
    invariante := fun _ => localBound
    requires := fun f => match f with
      | .pruefeA => mA7
      | _ => .tru
    ensures := fun f => match f with
      | .hauptA => mA7
      | _ => .tru }

def family : SperrInv mD :=
  { orte := mSI.orte, inv := fun _ _ => true }

def sources : Invarianten.Pruefer.LockSources family := fun _ => some
  { resources := [], expression := .tru, correct := fun _ => rfl }

def carriers : List (mD.Tab ⊕ mD.Glob) := [.inl MTab.konto, .inl MTab.privA, .inl MTab.privB]

/-- Honest source metadata for the original, unsupported cross-slot lock relation. -/
def originalSources : Invarianten.Pruefer.LockSources mSI := fun _ => some
  { resources := mL, expression := mGleich, correct := fun _ => rfl }

theorem accepted_zeuge :
    Akzeptiert program family mFs [()] carriers [mHauptA, mHauptB]
      (sources := sources) = true := by
  decide +kernel

theorem contracts_checked : Vertraege.Pruefer.KontrakteGeprueftB program family mFs sources = true :=
  (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp accepted_zeuge).2).2

/-- The actual checked certificate supplies the semantic body duties. -/
theorem duties (f : mD.Fn) : Vertraege.Pruefer.ContractDuties program family f := by
  have gate := (Bool.and_eq_true_iff.mp accepted_zeuge).2
  have contracts := (Bool.and_eq_true_iff.mp gate).2
  exact Vertraege.Pruefer.KontrakteGeprueftB_sound mFs_voll contracts f

theorem bodies (passes : Nat) (f : mD.Fn) : KoerperGutS program passes (axWahr mD) family f :=
  koerperGutS_of_A ((duties f passes (axWahr mD) (fun _ => False) (fun _ h => False.elim h)).1)

theorem invariants (passes : Nat) (f : mD.Fn) : InvGutS program passes (axWahr mD) family f :=
  invGutS_of_A ((duties f passes (axWahr mD) (fun _ => False) (fun _ h => False.elim h)).2.1)

theorem reason_invariants (passes : Nat) (f : mD.Fn) : InvGutGrund program passes (axWahr mD) family f :=
  invGutGrund_of_A ((duties f passes (axWahr mD) (fun _ => False) (fun _ h => False.elim h)).2.2)

theorem family_local : SperrInvLokal family := fun _ _ _ _ => rfl

end Gabbro.Grammatik.CheckedMehrfaden
