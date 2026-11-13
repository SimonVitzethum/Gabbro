/-
  File:      Grammatik/Niedrig/Arch/ZustandZeuge.lean
  Subject:   WITNESS FOR THE NEUTRAL ARCHITECTURAL STATE (L4a): a fixture run
    of four steps and one refused step from user privilege.

  The run enters the kernel, sets the mask, sets the root and leaves, each
  step closed by its constructor; the end state is read back field by field.
  The refusal instantiates `keinMaskeNutzer`: no `setMask` step leaves a user
  state.
-/
module

public import Grammatik.Niedrig.Arch.Zustand

@[expose] public section


namespace Gabbro.Grammatik.Niedrig.Arch

/-- The fixture start: a user state on core 2. -/
def a0 : ArchState :=
  { priv := Priv.nutzer
    wurzel := 0
    maske := false
    vektor := 0
    kern := 2 }

/-- After entering the kernel. -/
def a1 : ArchState :=
  { priv := Priv.kern
    wurzel := 0
    maske := false
    vektor := 0
    kern := 2 }

/-- After setting the mask. -/
def a2 : ArchState :=
  { priv := Priv.kern
    wurzel := 0
    maske := true
    vektor := 0
    kern := 2 }

/-- After setting the translation root. -/
def a3 : ArchState :=
  { priv := Priv.kern
    wurzel := 7
    maske := true
    vektor := 0
    kern := 2 }

/-- After leaving the kernel. -/
def a4 : ArchState :=
  { priv := Priv.nutzer
    wurzel := 7
    maske := true
    vektor := 0
    kern := 2 }

/-- Step one: a user state may enter the kernel. -/
theorem zSchritt1 : ArchStep ArchOp.enterKernel a0 a1 :=
  ArchStep.betrete a0

/-- Step two: at kernel privilege the mask is set. -/
theorem zSchritt2 : ArchStep (ArchOp.setMask true) a1 a2 :=
  ArchStep.maske a1 true rfl

/-- Step three: at kernel privilege the root is set. -/
theorem zSchritt3 : ArchStep (ArchOp.setRoot 7) a2 a3 :=
  ArchStep.wurzel a2 7 rfl

/-- Step four: at kernel privilege the kernel is left. -/
theorem zSchritt4 : ArchStep ArchOp.leaveKernel a3 a4 :=
  ArchStep.verlasse a3 rfl

/-- The run ends unprivileged. -/
theorem zEndePriv : a4.priv = Priv.nutzer :=
  rfl

/-- The run ends masked. -/
theorem zEndeMaske : a4.maske = true :=
  rfl

/-- The run ends with the installed root. -/
theorem zEndeWurzel : a4.wurzel = 7 :=
  rfl

/-- The run never moved the core. -/
theorem zEndeKern : a4.kern = 2 :=
  rfl

/-- Refused: no `setMask` step leaves the user start. -/
theorem zVerweigert (s' : ArchState) :
    ¬ ArchStep (ArchOp.setMask true) a0 s' :=
  fun h => keinMaskeNutzer true a0 s' rfl h

#print axioms Gabbro.Grammatik.Niedrig.Arch.zSchritt2
#print axioms Gabbro.Grammatik.Niedrig.Arch.zEndeWurzel
#print axioms Gabbro.Grammatik.Niedrig.Arch.zVerweigert

end Gabbro.Grammatik.Niedrig.Arch
