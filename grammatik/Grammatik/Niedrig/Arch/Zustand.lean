/-
  File:      Grammatik/Niedrig/Arch/Zustand.lean
  Subject:   THE ARCHITECTURAL STATE AS A NEUTRAL INTERFACE (L4a): the
    privilege level `Priv`, the machine-neutral `ArchState`, and the
    privileged operations as the relation `ArchStep` — a neutral state
    with tightness theorems, and nothing more.

  THE LAYER (outside the statement: `Spec.lean`, machine G and `Akzeptiert`
  are not touched; nothing imports these modules except the witness and L5a).
  * `ArchState` holds exactly the L4 row: the privilege level, the
    translation root (an abstract identifier, a `Nat`, never a pointer), the
    interrupt mask, the vector base, and the core identity. No register file,
    no instruction semantics, nothing named after one architecture.
  * `ArchOp` is the neutral operation vocabulary: set the mask, the root or
    the vector base, enter the kernel, leave the kernel. Every operation but
    `enterKernel` steps only at kernel privilege; entering is the one step a
    user state may take.
  * The theorems say the interface is tight: every operation changes only
    its own field, `ArchStep` is deterministic, the core identity never
    changes, and no kernel-privileged operation steps from user privilege.
  * NOT delivered here: privileged operations as calls of target-binding
    functions over `context<P>` with contracts (their meaning a GIR cell
    and their bytes a target-table row, PLAN-COMPILER-READY section 4.1,
    O12) — that connection is L4b; and one generic theorem per entry/exit
    frame kind — those are L5b over the descriptors of `Niedrig.Eingang`.
-/
module

@[expose] public section


namespace Gabbro.Grammatik.Niedrig.Arch

/-- The privilege level, user or kernel, as the plan names the levels. -/
inductive Priv
  | nutzer : Priv
  | kern : Priv
  deriving DecidableEq

/-- The neutral architectural state: privilege, translation root, interrupt
    mask, vector base, core identity. -/
structure ArchState where
  priv : Priv
  wurzel : Nat
  maske : Bool
  vektor : Nat
  kern : Nat

/-- The neutral privileged operations (L4 row, nothing more). -/
inductive ArchOp
  | setMask : Bool → ArchOp
  | setRoot : Nat → ArchOp
  | setVectorBase : Nat → ArchOp
  | enterKernel : ArchOp
  | leaveKernel : ArchOp
  deriving DecidableEq

/-- One privileged step: the operation runs and exactly its field moves. The
    four kernel-privileged operations carry `s.priv = Priv.kern`. -/
inductive ArchStep : ArchOp → ArchState → ArchState → Prop where
  | maske (s : ArchState) (b : Bool) :
    s.priv = Priv.kern → ArchStep (ArchOp.setMask b) s { s with maske := b }
  | wurzel (s : ArchState) (r : Nat) :
    s.priv = Priv.kern → ArchStep (ArchOp.setRoot r) s { s with wurzel := r }
  | vektor (s : ArchState) (v : Nat) :
    s.priv = Priv.kern →
      ArchStep (ArchOp.setVectorBase v) s { s with vektor := v }
  | betrete (s : ArchState) :
    ArchStep ArchOp.enterKernel s { s with priv := Priv.kern }
  | verlasse (s : ArchState) :
    s.priv = Priv.kern → ArchStep ArchOp.leaveKernel s { s with priv := Priv.nutzer }

/-! ## Frame: every operation changes only its own field -/

/-- `setMask` keeps the privilege. -/
theorem schrittMaskePriv (s s' : ArchState) (b : Bool)
    (h : ArchStep (ArchOp.setMask b) s s') : s'.priv = s.priv := by
  cases h <;> rfl

/-- `setMask` keeps the translation root. -/
theorem schrittMaskeWurzel (s s' : ArchState) (b : Bool)
    (h : ArchStep (ArchOp.setMask b) s s') : s'.wurzel = s.wurzel := by
  cases h <;> rfl

/-- `setMask` installs the mask. -/
theorem schrittMaskeMaske (s s' : ArchState) (b : Bool)
    (h : ArchStep (ArchOp.setMask b) s s') : s'.maske = b := by
  cases h <;> rfl

/-- `setMask` keeps the vector base. -/
theorem schrittMaskeVektor (s s' : ArchState) (b : Bool)
    (h : ArchStep (ArchOp.setMask b) s s') : s'.vektor = s.vektor := by
  cases h <;> rfl

/-- `setMask` keeps the core identity. -/
theorem schrittMaskeKern (s s' : ArchState) (b : Bool)
    (h : ArchStep (ArchOp.setMask b) s s') : s'.kern = s.kern := by
  cases h <;> rfl

/-- `setRoot` keeps the privilege. -/
theorem schrittWurzelPriv (s s' : ArchState) (r : Nat)
    (h : ArchStep (ArchOp.setRoot r) s s') : s'.priv = s.priv := by
  cases h <;> rfl

/-- `setRoot` installs the translation root. -/
theorem schrittWurzelWurzel (s s' : ArchState) (r : Nat)
    (h : ArchStep (ArchOp.setRoot r) s s') : s'.wurzel = r := by
  cases h <;> rfl

/-- `setRoot` keeps the interrupt mask. -/
theorem schrittWurzelMaske (s s' : ArchState) (r : Nat)
    (h : ArchStep (ArchOp.setRoot r) s s') : s'.maske = s.maske := by
  cases h <;> rfl

/-- `setRoot` keeps the vector base. -/
theorem schrittWurzelVektor (s s' : ArchState) (r : Nat)
    (h : ArchStep (ArchOp.setRoot r) s s') : s'.vektor = s.vektor := by
  cases h <;> rfl

/-- `setRoot` keeps the core identity. -/
theorem schrittWurzelKern (s s' : ArchState) (r : Nat)
    (h : ArchStep (ArchOp.setRoot r) s s') : s'.kern = s.kern := by
  cases h <;> rfl

/-- `setVectorBase` keeps the privilege. -/
theorem schrittVektorPriv (s s' : ArchState) (v : Nat)
    (h : ArchStep (ArchOp.setVectorBase v) s s') : s'.priv = s.priv := by
  cases h <;> rfl

/-- `setVectorBase` keeps the translation root. -/
theorem schrittVektorWurzel (s s' : ArchState) (v : Nat)
    (h : ArchStep (ArchOp.setVectorBase v) s s') : s'.wurzel = s.wurzel := by
  cases h <;> rfl

/-- `setVectorBase` keeps the interrupt mask. -/
theorem schrittVektorMaske (s s' : ArchState) (v : Nat)
    (h : ArchStep (ArchOp.setVectorBase v) s s') : s'.maske = s.maske := by
  cases h <;> rfl

/-- `setVectorBase` installs the vector base. -/
theorem schrittVektorVektor (s s' : ArchState) (v : Nat)
    (h : ArchStep (ArchOp.setVectorBase v) s s') : s'.vektor = v := by
  cases h <;> rfl

/-- `setVectorBase` keeps the core identity. -/
theorem schrittVektorKern (s s' : ArchState) (v : Nat)
    (h : ArchStep (ArchOp.setVectorBase v) s s') : s'.kern = s.kern := by
  cases h <;> rfl

/-- `enterKernel` raises the privilege. -/
theorem schrittBetretePriv (s s' : ArchState)
    (h : ArchStep ArchOp.enterKernel s s') : s'.priv = Priv.kern := by
  cases h <;> rfl

/-- `enterKernel` keeps the translation root. -/
theorem schrittBetreteWurzel (s s' : ArchState)
    (h : ArchStep ArchOp.enterKernel s s') : s'.wurzel = s.wurzel := by
  cases h <;> rfl

/-- `enterKernel` keeps the interrupt mask. -/
theorem schrittBetreteMaske (s s' : ArchState)
    (h : ArchStep ArchOp.enterKernel s s') : s'.maske = s.maske := by
  cases h <;> rfl

/-- `enterKernel` keeps the vector base. -/
theorem schrittBetreteVektor (s s' : ArchState)
    (h : ArchStep ArchOp.enterKernel s s') : s'.vektor = s.vektor := by
  cases h <;> rfl

/-- `enterKernel` keeps the core identity. -/
theorem schrittBetreteKern (s s' : ArchState)
    (h : ArchStep ArchOp.enterKernel s s') : s'.kern = s.kern := by
  cases h <;> rfl

/-- `leaveKernel` lowers the privilege. -/
theorem schrittVerlassePriv (s s' : ArchState)
    (h : ArchStep ArchOp.leaveKernel s s') : s'.priv = Priv.nutzer := by
  cases h <;> rfl

/-- `leaveKernel` keeps the translation root. -/
theorem schrittVerlasseWurzel (s s' : ArchState)
    (h : ArchStep ArchOp.leaveKernel s s') : s'.wurzel = s.wurzel := by
  cases h <;> rfl

/-- `leaveKernel` keeps the interrupt mask. -/
theorem schrittVerlasseMaske (s s' : ArchState)
    (h : ArchStep ArchOp.leaveKernel s s') : s'.maske = s.maske := by
  cases h <;> rfl

/-- `leaveKernel` keeps the vector base. -/
theorem schrittVerlasseVektor (s s' : ArchState)
    (h : ArchStep ArchOp.leaveKernel s s') : s'.vektor = s.vektor := by
  cases h <;> rfl

/-- `leaveKernel` keeps the core identity. -/
theorem schrittVerlasseKern (s s' : ArchState)
    (h : ArchStep ArchOp.leaveKernel s s') : s'.kern = s.kern := by
  cases h <;> rfl

/-! ## The step is deterministic and never moves the core -/

/-- `ArchStep` is deterministic: one operation from one state reaches one state. -/
theorem schrittDet (op : ArchOp) (s a b : ArchState)
    (h1 : ArchStep op s a) (h2 : ArchStep op s b) : a = b := by
  cases h1 <;> cases h2 <;> rfl

/-- The core identity never changes, under any operation. -/
theorem schrittKern (op : ArchOp) (s s' : ArchState)
    (h : ArchStep op s s') : s'.kern = s.kern := by
  cases h <;> rfl

/-! ## Kernel-privileged operations have no step from user privilege -/

/-- `setMask` has no step from user privilege. -/
theorem keinMaskeNutzer (b : Bool) (s s' : ArchState)
    (hn : s.priv = Priv.nutzer)
    (h : ArchStep (ArchOp.setMask b) s s') : False := by
  cases h with
  | maske _ _ hk =>
    rw [hk] at hn
    exact Priv.noConfusion hn

/-- `setRoot` has no step from user privilege. -/
theorem keinWurzelNutzer (r : Nat) (s s' : ArchState)
    (hn : s.priv = Priv.nutzer)
    (h : ArchStep (ArchOp.setRoot r) s s') : False := by
  cases h with
  | wurzel _ _ hk =>
    rw [hk] at hn
    exact Priv.noConfusion hn

/-- `setVectorBase` has no step from user privilege. -/
theorem keinVektorNutzer (v : Nat) (s s' : ArchState)
    (hn : s.priv = Priv.nutzer)
    (h : ArchStep (ArchOp.setVectorBase v) s s') : False := by
  cases h with
  | vektor _ _ hk =>
    rw [hk] at hn
    exact Priv.noConfusion hn

/-- `leaveKernel` has no step from user privilege. -/
theorem keinVerlasseNutzer (s s' : ArchState)
    (hn : s.priv = Priv.nutzer)
    (h : ArchStep ArchOp.leaveKernel s s') : False := by
  cases h with
  | verlasse _ hk =>
    rw [hk] at hn
    exact Priv.noConfusion hn

#print axioms Gabbro.Grammatik.Niedrig.Arch.schrittDet
#print axioms Gabbro.Grammatik.Niedrig.Arch.schrittKern
#print axioms Gabbro.Grammatik.Niedrig.Arch.keinMaskeNutzer
#print axioms Gabbro.Grammatik.Niedrig.Arch.keinVerlasseNutzer

end Gabbro.Grammatik.Niedrig.Arch
