/-
  File:      stage0/Stage0/Senke/Bild/Ruf/Hardware.lean
  Subject:   **The oracle premises of the image theorem come from the goal theorem's hardware assumptions.** The named
             class `LeseblindOK` (register and visibility answers do not look at read events) follows from
             `RegLokal`, one of the named components of `HardwareAnnahmen` (Zielsatz/Kern/Spec): a register answer
             depends on the register's device carriers and a visibility answer on the awaited global, and `≈` worlds
             have the same memory. So every oracle the goal theorem speaks about has it -- no premise of its own.
             The foreign half (`LeseblindW`) is needed only by a program WITH foreign calls; a program without
             (`FremdFrei`, a decidable check per body) has the whole program premise `LeseblindP` from the hardware
             assumptions alone (`leseblindP_hardware`).

             Witness (`zaehlOrakel`): an oracle whose foreign answer COUNTS the trace -- read events included, so it
             is not read-blind -- still meets the premise of every program without foreign calls.
-/
module
public import Stage0.Senke.Bild.Ruf.RufOkGleich
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraetSem.Teil1
public import Grammatik.Zielsatz.Kern.Spec.Teil1
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik

set_option linter.unusedSectionVars false

variable {D : Deklaration}

/-- `≈` worlds agree on every footprint. -/
theorem WeltGleich.gleichAuf {σ σ' : World D} (h : WeltGleich σ σ') (S : List (D.Tab ⊕ D.Glob)) :
    GleichAuf S σ σ' :=
  ⟨fun t _ => congrFun h.slots t, fun g _ => congrFun h.globs g⟩

/-- **Register locality gives read-blind register and visibility answers.** -/
theorem leseblindRS_regLokal {O : Orakel D} (h : RegLokal O) : LeseblindRS O :=
  ⟨fun r σ σ' hw => h.1 r σ σ' (hw.gleichAuf _), fun g σ σ' hw => h.2 g σ σ' (hw.gleichAuf _)⟩

/-- **The named oracle property from the named hardware assumption.** -/
theorem leseblindOK_regLokal {O : Orakel D} (h : RegLokal O) : LeseblindOK O :=
  ⟨leseblindRS_regLokal h⟩

/-- **Every oracle of the goal theorem has the named oracle property.** -/
theorem leseblindOK_hardware {O : Orakel D} {Q : AxEns D} (h : Zielsatz.HardwareAnnahmen O Q) :
    LeseblindOK O := by
  unfold Zielsatz.HardwareAnnahmen at h
  exact leseblindOK_regLokal h.2.1

/-- **The program premise from the hardware assumptions**, for a program without foreign calls. -/
theorem leseblindP_hardware {P : Programm D} {O : Orakel D} {Q : AxEns D} (h : Zielsatz.HardwareAnnahmen O Q)
    (hP : FremdFrei P) : LeseblindP P O := by
  unfold Zielsatz.HardwareAnnahmen at h
  exact leseblindP_frei (leseblindRS_regLokal h.2.1) hP

/-- An oracle that is NOT read-blind: a foreign call answers the length of the trace, read events included. Registers
    read `0`, every publication is visible. -/
def zaehlOrakel (D : Deklaration) : Orakel D where
  wirkt := fun _ σ _ => (σ, (σ.spur.length : Int))
  regLies := fun _ _ => 0
  regSchreib := fun _ _ => ()
  sichtbar := fun _ _ => true

/-- The counting oracle is register-local. -/
theorem zaehlOrakel_regLokal (D : Deklaration) : RegLokal (zaehlOrakel D) :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

/-- **Witness**: the counting oracle meets the program premise of every program without foreign calls, although its
    foreign answers see read events. -/
theorem leseblindP_zaehl {P : Programm D} (hP : FremdFrei P) : LeseblindP P (zaehlOrakel D) :=
  leseblindP_frei (leseblindRS_regLokal (zaehlOrakel_regLokal D)) hP

/-- The counting oracle's foreign answer does see a read: one read of a nonempty place list changes it. -/
theorem zaehlOrakel_sieht (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) (Λ : List (Res D))
    {os : List (D.Tab ⊕ D.Glob)} (hne : os ≠ []) :
    WeltGleich σ (σ.lese Λ os) ∧ ((zaehlOrakel D).wirkt a σ ρ).2 ≠ ((zaehlOrakel D).wirkt a (σ.lese Λ os) ρ).2 := by
  refine ⟨weltGleich_lese σ Λ os, ?_⟩
  show ((σ.spur.length : Nat) : Int) ≠ (((σ.lese Λ os).spur.length : Nat) : Int)
  rw [lese_spur_length]
  cases os with
  | nil => exact absurd rfl hne
  | cons o os =>
      rw [List.length_cons]
      omega

#print axioms leseblindOK_hardware
#print axioms leseblindP_hardware

end Gabbro.Stage0.Senke.BildLauf
