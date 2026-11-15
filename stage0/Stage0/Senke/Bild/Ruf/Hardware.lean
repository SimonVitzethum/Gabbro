/-
  File:      stage0/Stage0/Senke/Bild/Ruf/Hardware.lean
  Subject:   **Read-blindness needs no assumption; the counting-oracle witness.** Machine G hands the oracle the world
             WITHOUT its read events (`Orakel.wirkt`, grammatik Kern/Semantik/Semantik/T1/Lese.lean, 2026-11-13), so
             register and visibility answers (`leseblindRS_alle`) and foreign answers (`leseblindW_alle`) never look
             at read events, whatever the oracle: read-blindness is a theorem (`leseblindP_alle`), not a premise, and
             not a consequence of the hardware assumptions either.

             Witness (`zaehlOrakel`): an oracle whose foreign answer COUNTS the history of the thread -- every question,
             write and lock move before the call -- still answers alike before and after a read
             (`zaehlOrakel_lese`), and still answers differently after a further question (`zaehlOrakel_fragt`):
             the interface erases reads only, and a repeated foreign call may still answer differently.
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

/-- An oracle that answers from the history: a foreign call answers the length of the thread's trace without reads
    (every question, write and lock move before it). Registers read `0`, every publication is visible. -/
def zaehlOrakel (D : Deklaration) : Orakel D where
  wirktL := fun _ ε _ => ({ ε with spur := [] }, (ε.spur.length : Int))
  regLiesL := fun _ _ => 0
  regSchreib := fun _ _ => ()
  sichtbarL := fun _ _ => true

/-- The counting oracle is register-local. -/
theorem zaehlOrakel_regLokal (D : Deklaration) : RegLokal (zaehlOrakel D) :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

/-- The counting oracle answers the rank of the asking world. -/
theorem zaehlOrakel_wirkt (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) :
    ((zaehlOrakel D).wirkt a σ ρ).2 = (σ.rang : Int) := rfl

/-- **A read is invisible to the counting oracle** (as to every oracle, `leseblindW_alle`). -/
theorem zaehlOrakel_lese (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) (Λ : List (Res D))
    (os : List (D.Tab ⊕ D.Glob)) :
    ((zaehlOrakel D).wirkt a σ ρ).2 = ((zaehlOrakel D).wirkt a (σ.lese Λ os) ρ).2 :=
  (leseblindW_alle (zaehlOrakel D) a σ (σ.lese Λ os) ρ (weltGleich_lese σ Λ os)).2

/-- **A further question is visible to the counting oracle**: two calls of one foreign body may still answer
    differently. -/
theorem zaehlOrakel_fragt (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) (q : D.Ax ⊕ D.Reg ⊕ D.Glob) :
    ((zaehlOrakel D).wirkt a σ ρ).2 ≠ ((zaehlOrakel D).wirkt a (σ.fragt q) ρ).2 := by
  rw [zaehlOrakel_wirkt, zaehlOrakel_wirkt, World.rang_fragt]
  omega


end Gabbro.Stage0.Senke.BildLauf
