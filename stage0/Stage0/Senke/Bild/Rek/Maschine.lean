/-
  File:      stage0/Stage0/Senke/Bild/Rek/Maschine.lean
  Subject:   **Boundaries inside a callee, machine G** (package P4 of the closed calls of the image theorem, part 1).
             Until P3 a call is ONE decomposed step: the image states inside the callee correspond only to the
             caller's machine in front of the call. P4 descends into the callee. On machine G the descent is the
             step `ruf` of a plain call at `ende` position (`w_rufEnde`): it pushes the caller frame, waiting behind
             the call (`rufRahmenNach`), and starts the callee's frame at the residue `.ende (P.rumpf g)`, with the
             argument values of the read world and that world as its entry world.

             The image's handler `rufAt` runs the callee's body in the world after the argument reads AND the read
             of the callee's `requires` places (`rufWelt`); machine G reads no contract. So the callee's first body
             boundary holds up to read events (`RandGL`): the machine's entry world `σm` is `≈` to `rufWelt` (it IS
             the world after the argument reads on the machine side, `≈` to the sequential one), the environment is
             the sequential argument environment (`rufEnv`; arguments do not see the trace), the callee's entry
             holdings follow from the caller's (`heldB_eintritt`), and no other thread moved.
-/
module
public import Stage0.Senke.Bild.Ruf.RufOkGleich
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik

set_option linter.unusedSectionVars false

variable {D : Deklaration}

/-! ## The callee's entry: the world, the environment, the waiting caller -/

/-- **The world the image's handler runs the callee's body in**: the reads of the call's arguments, then the read of
    the callee's `requires` places (`rufAt`). -/
abbrev rufWelt (P : Programm D) (g : D.Fn) (σ : World D) (Λ : List (Res D)) {Γ : Ctx}
    (args : Args D Γ Λ (D.params g)) : World D :=
  (σ.lese Λ args.orte).lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte

/-- **The callee's parameters**: the argument values in the world after the argument reads. -/
abbrev rufEnv (g : D.Fn) (σ : World D) (Λ : List (Res D)) {Γ : Ctx} (args : Args D Γ Λ (D.params g))
    (ρ : Env D Γ) : Env D (D.params g) :=
  evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ

/-- **The caller frame below a callee**: the frame of `f` (parameters `rho`, entry world `s0`), resumed behind a plain
    call at the residue `.ende rest` with the environment `ρ`. -/
abbrev rufRahmenNach {f : D.Fn} (rho : Env D (D.params f)) (s0 : World D) {l : Bool} {Γ : Ctx}
    {Λ' : List (Res D)} (ρ : Env D Γ) (rest : Endblock D (vertragVon D f) l Γ Λ') : RufRahmenG D :=
  ⟨f, rho, s0, ⟨l, Γ, Λ', ρ, .ende rest⟩⟩

/-- The world after the argument reads is `≈` to the callee's body world (only the `requires` read lies between). -/
theorem rufWelt_gleich (P : Programm D) (g : D.Fn) (σ : World D) (Λ : List (Res D)) {Γ : Ctx}
    (args : Args D Γ Λ (D.params g)) : WeltGleich (rufWelt P g σ Λ args) (σ.lese Λ args.orte) :=
  (weltGleich_lese (σ.lese Λ args.orte) (Signatur.anfang D (D.signatur g)) (P.requires g).orte).symm

/-! ## The descent, machine G -/

/-- **Into the callee, machine G**: from a boundary up to read events in front of a plain call `g(args); rest` (the
    thread runs the frame of `f` above `stapel`), thread `thr` takes the step `ruf`: it stands at the first body
    boundary of `g` (residue `.ende (P.rumpf g)`), up to read events against the image handler's body world
    `rufWelt`, with the caller frame waiting behind the call on top of `stapel`, the callee's parameters `rufEnv`
    and the machine's own entry world `σm` (`≈` to the sequential world after the argument reads). -/
theorem randGL_ruf_eintritt {P : Programm D} {O : Orakel D} {passes : Nat} {thr : Faden}
    {stapel : List (RufRahmenG D)} {f : D.Fn} {rho : Env D (D.params f)} {s0 : World D} {Agl : D.Lock → Prop}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {g : D.Fn} {args : Args D Γ Λ (D.params g)}
    {hp : RufPasst D (vertragVon D f) (D.signatur g) Λ} {hr : D.gruende g = 0}
    {rest : Endblock D (vertragVon D f) l Γ (nach D g Λ)} {M : RufMaschineG D} {σ : World D} {ρ : Env D Γ}
    (h : RandGL thr stapel f rho s0 Agl (.cons (.call g args hp hr) rest) M σ ρ) :
    ∃ (M1 : RufMaschineG D) (σm : World D), RufLaufG P O passes thr M M1 ∧
      WeltGleich (σ.lese Λ args.orte) σm ∧
      RandGL thr (rufRahmenNach rho s0 ρ rest :: stapel) g (rufEnv g σ Λ args ρ) σm Agl (P.rumpf g) M1
        (rufWelt P g σ Λ args) (rufEnv g σ Λ args ρ) := by
  obtain ⟨σm0, hw, ⟨log, hZ⟩, hΛ, hA⟩ := h
  have hW := hZ.welt
  obtain ⟨M1, hs1, hZ1⟩ := w_rufEnde (P := P) (O := O) (passes := passes) hZ.1 g args hp hr rest ρ rfl
    hΛ.heldIn
  rw [hW] at hZ1
  have hw1 : WeltGleich (σ.lese Λ args.orte) (σm0.lese Λ args.orte) := hw.lese Λ args.orte
  have hargs : evalArgs (σm0.lese Λ args.orte) args (σm0.lese Λ args.orte) ρ = rufEnv g σ Λ args ρ :=
    (hw1.werte args ρ).symm
  rw [hargs] at hZ1
  have hl : RufLaufG P O passes thr M M1 := RufLaufG.einzeln hs1
  have hG : RandG thr (rufRahmenNach rho s0 ρ rest :: stapel) g (rufEnv g σ Λ args ρ) (σm0.lese Λ args.orte)
      Agl (P.rumpf g) M1 (σm0.lese Λ args.orte) (rufEnv g σ Λ args ρ) :=
    ⟨⟨_, hZ1⟩, heldB_eintritt hp hΛ args.orte Λ, hA.lauf hl⟩
  exact ⟨M1, σm0.lese Λ args.orte, hl, hw1, σm0.lese Λ args.orte,
    (rufWelt_gleich P g σ Λ args).trans hw1, hG⟩

#print axioms randGL_ruf_eintritt

end Gabbro.Stage0.Senke.BildLauf
