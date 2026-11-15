module

public import Grammatik.Logik.Invarianten.Pruefer.Program
public import Grammatik.Zielsatz.Atomar.AtomarPflicht

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Pruefer

open Zielsatz

variable {D : Deklaration} {program : Programm D} {S : SperrInv D}
  {functions : List D.Fn} {sources : LockSources S} {budget : VC.VCBudget}

theorem invariantVCB_invGut (complete : ∀ f, f ∈ functions)
    (accepted : invariantVCB program S functions sources budget = true)
    (passes : Nat) (Q : AxEns D) (f : D.Fn) :
    InvGutS program passes Q S f ∧ InvGutGrund program passes Q S f := by
  have facts := invariantVCB_invGutA complete accepted passes Q (fun _ => False)
    (fun _ impossible => False.elim impossible) f
  exact ⟨invGutS_of_A facts.1, invGutGrund_of_A facts.2⟩

/-- Reconstruct the existing SC duty from the checker certificate. Only the
    locality and pointer premises remain inputs; Spec itself is unchanged. -/
theorem logikPflicht_of_invariantVCB (complete : ∀ f, f ∈ functions)
    (accepted : invariantVCB program S functions sources budget = true)
    (Q : AxEns D)
    (locality : SperrInvLokal S ∧ AxEnsLokal Q ∧ PtrVerfeinert program) :
    LogikPflicht program S Q :=
  ⟨fun passes f => ⟨koerperGutS_of_A
      ((invariantVCB_sound complete accepted f passes Q (fun _ => False)
        (fun _ impossible => False.elim impossible)).1),
      invariantVCB_invGut complete accepted passes Q f⟩,
    locality⟩

/-- The same adapter preserves the atomic rely rather than replacing shared
    reads with sequential reads. Unsupported atomic-reading bodies refuse. -/
theorem logikPflichtA_of_invariantVCB (complete : ∀ f, f ∈ functions)
    (accepted : invariantVCB program S functions sources budget = true)
    (Q : AxEns D) (shared : D.Tab ⊕ D.Glob → Prop)
    (subset : ∀ carrier, shared carrier → AtomarAusgenommen carrier)
    (locality : SperrInvLokal S ∧ AxEnsLokal Q ∧ PtrVerfeinert program) :
    LogikPflichtA program S Q shared :=
  ⟨fun passes f => ⟨(invariantVCB_sound complete accepted f passes Q shared subset).1,
    invariantVCB_invGutA complete accepted passes Q shared subset f⟩, locality⟩

end Gabbro.Grammatik.Invarianten.Pruefer
