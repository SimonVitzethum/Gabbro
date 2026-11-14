module

public import Grammatik.Logik.Invarianten.Pruefer.Locks
public import Grammatik.Speichermodell.Atomar.Invariants.AtomarRec

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Pruefer

open Frag Elim Elim.Korrekt VC Modell

variable {D : Deklaration}

/-- The invariant duties needed by the goal, uniformly in the hardware
    contract, execution budget and choice of shared atomic carriers. This is
    semantic evidence obtained from checked VCs, never a checker input. -/
def InvariantDuties (program : Programm D) (S : SperrInv D) (f : D.Fn) : Prop :=
  ∀ (passes : Nat) (Q : AxEns D) (shared : D.Tab ⊕ D.Glob → Prop),
    (∀ carrier, shared carrier → AtomarAusgenommen carrier) →
    InvGutSA program passes Q S shared f ∧ InvGutGrundA program passes Q S shared f

def atomicFreeB (program : Programm D) (f : D.Fn) : Bool :=
  (endblockOrteP program (program.rumpf f)).all fun carrier =>
    match carrier with
    | .inl _ => true
    | .inr name => !D.atomar name

theorem atomicFreeB_sound (program : Programm D) (f : D.Fn)
    (accepted : atomicFreeB program f = true) :
    ∀ carrier ∈ endblockOrteP program (program.rumpf f), ¬ AtomarAusgenommen carrier := by
  intro carrier member atomic
  obtain ⟨name, same, atom⟩ := atomic
  subst carrier
  have fact := List.all_eq_true.mp accepted (.inr name) member
  simp only [atom, Bool.not_true, Bool.false_eq_true] at fact

end Gabbro.Grammatik.Invarianten.Pruefer
