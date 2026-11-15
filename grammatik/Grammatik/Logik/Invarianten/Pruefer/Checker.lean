module

public import Grammatik.Logik.Invarianten.Pruefer.Duties
public import Grammatik.Zielsatz.Atomar.AkzeptiertSchnell

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Pruefer

open Zielsatz

variable {D : Deklaration} [DecidableEq D.Fn] [DecidableEq D.Ax]
  {program : Programm D} {S : SperrInv D} {functions starts : List D.Fn}
  {locks : List D.Lock} {carriers : List (D.Tab ⊕ D.Glob)}
  {accumulators : List (Kernzelle.AccumulatorDecl D)} {checks : List (CheckDecl D)}
  {queries : List D.Ax} {guests : List (GuestBoundary D)} {sources : LockSources S}
  {hints : Vertraege.Pruefer.LoopHints D}

theorem invariantVCB_of_akzeptiert
    (accepted : Akzeptiert program S functions locks carriers starts
      accumulators checks queries guests sources = true) :
    invariantVCB program S functions sources {} (fun _ => none) locks = true :=
  (Bool.and_eq_true_iff.mp accepted).2

theorem invariantVCB_of_akzeptiertX
    (accepted : AkzeptiertX program S functions locks carriers starts
      accumulators checks queries guests sources hints = true) :
    invariantVCB program S functions sources {} hints locks = true :=
  (Bool.and_eq_true_iff.mp accepted).2

theorem invariantVCB_of_akzeptiertXVoll
    (accepted : AkzeptiertXVoll program S functions locks carriers starts
      accumulators checks queries guests sources hints = true) :
    invariantVCB program S functions sources {} hints locks = true :=
  (Bool.and_eq_true_iff.mp accepted).2

/-- Acceptance supplies the invariant part of the existing atomic user duty.
    The other user premises and the statement of gabbro_ziel are unchanged. -/
theorem logikPflichtA_of_akzeptiertX (complete : ∀ f, f ∈ functions)
    (accepted : AkzeptiertX program S functions locks carriers starts
      accumulators checks queries guests sources hints = true)
    (Q : AxEns D) (shared : D.Tab ⊕ D.Glob → Prop)
    (subset : ∀ carrier, shared carrier → AtomarAusgenommen carrier)
    (locality : SperrInvLokal S ∧ AxEnsLokal Q ∧ PtrVerfeinert program) :
    LogikPflichtA program S Q shared :=
  logikPflichtA_of_invariantVCB complete (invariantVCB_of_akzeptiertX accepted)
    Q shared subset locality

#print axioms invariantVCB_invGutA
#print axioms invariantVCB_invGut
#print axioms logikPflichtA_of_akzeptiertX

end Gabbro.Grammatik.Invarianten.Pruefer
