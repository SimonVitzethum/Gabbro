/-
  Subject: Satisfiability of the reachability premises of machine G (stream E6, owner rule of 2026-11-19).

  `ruf_erreichbar_erfuellbar`: from the start machine of a program, a call step and the matching return step are
  steps of machine G, and the machine after both is reachable. The premises `RufSchrittG` and `RufErreichbarG` of
  the run lemmas therefore hold on a run that enters and leaves a callee frame, not only on the start machine.
-/
module

public import Grammatik.Kern.Syntax.Marken.Owner.EscrowRun

@[expose] public section

namespace Gabbro.Grammatik

open EscrowWitness in
/-- **Satisfiability of the reachability premises**: a call step and its return step from the start machine, and
    the machine after both reachable from the start. -/
theorem ruf_erreichbar_erfuellbar :
    ∃ (D : Deklaration) (P : Programm D) (O : Orakel D) (sp : Speicher D)
      (init : Faden → Σ f : D.Fn, Env D (D.params f)) (M1 M2 : RufMaschineG D),
      RufSchrittG P O 0 (RufStartG P sp init) 0 M1 ∧ RufSchrittG P O 0 M1 0 M2 ∧
      RufErreichbarG P O 0 (RufStartG P sp init) M2 :=
  ⟨escrowD, progE, orakelE, spE, initE, M1E, M2E, schrittPushE, schrittPopE,
    .schritt _ _ _ (.schritt _ _ _ .start schrittPushE) schrittPopE⟩

end Gabbro.Grammatik
