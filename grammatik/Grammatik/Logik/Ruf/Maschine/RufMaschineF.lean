/-
  File:      Grammatik/RufMaschineF.lean
  Subject:   THE CALL MACHINE WITH LOCAL ENVIRONMENTS (attempt F) -- threads
             with a FRAME STACK over shared memory, where each frame carries
             the environment of its CURRENT context next to its residue.

  Why: `RufMaschineD.lean` (see its REVIEWER NOTE) threads every step through
  a FREE `rho : Env D Gamma`: a step may run under ANY values of the locals,
  so the machine over-approximates the program. Here each frame carries
  `Gamma` with `rho : Env D Gamma` next to the residue
  `Endblock D (vertragVon D f) l Gamma Lambda`: `blatt` runs `execStmt` with
  the STORED `rho` and stores the resulting `rho'` (the `.ok` outcome);
  `ruf` evaluates the arguments in the caller's stored `rho`; `rueck`
  evaluates the result in the callee's stored `rho`. No step constructor
  keeps a free `rho` binder. The stack/log invariant compares frames only by
  (function, parameter environment, entry world) -- never by residue -- and
  its preservation along `RufSchrittF` is proved, lifting return fidelity
  (`rufF_treu`) to every reachable machine by induction.
-/

import Grammatik.Logik.Ruf.Maschine.RufMaschineF.T1
import Grammatik.Logik.Ruf.Maschine.RufMaschineF.T2
import Grammatik.Logik.Ruf.Maschine.RufMaschineF.T3
