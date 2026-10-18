/-
  File:      Grammatik/MitRuheSemantik.lean
  Subject:   EVERY FUNCTION OF P BEHAVES IN P.mitRuhe AS IN P (MitRuhe.lean).
             Expressions evaluate to the translated value (eval_ru); reads
             record the translated events (lese_worldR); every statement,
             block and end block of a translated body runs, from the
             translated world and environment under O.mitRuhe, to the
             translated outcome, given call handlers that answer translated
             calls with translated answers (execStmt_ru, execBlock_ru,
             execEnd_ru); hence the body of some f in P.mitRuhe runs as the
             body of f in P (rumpf_mitRuhe_verhalten), requires holds at some f
             exactly when it holds at f (req_mitRuhe_iff), and every CALL --
             requires, body, ensures, owed invariants, at every depth -- of
             P.mitRuhe at some f behaves as the call of P at f
             (rufAt_mitRuhe; the generic form of gPB_wie_gP).

  NOT here (open): the same for execEndH, the lock-aware semantics the user
  obligation KoerperGutS is stated against (it quantifies over oracles,
  environment moves and handlers on the D.mitRuhe side, each of which is the
  translation of one on the D side); with it the user obligation on P
  transfers to P.mitRuhe.
-/

import Grammatik.Nebenlaeufigkeit.Sperren.MitRuheSemantik.T1
import Grammatik.Nebenlaeufigkeit.Sperren.MitRuheSemantik.T2
import Grammatik.Nebenlaeufigkeit.Sperren.MitRuheSemantik.T3
import Grammatik.Nebenlaeufigkeit.Sperren.MitRuheSemantik.T4
