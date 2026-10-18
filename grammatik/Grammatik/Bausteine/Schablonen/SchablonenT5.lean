/-
  File:      Grammatik/SchablonenT5.lean
  Part of:   Gabbro -- the generator-template library (T5 of
             dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md).

  What this file is: ABSTRACT cores for the templates of
  `crates/gabbro-check/src/schablonen.rs` -- abstract cores, NOT tied
  to the semantics. Every lemma below is proved in Lean 4.33.1 over a
  small SELF-INVENTED model of the template named in its doc comment;
  these models are not connected to Gabbro's semantics (`execStmt` /
  `execEnd`, `World`, `EmitLay`), so they prove nothing about any
  Gabbro program. The semantics-tied versions live in
  `Grammatik/SchablonenT5Sem.lean`. Every lemma comes with a
  `NAME_zeuge` that instantiates ALL premises JOINTLY on concrete
  values only -- no witness here is tied to a program run (the former
  `refB` conjuncts were removed as decoration on 2026-09-14 review:
  conjoining an unrelated run fact is not inhabitation).

  Order: most-used corpus construct first (measured 2026-09-13 over
  `beispiele/`: table/count 370/354, locks 292, device 130, option 90,
  entry 89, clobbers 80, format 58, transition 34, exchange 31,
  accumulates/mappings 23, consuming 13, group 10, reset 9, restrict 5,
  induction 3, transset 2).
-/


import Grammatik.Bausteine.Schablonen.SchablonenT5.T1
import Grammatik.Bausteine.Schablonen.SchablonenT5.T2
import Grammatik.Bausteine.Schablonen.SchablonenT5.T3
