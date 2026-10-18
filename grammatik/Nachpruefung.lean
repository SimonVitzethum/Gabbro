/-
  **Nachpruefung.lean -- the ten-minute check, for a reviewer who wants to see it, not be told.**

  This file proves nothing. It asks Lean, in the reviewer's own build, three questions about
  the sentences this project claims -- and every answer is printed by the kernel, not by us:

    1. WHICH AXIOMS does each sentence rest on? `#print axioms` walks the whole proof term.
       The expected answer is Lean's standard three (`propext`, `Classical.choice`,
       `Quot.sound`) and nothing else. **A `sorryAx` in the list means the sentence is NOT
       proved** -- that is exactly what this file is for.
    2. WHAT DOES THE STATEMENT SAY? `#check` prints the type. The goal theorem's text is the
       thing under review; no axiom list can tell you whether it is the right statement.
    3. ARE THE WITNESSES REAL? A sentence over an empty world is true and worthless, so the
       witnesses below are printed with their axioms too.

  Run it:  cd grammatik && lake build && lake env lean Nachpruefung.lean
  (`lake build` first: this file imports the library, and `lake env lean` does not build it.)
-/
import Grammatik

open Gabbro.Grammatik

/-! ## 1. The goal theorem: what it says, and what it rests on -/

-- The statement under review (the long form with its assumption list is in
-- `Grammatik/Zielsatz/Spec.lean`; read that file, not this printout, for the review).
#check @Gabbro.Grammatik.Zielsatz.GabbroZiel
#check @Gabbro.Grammatik.Zielsatz.gabbro_ziel

-- The whole chain of the goal theorem, in one line of kernel output.
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel
-- The statement of before (without the atomic rely, lane O25c), and its derivation.
#check @Gabbro.Grammatik.Zielsatz.GabbroZielSC
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel_sc
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel_sc_aus

/-! ## 2. Non-degeneracy: the witnesses -/

-- A two-thread program that actually moves memory, accepted by the checker Bool, with the
-- goal's conclusion on it -- so the theorem is not vacuous for want of an accepted program.
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel_zeuge

-- And the refutations: programs the checker REFUSES. A checker that accepts everything would
-- make the theorem trivial; these say it does not.
#print axioms Gabbro.Grammatik.Zielsatz.probeA_widerlegt_gilt
#print axioms Gabbro.Grammatik.Zielsatz.probeD_widerlegt_gilt
#print axioms Gabbro.Grammatik.Zielsatz.w1_abgelehnt

/-! ## 3. The corpus units: the user's logic of two real programs

`beispiele/104` and `beispiele/108` are parsed by the Lean pipeline from their real source text and
lowered to machine G; `NutzerPflicht` (premise (b) of the goal theorem) is proved on the parsed
bodies. (The C correspondence chain of these units was deleted with the C emitter: tag
`archiv/c-emitter-2026-10-17`.) -/

#print axioms Gabbro.Grammatik.Einheit104.nutzer4
#print axioms Gabbro.Grammatik.Einheit108.nutzer8
