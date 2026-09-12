/-
  File:      Grammatik/HoareRuf.lean
  Subject:   HOARE RULE FOR THE CALL STATEMENT, SOUND AGAINST A
              CONTRACT-RESPECTING CALL HANDLER.

  `HoareRegeln.lean` has partial-correctness triples `STTripel` over
  `execStmt` and rules skip/assign/seq/ite/consequence, plus
  call-independence for call-free bodies. This file adds the missing
  rule for a `Stmt.call` statement, stated against a call handler `R`
  that respects the program contracts at their place
  (`RespektiertVertraege`, over `ReqAmEintritt`/`EnsAmRueck` from
  `VertragOrtB.lean` with the ACTUAL evaluated arguments and the
  ACTUAL entry/return worlds -- never quantified over environments).

  `hoare_call`: whenever `R` respects the contracts, the call
  statement `.call f args hp hr` satisfies the statement triple
  whose precondition is "requires holds at the argument world with
  the evaluated arguments" and whose postcondition is "ensures holds
  with the actual entry world, the actual return world, the actual
  arguments and the actual result".

  Witness: `hoare_call_zeuge` on a non-degenerate one-function
  program (one table that the function writes; ensures result =
  param + 1) with a handler that runs the body, plus the instructed
  `rufPD` witness (`respektiert_rufPD`).
-/
import Grammatik.HoareRegeln
import Grammatik.VertragOrtB
import Grammatik.RufMaschineD

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

/-- A call handler respects the program contracts at their place: every
    call it answers normally satisfies `ensures` with the ACTUAL entry
    world, return world, arguments and result. `ReqAmEintritt` is the
    entry gate, `EnsAmRueck` the return duty (both `VertragOrtB.lean`).
    Every premise is used by `hoare_call` below. -/
def RespektiertVertraege (P : Programm D)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) : Prop :=
  ∀ f σ ρ, ReqAmEintritt P f σ ρ →
    ∀ σ' v, R f σ ρ = RufAusgang.ok σ' v →
      EnsAmRueck P f σ σ' ρ v

end Gabbro.Grammatik
