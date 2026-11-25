/-
  File:      core/Core/Ziel/Korrektheit/PrueferRestBeweis.lean
  Subject:   Direct proof of the pinned `PrueferRestUnentscheidbarAussage`.

  No pinned statement is changed and no open `…Aussage` is used as a premise: the target is
  definitionally `Beobachtung.Unentscheidbar.RiceAussage`, and the theorem `substrat_rice`
  proves that transfer for every simulation substrate, extensional property and non-triviality
  witness from Mathlib's Rice theorem alone. The substrate-existence statement
  (`SubstratAussage`) is intentionally not needed: `substrat_rice` quantifies over the substrate.
-/
module

public import Core.Ziel.Korrektheit.Pruefer
public import Core.Beobachtung.Unentscheidbar.Rice

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core

/-- The checker's undecidable remainder is proved: the Rice transfer holds for every substrate and every
    extensional property that is neither empty nor full on the simulation image. -/
theorem prueferRestUnentscheidbar : PrueferRestUnentscheidbarAussage := by
  intro s Q hExt hNontrivial
  exact Beobachtung.Unentscheidbar.substrat_rice s Q hExt hNontrivial

end Gabbro.Core.Ziel.Korrektheit
