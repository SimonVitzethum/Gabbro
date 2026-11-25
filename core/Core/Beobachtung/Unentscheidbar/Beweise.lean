module

public import Core.Beobachtung.Unentscheidbar.Reduktion
public import Core.Beobachtung.Unentscheidbar.Rice

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar

/-- The pinned halting statement: for every simulation substrate and every fixed
    input, the Gabbro halting predicate over program numbers is undecidable.
    Discharged by the many-one reduction of the mu-recursive halting problem in
    `Reduktion.lean`. -/
theorem halteUnentscheidbar : HalteUnentscheidbarAussage := by
  intro s n
  exact substrat_halts_unentscheidbar s n

/-- The pinned Rice statement: every nontrivial extensional property of
    simulated Gabbro programs is undecidable as a predicate over program
    numbers. Discharged by the Rice transfer in `Rice.lean`. -/
theorem riceUnentscheidbar : RiceAussage := by
  intro s Q hext hn
  exact substrat_rice s Q hext hn

end Gabbro.Core.Beobachtung.Unentscheidbar
