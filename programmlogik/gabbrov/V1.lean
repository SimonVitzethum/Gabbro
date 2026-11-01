/-
  File:    gabbrov/V1.lean
  Subject: **V1 of `dokumente/GABBROV.md` -- are the 66 logic obligations SAYABLE in the
           Lean fragment of §7?**

  This file is the measurement, not a report about one. Every one of the 66 `L` rows of
  `dokumente/PFLICHTEN.md` stands below as a Lean `Prop` over `Gabbro.Body.State`, or it
  stands below with the reason it cannot -- and `lean` type-checks the file either way.
  *A count of what is expressible, produced by a tool that refuses what is not, is worth
  more than the same count produced by a reader.*

  WHY IT IMPORTS `Gabbro.Body` AND DEFINES NO SECOND SEMANTICS
    §8: GabbroV checks obligations against a meaning of Gabbro, and GabbroC's correctness
    proof uses one -- **it must be the same one.** So this file adds no `Value`, no `Place`
    and no `World`. Where the existing four-form `Value` cannot carry an obligation, that is
    a FINDING and it is written down as one, not repaired by a local definition that would
    make the two semantics differ in exactly the place the section warns about.

  THE FRAGMENT, as §7 outlines it
    "Lean terms of a certain type, with outlined means: predicates over values, integer and
     bitvector arithmetic with overflow behaviour, aggregation over table domains, pure
     helper functions in the translatable part."

    Taken literally, and every means is built below from Lean core -- `programmlogik` has NO
    mathlib, and its lakefile says why. So no `Finset`, no `Relation.ReflTransGen`: a table
    domain is a `List Int` and the aggregation is `List.filter`.

  THE FOUR VERDICTS, and the count in §8 is read off the file rather than written beside it
    SAYABLE    -- a `Prop` stands there and `lean` accepted it.
    DEMAND     -- sayable, but through a means §7 must carry. The means is a pure helper over
                  the UNCHANGED `Gabbro.Body`, so it costs the shared semantics nothing --
                  which is exactly what separates it from the next line.
    EXTENSION  -- sayable only if the SHARED `Value` grows a form. §8 forbids growing it
                  here, so the row carries `notSayable` and the price is named.
    NOT        -- no `Prop` over one or two states expresses it, and no extension of `Value`
                  would change that. The reason stands at the row.
-/
module

public import gabbrov.V1.Teil1
public import gabbrov.V1.Teil2
