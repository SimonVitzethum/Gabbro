/-
  File:      Grammatik/Speichermodell/AtomarZeuge.lean
  Subject:   The checker side of racing atomics (Opus lane O25, 2026-09-26): the footprint
             component with the atomic exemption as a Bool (`fussWAB`), the checker Bool
             `AkzeptiertA` that uses it, its link to the memory theorem of `Atomar.lean`, and the
             witnesses. Standalone: `Zielsatz/Spec.lean` and `Akzeptiert` are unchanged.

  * `fussWAB_iff` -- the Bool decides `FussSA` (the footprint property with atomics exempt).
  * `akzeptiertA_of_akzeptiert` -- EMBEDDING: every program the goal's checker `Akzeptiert`
    accepts, `AkzeptiertA` accepts (old units keep their verdicts).
  * `schwach_ist_gA_akzeptiert` -- on a program `AkzeptiertA` accepts, with an admissible start:
    every step of W is a step of GA, and the memory it is presented is G's at every
    non-atomic carrier.
  * `w_sprache_akzeptiertA` -- the legs of `Ziel` that the LANGUAGE carries without the user's
    proof hold at every machine W reaches on such a program: the trace invariant
    (`speicherSicher`), lock exclusivity, no global deadlock, no wait cycle, the time bound.
    The contract legs are not here (they need the replay: OFFEN O25).
  * WITNESSES, on the noninterference fixture (`NIZeuge`: the globals `konfig`, `zaehler` are
    `atomic`, the tables `tabA`, `tabB` plain):
    - `n1_akzeptiertA` / `n1_nicht_sc_aber_ga` -- the FLAG: configuration 1 (`kern` publishes
      `konfig`, the tenants `hauptA`/`hauptB` read it with no lock) is refused by `Akzeptiert`
      and accepted by `AkzeptiertA`; on it W really takes the non-SC step of `w_nicht_sc`
      (`hauptA` reads the stale `konfig` after `kern`'s write) -- and that step is a GA step
      whose presented memory is G's at both plain tables. The leg `schwach` of `Ziel` (W takes
      only G's steps) is FALSE there (`schwach_nicht_trivial`): a goal over `AkzeptiertA`
      needs the leg in GA form (`messung/OPUS-O25-ATOMICS.md` §5).
    - `faltung_akzeptiertA` -- the PER-CORE FOLD (OFFEN O17, read half): `zaehlA` twice (a pool
      writing the atomic accumulator `zaehler`) and `zaehlB` (reads `zaehler`, the fold) --
      refused by `Akzeptiert` at the footprint component, accepted by `AkzeptiertA`.
    - `nutzlast_ohne_erwerb_abgelehnt` -- the REFUSAL: `hauptA` writes the PLAIN table `tabA`,
      `zaehlA` reads it with no lock (a payload read without any synchronisation) -- refused
      by `AkzeptiertA`, at its footprint component: the exemption is for atomics only.
-/
module

public import Grammatik.Speichermodell.Atomar.AtomarZeuge.Teil1
public import Grammatik.Speichermodell.Atomar.AtomarZeuge.Teil2
