/-
  File:      Grammatik/ArenaZucker.lean
  Subject:   **`alloc` AND `reset` GET A FORM IN THE SPECIFICATION** -- as SUGAR over the
             existing `Stmt`/`Block`, not as two new constructors.

  THE FINDING THIS ANSWERS (`messung/muse/OPUS-BERICHT-GRAMMATIK-EMIT.md` sections 2.2 and
  5.3): the Rust checker accepts `let i = alloc A (v) [else …];` and `reset A;` with zero
  diagnostics, `emit.rs` writes C for them, that C compiles -- and `Syntax.lean` had no
  `Stmt` constructor for either. `SYNTAX.md`:934 said so verbatim (*"no `Stmt` constructor
  -- the generation is checker state"*), and `Arena.lean` carried the arithmetic of the
  arena with no tie to the syntax at all.

  WHY SUGAR AND NOT TWO CONSTRUCTORS. `Stmt` has 26 constructors and every exhaustive match
  over it is a proof obligation of the goal theorem: 30 Lean files carry 252 occurrences of
  the single leaf constructor `retGrund`, and 79 files name `assignSlot`. Two new
  constructors would be two new arms in the semantics, the machine, race freedom, deadlock,
  progress, cost, the invariant families and the non-interference layer -- and the arena
  would additionally be a NEW CARRIER, so `World` would grow a field and every frame lemma
  in the tree would move. **Sugar costs none of that**: an arena program is an ordinary term
  of the existing `Block`, so `theorem gabbro_ziel` covers it with no new case and no
  re-proof. That is the whole point of `Zucker.lean`, and the arena fits it exactly.

  THE SHAPE. An `arena A capacity lo .. hi of T` is, in the specification, a pair already in
  the language:

    * a table `tab` with `count tab = hi` and one field `feld : T` -- the slots;
    * a global `zaehl` of type `int 0 hi` -- the `used` counter.

  That is also literally what the emitter writes: `A_arena_speicher.buf[…]` beside
  `A_arena_speicher.used`. Then

    `reset A;`                    =  `zaehl = 0;`                  (`Stmt.assignGlob`)
    `let i = alloc A (v) else B;` =  narrow `zaehl` into `0 ..< hi`, else `B`;
                                     `tab.slots[i].feld = v;`  `zaehl = i + 1;`
                                                                   (`Block.narrow` +
                                                                    `Stmt.assignSlot` +
                                                                    `Stmt.assignGlob`)

  `Block.narrow` is the exact form of the emitted guard: the value fits the range, or the
  `else` branch runs and does not fall through. **The reservation `lo` is NOT in the Lean
  form and must not be**: it is a STATIC count the Rust checker keeps (`N212`), and its
  meaning here is `arenaAlloc_unter_schranke` below -- while the counter stands under the
  hard bound, the `else` branch is not entered, so the surface form that omits it is sound
  for any choice of branch. That is the syntactic half of `Arena.alloc_innerhalb_reserve`.

  WHAT IS STILL OPEN AND IS BOOKED, NOT HIDDEN (`dokumente/TODO.md` O14): the Rust exporter
  `lean_g.rs` refuses an arena declaration (`LG001`) instead of lowering it to this
  table-plus-global pair, so no arena program closes a translation-validation chain YET.
  The form now exists; the export does not.

  Core direction: imports `Zucker` (for `Expr.weaken`) and `Arena` (for the bridge).
-/
module

public import Grammatik.Bausteine.Arena.ArenaZucker.Teil1
public import Grammatik.Bausteine.Arena.ArenaZucker.Teil2
public import Grammatik.Bausteine.Arena.ArenaZucker.Teil3
