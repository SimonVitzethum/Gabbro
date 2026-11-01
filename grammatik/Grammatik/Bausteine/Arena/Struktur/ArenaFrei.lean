/-
  File:      Grammatik/ArenaFrei.lean
  Subject:   `free A[i];` AND THE FREE LIST AS A FORM OF MACHINE G, with the invariant of the list
             preserved by `free` and by `alloc` from the list (PLAN-DYNAMIC.md section 8a, phase 1).

  THE SHAPE (sugar, as `ArenaZucker.lean` and `ArenaDyn.lean`: no new `Stmt` constructor, `World`
  does not grow). A dynamic arena with slot release is, in the specification, the dynamic arena
  of `ArenaDyn.lean` plus

    * a global `kopf` of type `int 0 count` -- the head of the free list; the value `count` means
      EMPTY (an index never reaches it);
    * a field `nxt` of the SAME table of type `int 0 count` -- the link of a freed slot.

  The runtime writes the link into the freed payload (`LLVM-BACKEND.md` section 4); the model keeps
  it as its own field, so a freed slot's payload is untouched. The two readings agree on everything
  a program can observe, because the static death of the name (`N586`) means no program reads a
  freed slot's payload.

    `free A[i];`   =  `nxt[i] = kopf;  kopf = i;`
    `alloc` from the list  =  `i = kopf; kopf = nxt[i]; slot[i] = v`   (when `kopf < count`)

  THE INVARIANT. `FreiOk`: the chain from `kopf` along `nxt` ends at `count`, visits each slot at most
  once, and only slots below the arena's used counter. It is a PREDICATE over a world, not a new
  carrier. Two preservation theorems, both on the executed form:

    * `frei_erhaelt`  -- `free` of a slot that is live, below the used counter and not already on the
      list leaves `FreiOk` true. The hypothesis is exactly what the checker's `N586` establishes
      statically (single release, no release of a foreign slot); without it the claim is false
      (`doppelt_bricht`), which is the model's reading of why the refusal exists.
    * `abheben_erhaelt` -- taking the head off the list leaves `FreiOk` true.

  Memory safety does not depend on the invariant (every access is bounds-checked by the index type);
  what it carries is the LOGICAL correctness of reuse: no slot is handed out twice while live.
-/
module

public import Grammatik.Bausteine.Arena.Struktur.ArenaFrei.Teil1
public import Grammatik.Bausteine.Arena.Struktur.ArenaFrei.Teil2
