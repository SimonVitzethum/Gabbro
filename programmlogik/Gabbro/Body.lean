/-
  File:    Gabbro/Body.lean
  Subject: What a Gabbro BODY means -- the statement descent as a state transition.

  WHY THIS FILE IS NOT IN `passlogik/`
    `passlogik/` formalises the CHECKER -- range lattices, effect hulls, rank order. Those
    are statements about PASSES. This one is a statement about PROGRAMS, and the two must not
    live in one namespace: a theorem about a pass read as a theorem about a program is a
    different claim with different consequences.

  WHAT IT CLOSES
    `passlogik/README.md` books the same missing item four times (`B1`, `L1`, `P2`, `R1`):

        "The STATEMENT DESCENT -- what a body does statement by statement -- stands in NONE
         of the seven files."

    And `messung/P6.md` measures what hangs on it: of 62 obligations, `refinement.rs` refuses
    seventeen with `body-effect`, because there is no meaning of a Gabbro body -- ten `N`,
    six `E`, and the one `R`.

  WHAT IS MODELLED
    A WORLD as an assignment of places (a table's slot field, a `static`) to values, a local
    binding for `let` names, and the descent over the SEQUENTIAL CORE: `let`, assignment,
    `if`, `match` over `option`, `return`.

    **And since 2026-09-07 the composition** -- everything that was a person's plumbing
    until then, and is the generator's now (`crates/gabbro-check/src/lean.rs`):
      * a CALL over the callee's contract (§4.1: `Contract`, `Frame`), with the callee's
        `requires` as the stuck-condition of the call;
      * a LOOP as an anonymous routine with a rule (`LoopRule`), the exits `next`/`leave`,
        and a `return` inside one desugared to a flagged `leave`;
      * the bounded QUANTIFIER over a table's index domain and the parent CHAIN
        (`forallSlots`, `existsSlots`, `reaches`, `chainFrom`) -- as expressions, so that a
        contract may demand them;
      * the error propagation (`bindCallElse`, `Value.reason`), `tagged` values
        (`Value.tagged`, `onTag`), `wrapping` stores (`wrapTo`), `narrow` (an `ite`);
      * the well-typed world as ONE typing per unit (`WF`, §4.0), and the two theorems that
        make it free (`WF_store`, `WF_int`);
      * and the wiring: `contract_of_duty`, `looprule_of_body` (§5.1) -- the induction over
        the call graph and over the passes, done once here and instantiated per unit.

  WHAT THE PLUMBING ALREADY CARRIES -- and what this model therefore need not build
    This is the whole reason the file is short. Every line names the theorem that allows it:

      overflow      Integers are `Int`, unbounded.
                    -> `Passlogik.Bereich.passt_dann_kein_ueberlauf` (`M104`)
      shift width   A shift COUNT at or above the operand's width is undefined in C, and
                    there is no width here. It is booked as an overflow like every other:
                    `typen::schiebe_links`/`schiebe_rechts` mark `b.max >= a.breite`.
                    -> `M104`.  **This booking is void for a `wrapping` operand** -- see
                    §3.2 and DOES NOT COVER below.
      zero divisor  A denominator whose range does not exclude zero is refused.
                    -> `M102`.  The model does NOT lean on it: it gets stuck at zero, so
                    the premise stays visible in every proof that goes through a `/`.
      frame         The frame IS the declared `effects` list; a place outside it survives.
                    -> `Passlogik.Wirkung.huelle_deckt` (`E005`/`E008`)
      alias         Two distinct `Place`s are distinct places, full stop.
                    -> the alias passes; `A1` closed 2026-08-24 with `R007`
      termination   The core has no loop -- and the loop forms carry their measure.
                    -> `K008`/`K009`, `Bereich.keine_unendliche_verengung`
      races         Sequential reading is sound; `Held(L)` holds at the body's entry.
                    -> `H005`/`H006`/`H012`/`H016`

    **Hence there is NO heap model here, NO separation logic, NO pointers and NO
    concurrency.** A state is a map from places to values. Whoever reads this file without
    reading the plumbing alongside will take the model for naive -- it is the cashed-out form
    of this folder's thesis.

  ASSUMED RATHER THAN PROVED
    (U1) That the EMITTER (`crates/gabbro-check/src/lean.rs`) translates a Gabbro body into a
         `Stmt` datum correctly does not stand here. That is the same seam the other seven
         files have -- only this one is drawn mechanically and is therefore mutable.
         `instrumente/pruefe-lean-beweis.sh` drives it in both directions.
    (U2) The WELL-FORMED state -- that a slot field carries a value of its declared shape --
         is a hypothesis and not a consequence. The emitter writes it per unit out of the
         `table` declaration; it stands visibly in the theory.
    (U3) Two distinct carrier names denote two distinct objects. That is the alias statement,
         and the alias passes carry it -- no line here does.

  DOES NOT PROVE
    That a body terminates (the core has no loop -- there is nothing to show), that it is
    overflow-free (`M104`), or that it respects its frame (`E005`).

  DOES NOT COVER, and the names are here rather than in a commit message
    (N1) A bit operation or a shift with a NEGATIVE operand. The C answer is read off a
         two's complement of a width this file does not have -- and for `>>` it is
         *implementation-defined* even then, so `M104` never fires on it either. `binop`
         gets stuck; §3.2 says so as a theorem.
    (N2) A shift whose left operand has a `wrapping` type. `M1` suppresses the overflow
         there, so the shift-width booking above does not apply -- and a count at or above
         the width is undefined in C even on an unsigned operand. A `wrapping` FIELD is
         already refused by the emitter (`no-shape-for-field`); a `wrapping` LOCAL is not,
         and that hole is older than the shifts: `+` on one stands here unbooked too.
    (N3) That a DECLARED range is a hypothesis. `u32` says `0 ≤ x` and `u16 in 1 .. Q` says
         `x ≠ 0`, and neither reaches this model: the emitter writes shapes (`isInt`), not
         ranges. So a proof through a mask or a division must get the guard from the body
         or from a `requires` -- which is where `raeumen`-style bodies get it, and where
         `falte(s : u32)` does not.
-/

module

public import Gabbro.Body.Teil1
public import Gabbro.Body.Teil2
public import Gabbro.Body.Teil3
public import Gabbro.Body.Teil4
public import Gabbro.Body.Teil5
public import Gabbro.Body.Teil6
public import Gabbro.Body.Teil7
public import Gabbro.Body.Teil8
