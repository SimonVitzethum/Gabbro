/-
  P22 probe, LESESTELLE gap #18 `regbind` (G-NAME).
  Rule: a register binding pair `name : value` (regs in and regs out of
  entry and entrust, asm operands) never stands alone; it arrives as a
  positional argument inside the foreign-body call. The tree carries the
  argument list, never the pair.
  Witness: `Block.bindAxiom` takes `Args` over the declared parameter types;
  the `#check` output below is the evidence.
  Check with: LEAN_PATH=grammatik/.lake/build/lib/lean lean <this file>.
-/
import Grammatik.Syntax

open Gabbro.Grammatik

#check @Block.bindAxiom
#check @Args.cons
