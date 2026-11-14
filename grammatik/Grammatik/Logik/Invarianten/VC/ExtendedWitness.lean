module

public import Grammatik.Logik.Invarianten.VC.Extended
public import Grammatik.Logik.Invarianten.VC.Witness

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Gabbro.Grammatik.Invarianten.VC.ExtendedWitness

open Frag Elim Elim.Korrekt Modell
open Witness

/-- `while len < cap bounded 2` is the canonical retry of the negated test. -/
def boundedWriter : Endblock declaration contract false [] [] :=
  .cons (.retry 2 (.not guard) (.cons increment .nil) .nil)
    (.ret .empty (List.Perm.refl _))

/-- The same bounded loop without the cap guard can break len <= cap. -/
def overflowingWriter : Endblock declaration contract false [] [] :=
  .cons (.retry 2 .fls (.cons increment .nil) .nil)
    (.ret .empty (List.Perm.refl _))

/-- Snapshot equality matters: havocing the temporary independently of len
    would reject this writer. The assignment writes exactly the snapshot. -/
def temporaryWriter : Endblock declaration contract false [] [] :=
  .bind lengthValue
    (.cons (.assignGlob false (.var .here) rfl (access false))
      (.ret .empty (List.Perm.refl _)))

/-- A mutable temporary is updated before the store, under the same cap guard. -/
def mutableWriter : Endblock declaration contract false [] [] :=
  .bind lengthValue
    (.cons (.ite (.lt (.var .here) (.glob true (access true)))
      (.cons (.assignVar .here (.eng (.add (.var .here) (.lit 1)) 0 10 (.var .here)))
        (.cons (.assignGlob false (.var .here) rfl (access false)) .nil)) .nil)
      (.ret .empty (List.Perm.refl _)))

/-- Traverse also consumes its generated index and shrinks it on all exits. -/
def traverseWriter : Endblock declaration contract false [] [] :=
  .cons (.traverse () .tru
    (.cons (.ite guard (.cons increment .nil) .nil) .nil))
    (.ret .empty (List.Perm.refl _))

def noLockFacts (lock : declaration.Lock) :
    Except Frag.Refusal (LockFormula (SperrInv.leer declaration) lock) := nomatch lock

def compile (code : Endblock declaration contract false [] []) :
    Except Frag.Refusal (EndCondition program noFacts (SperrInv.leer declaration) code .nil post) :=
  extendedEnd program noFacts noLockFacts 16 none 64 code .nil post

def boundedCompiled : EndCondition program noFacts (SperrInv.leer declaration) boundedWriter .nil post :=
  (compile boundedWriter).toOption.get (by decide)

def overflowingCompiled : EndCondition program noFacts (SperrInv.leer declaration) overflowingWriter .nil post :=
  (compile overflowingWriter).toOption.get (by decide)

def temporaryCompiled : EndCondition program noFacts (SperrInv.leer declaration) temporaryWriter .nil post :=
  (compile temporaryWriter).toOption.get (by decide)

def mutableCompiled : EndCondition program noFacts (SperrInv.leer declaration) mutableWriter .nil post :=
  (compile mutableWriter).toOption.get (by decide)

def traverseCompiled : EndCondition program noFacts (SperrInv.leer declaration) traverseWriter .nil post :=
  (compile traverseWriter).toOption.get (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem bounded_decided_zeuge :
    decideB (Extended.writerVC boundedCompiled entry .tru) = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem overflow_decided_zeuge :
    decideB (Extended.writerVC overflowingCompiled entry .tru) = false := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem temporary_decided_zeuge :
    decideB (Extended.writerVC temporaryCompiled entry .tru) = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem mutable_decided_zeuge :
    decideB (Extended.writerVC mutableCompiled entry .tru) = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem traverse_decided_zeuge :
    decideB (Extended.writerVC traverseCompiled entry .tru) = true := by decide

/-- With a checked same-fragment invariant, a bound beyond the unrolling
    allowance is handled inductively rather than expanded into one hundred passes. -/
def inductiveWriter : Endblock declaration contract false [] [] :=
  .cons (.retry 100 (.not guard) (.cons increment .nil) .nil)
    (.ret .empty (List.Perm.refl _))

def inductiveCompiled : EndCondition program noFacts (SperrInv.leer declaration) inductiveWriter .nil post :=
  (extendedEnd program noFacts noLockFacts 16 (some post) 64 inductiveWriter .nil post).toOption.get (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem inductive_decided_zeuge :
    decideB (Extended.writerVC inductiveCompiled entry .tru) = true := by decide

/-- The false decision has both an extracted arithmetic assignment and an
    actual typed G execution that destroys the invariant. -/
theorem overflow_assignment_zeuge :
    ∃ values : Assignment (Observation declaration),
      Extended.writerCounterexample overflowingCompiled entry .tru = some values :=
  Extended.writerCounterexample_complete overflowingCompiled entry .tru overflow_decided_zeuge

theorem overflow_execution_zeuge :
    (match execEnd oracle 0 calls overflowingWriter counterexampleWorld .nil with
      | .zurueck next _ => eval next invariant next .nil
      | _ => true) = false := by decide

theorem temporary_execution_zeuge :
    (match execEnd oracle 0 calls temporaryWriter counterexampleWorld .nil with
      | .zurueck next _ => eval next invariant next .nil
      | _ => false) = true := by decide

/-- An over-budget loop is a definite refusal, not an unchecked fallback. -/
theorem over_budget_refused_zeuge :
    (extendedEnd program noFacts noLockFacts 0 none 64 boundedWriter .nil post).toOption.isNone = true := by
  decide

end Gabbro.Grammatik.Invarianten.VC.ExtendedWitness
