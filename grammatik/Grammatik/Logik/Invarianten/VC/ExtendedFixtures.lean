module

public import Grammatik.Logik.Invarianten.VC.Extended
public import Grammatik.Logik.Invarianten.VC.Witness
public import Grammatik.Logik.Vertraege.Pruefer.Program
import all Batteries.Data.Except

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 400000

namespace Gabbro.Grammatik.Invarianten.VC.ExtendedWitness

open Frag Elim Elim.Korrekt Modell
open Gabbro.Grammatik.Invarianten.VC.Witness

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
  (compile boundedWriter).toOption.get (by decide +kernel)

def overflowingCompiled : EndCondition program noFacts (SperrInv.leer declaration) overflowingWriter .nil post :=
  (compile overflowingWriter).toOption.get (by decide +kernel)

def temporaryCompiled : EndCondition program noFacts (SperrInv.leer declaration) temporaryWriter .nil post :=
  (compile temporaryWriter).toOption.get (by decide +kernel)

def mutableCompiled : EndCondition program noFacts (SperrInv.leer declaration) mutableWriter .nil post :=
  (compile mutableWriter).toOption.get (by decide +kernel)

def traverseCompiled : EndCondition program noFacts (SperrInv.leer declaration) traverseWriter .nil post :=
  (compile traverseWriter).toOption.get (by decide +kernel)

/-- With a checked same-fragment invariant, a bound beyond the unrolling
    allowance is handled inductively rather than expanded into one hundred passes. -/
def inductiveWriter : Endblock declaration contract false [] [] :=
  .cons (.retry 100 (.not guard) (.cons increment .nil) .nil)
    (.ret .empty (List.Perm.refl _))

def inductiveCompiled : EndCondition program noFacts (SperrInv.leer declaration) inductiveWriter .nil post :=
  (extendedEnd program noFacts noLockFacts 16 (some post) 64 inductiveWriter .nil post).toOption.get (by decide +kernel)

/-- The Boolean snapshot must retain its relation to the guard: choosing an
    unrelated true flag at len = cap would make the increment fail the post. -/
def booleanWriter : Endblock declaration contract false [] [] :=
  .bind guard
    (.cons (.ite (.var .here)
      (.cons (.assignGlob false
        (.eng (.add (.glob false (access false)) (.lit 1)) 0 10
          (.glob false (access false))) rfl (access false)) .nil) .nil)
      (.ret .empty (List.Perm.refl _)))

def bumpedLength : Expr declaration [] [] (.int 0 10) :=
  .eng (.add lengthValue (.lit 1)) 0 10 lengthValue

/-- Both arms are present in the source. Reversing the guard makes the writer
    increment at len = cap, where the declared invariant is false afterwards. -/
def conditionalWriter (preserves : Bool) : Endblock declaration contract false [] [] :=
  .bind (.wenn guard (if preserves then bumpedLength else lengthValue)
      (if preserves then lengthValue else bumpedLength))
    (.cons (.assignGlob false (.var .here) rfl (access false))
      (.ret .empty (List.Perm.refl _)))

def booleanCompiled : EndCondition program noFacts (SperrInv.leer declaration)
    booleanWriter .nil post := (compile booleanWriter).toOption.get (by decide +kernel)

def conditionalCompiled (preserves : Bool) : EndCondition program noFacts
    (SperrInv.leer declaration) (conditionalWriter preserves) .nil post :=
  (compile (conditionalWriter preserves)).toOption.get (by cases preserves <;> decide +kernel)

/-- The strict traversal rule must preserve the declared invariant and must
    reject the model's annotation logic stop, even with an empty body. -/
def traversalProgram (annotationHolds : Bool) : Programm declaration :=
  { program with
    rumpf := fun _ =>
      .cons (.traverse () (if annotationHolds then .tru else .fls) .nil)
        (.ret .empty (List.Perm.refl _)) }

end Gabbro.Grammatik.Invarianten.VC.ExtendedWitness
