module
public import Stage0.Senke.Anweisung.Fast.Code
public import Stage0.Senke.Anweisung.Faelle.Hilfen
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR

namespace CodeCache

theorem eq_of_value_eq {a b : CodeCache} (h : a.value = b.value) : a = b :=
  (ofPair_value a).symm.trans ((congrArg ofPair h).trans (ofPair_value b))

/-- Short newly emitted chunks are counted once; recursive continuations supply
    their cached sizes. The complete continuation is never passed to `length`. -/
def join (pre : List II) (middle : CodeCache) (suffix : List II)
    (tail : CodeCache) (top : Nat) : CodeCache :=
  { value := (pre ++ middle.value.1 ++ suffix ++ tail.value.1, top)
    size := pre.length + middle.size + suffix.length + tail.size
    correct := (by
      rw [middle.correct, tail.correct]
      simp only [List.length_append]) }

theorem join_ofPair (pre : List II) (middle : List II × Nat) (suffix : List II)
    (tail : List II × Nat) (top : Nat) :
    join pre (ofPair middle) suffix (ofPair tail) top =
      ofPair (pre ++ middle.1 ++ suffix ++ tail.1, top) := by
  apply eq_of_value_eq
  rfl

def narrow (d : Nat) (lo hi low high : Int) (ce : List II)
    (cx cr : CodeCache) (top : Nat) : CodeCache :=
  join (ce ++ wideExtendC (extSigned lo) (integerWords lo hi) (narrowWords lo hi low high) d ++
    wideOutC (narrowWords lo hi low high) d low high ++
    [ci 19 (d + narrowWords lo hi low high + 3) (16 * (cx.size + 2)) 0]) cx
    [ci 18 (16 * (cr.size + 1)) 0 0] cr top

theorem narrow_ofPair (d : Nat) (lo hi low high : Int) (ce : List II)
    (cx cr : List II × Nat) (top : Nat) :
    narrow d lo hi low high ce (ofPair cx) (ofPair cr) top =
      ofPair (narrowC d lo hi low high ce cx.1 cr.1, top) := by
  apply eq_of_value_eq
  simp only [narrow, join, ofPair, narrowC, List.append_assoc]

def callElse {D : Deklaration} (signature : Signatur D.Tab D.Glob D.Lock D.Marke)
    (s : Nat) (cc : List II) (cr ce : CodeCache) (top : Nat) : CodeCache :=
  join (cc ++ receiveC (D := D) signature s ++
    [ci 19 (s + FB + contextWords signature.params + returnWords signature.erg signature.gruende)
      (16 * (cr.size + 2)) 0]) cr [ci 18 (16 * (ce.size + 1)) 0 0] ce top

theorem callElse_ofPair {D : Deklaration}
    (signature : Signatur D.Tab D.Glob D.Lock D.Marke) (s : Nat) (cc : List II)
    (cr ce : List II × Nat) (top : Nat) :
    callElse (D := D) signature s cc (ofPair cr) (ofPair ce) top =
      ofPair (elseC (D := D) signature s cc cr.1 ce.1, top) := by
  apply eq_of_value_eq
  simp only [callElse, join, ofPair, elseC, List.append_assoc]

end CodeCache
end Gabbro.Stage0.Senke
