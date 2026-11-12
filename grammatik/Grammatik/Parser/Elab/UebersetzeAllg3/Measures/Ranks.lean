/-
  Equal measure lengths on recursion cycles, checked through a rank certificate.

  `cycleLengths` is the specification: it asks `zykS` for every pair of functions, and each
  answer closes the call graph twice. The executable form computes the strongly connected
  components once (`components`, not trusted), checks that their numbers never rise along a
  call site and that the tuple length is a function of the number (`fastLengths`), and only
  falls back to the specification when that check fails. Both forms are equal.
-/
module
public import Grammatik.Parser.Elab.UebersetzeAllg3.Measures.Expression
public import Grammatik.Logik.Terminierung.RangZeugnis
@[expose] public section

namespace Gabbro.Grammatik.Parser.Measures
open Uebersetze UebersetzeAllg UebersetzeAllg2

instance (u : UProg) : DecidableEq (declOf u).Fn := inferInstanceAs (DecidableEq (Fin u.fns.length))

/-- Check equal tuple lengths on cycles using every function, including functions without clauses. -/
def cycleLengths (u : UProg) (P : Programm (declOf u)) (m : Mass (declOf u)) : Bool :=
  (List.finRange u.fns.length).all fun f => (List.finRange u.fns.length).all fun g =>
    !(zykS P (List.finRange u.fns.length) f g) || decide ((m f).length = (m g).length)

theorem cycleLengths_sound (u : UProg) (P : Programm (declOf u)) (m : Mass (declOf u))
    (checked : cycleLengths u P m = true) :
    ∀ f g, zykS P (List.finRange u.fns.length) f g = true → (m f).length = (m g).length := by
  intro f g cycle
  have hf := List.all_eq_true.mp checked f (List.mem_finRange f)
  have hg := List.all_eq_true.mp hf g (List.mem_finRange g)
  simpa only [cycle, Bool.not_true, Bool.false_or, decide_eq_true_eq] using hg

/-- The callees of every function by index, from one walk over its call sites. -/
def adjacency (u : UProg) (P : Programm (declOf u)) : Array (Array Nat) :=
  Array.ofFn (n := u.fns.length) fun f =>
    (stellenE (P.rumpf (f : (declOf u).Fn))).foldl (fun out s =>
      match s with
      | .ruf g => out.push (g : Fin u.fns.length).val
      | .ind k => (List.finRange u.fns.length).foldl
          (fun out g => if (declOf u).passt g k then out.push g.val else out) out
      | .sperre _ => out) #[]

/-- Component numbers of a graph over `0 .. n - 1`, callees first (Tarjan with an explicit
    stack). The result is a candidate only; `fastLengths` judges it. -/
def components (n : Nat) (adj : Array (Array Nat)) : Array Nat := Id.run do
  let mut idx : Array Nat := Array.replicate n n
  let mut low : Array Nat := Array.replicate n 0
  let mut on : Array Bool := Array.replicate n false
  let mut comp : Array Nat := Array.replicate n 0
  let mut stack : Array Nat := #[]
  let mut calls : Array (Nat × Nat) := #[]
  let mut next := 0
  let mut count := 0
  let steps := 2 * n + adj.foldl (fun s out => s + out.size) 0 + 1
  for root in [0:n] do
    if idx[root]! == n then
      idx := idx.set! root next
      low := low.set! root next
      next := next + 1
      stack := stack.push root
      on := on.set! root true
      calls := calls.push (root, 0)
      for _ in [0:steps] do
        match calls.back? with
        | none => break
        | some (v, i) =>
          let out := adj[v]!
          if i < out.size then
            let w := out[i]!
            calls := calls.set! (calls.size - 1) (v, i + 1)
            if idx[w]! == n then
              idx := idx.set! w next
              low := low.set! w next
              next := next + 1
              stack := stack.push w
              on := on.set! w true
              calls := calls.push (w, 0)
            else if on[w]! then
              low := low.set! v (min low[v]! idx[w]!)
          else
            calls := calls.pop
            if low[v]! == idx[v]! then
              for _ in [0:n] do
                match stack.back? with
                | none => break
                | some w =>
                  stack := stack.pop
                  on := on.set! w false
                  comp := comp.set! w count
                  if w == v then break
              count := count + 1
            match calls.back? with
            | some (p, _) => low := low.set! p (min low[p]! low[v]!)
            | none => pure ()
  return comp

/-- The candidate: a component number per function and a tuple length per number. -/
def certificate (u : UProg) (P : Programm (declOf u)) (m : Mass (declOf u)) :
    Array Nat × Array Nat :=
  let comp := components u.fns.length (adjacency u P)
  (comp, (List.finRange u.fns.length).foldl
    (fun lens f => lens.set! comp[f.val]! (m f).length) (Array.replicate u.fns.length 0))

/-- The numbers never rise along a call site, and the tuple length is a function of the number. -/
def fastLengths (u : UProg) (P : Programm (declOf u)) (m : Mass (declOf u))
    (comp lens : Array Nat) : Bool :=
  kantenFallen P (List.finRange u.fns.length) (fun f => comp[(f : Fin u.fns.length).val]!) &&
    (List.finRange u.fns.length).all fun f => decide ((m f).length = lens[comp[f.val]!]!)

/-- **Any candidate that passes proves the specification.** -/
theorem fastLengths_sound (u : UProg) (P : Programm (declOf u)) (m : Mass (declOf u))
    (comp lens : Array Nat) (checked : fastLengths u P m comp lens = true) :
    cycleLengths u P m = true := by
  obtain ⟨falls, table⟩ := (Bool.and_eq_true _ _).mp checked
  apply List.all_eq_true.mpr
  intro f _
  apply List.all_eq_true.mpr
  intro g _
  cases cycle : zykS P (List.finRange u.fns.length) f g with
  | false => rfl
  | true =>
    rw [Bool.not_true, Bool.false_or, decide_eq_true_eq]
    exact zykS_gleich (fun g => List.mem_finRange g) falls (fun f => (m f).length)
      (fun k => lens[k]!)
      (fun f => of_decide_eq_true (List.all_eq_true.mp table f (List.mem_finRange f))) cycle

/-- The executable form: the certificate first, the specification only when it fails. -/
def cycleLengthsSchnell (u : UProg) (P : Programm (declOf u)) (m : Mass (declOf u)) : Bool :=
  fastLengths u P m (certificate u P m).1 (certificate u P m).2 || cycleLengths u P m

/-- **The certificate changes no answer.** -/
@[csimp] theorem cycleLengths_eq_schnell : @cycleLengths = @cycleLengthsSchnell := by
  funext u P m
  unfold cycleLengthsSchnell
  cases fast : fastLengths u P m (certificate u P m).1 (certificate u P m).2 with
  | false => rfl
  | true => exact fastLengths_sound u P m _ _ fast

end Gabbro.Grammatik.Parser.Measures
