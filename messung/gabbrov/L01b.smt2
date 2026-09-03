; L01b -- SECOND RUN, with the ONE premise the language cannot state.
; L01 -- "a root has no predecessor", the table invariant `wurzel_ohne_vorgaenger`
; of `messung/fragmente/F01.gab`:177-179, held against the body of `unlink` (:211-228).
;
; The verification condition, and it is the one a table invariant OWES:
;
;     invariant holds before  AND  the body ran  ==>  invariant holds after
;
; Everything the fragment DECLARES is a premise. Nothing else is -- which is the whole
; point of the run: the premises available to a checker are the ones the language can
; state, and `F01.gab` says in its own comment which ones it cannot («B14»).
;
; Encoding: an `option index into CapSpace` is a two-form datatype, exactly `Value`'s
; `absent` / `present`. The four slot fields are uninterpreted functions over the index.
; The post state is spelled out as a nest of `ite`s in the body's OWN ORDER -- the later
; write wins, which is what makes the `x = s` arm outermost.

(set-option :timeout 60000)
(set-option :produce-models true)
(declare-datatypes ((Opt 0)) (((none) (some (idx Int)))))

(declare-const N Int)                     ; the table's `count NSLOTS`
(declare-const s Int)                     ; the slot being unlinked
(assert (> N 1))
(assert (and (>= s 0) (< s N)))

(declare-fun parent0 (Int) Opt)
(declare-fun prev0   (Int) Opt)
(declare-fun next0   (Int) Opt)
(declare-fun child0  (Int) Opt)

; M1 carries this and GabbroV may assume it: an `option index into T` that is `present`
; points into T. Plumbing, not logic -- `GABBROV.md` §9 point 4.
(assert (forall ((x Int)) (=> (and (>= x 0) (< x N))
  (and (=> ((_ is some) (parent0 x)) (and (>= (idx (parent0 x)) 0) (< (idx (parent0 x)) N)))
       (=> ((_ is some) (prev0   x)) (and (>= (idx (prev0   x)) 0) (< (idx (prev0   x)) N)))
       (=> ((_ is some) (next0   x)) (and (>= (idx (next0   x)) 0) (< (idx (next0   x)) N)))
       (=> ((_ is some) (child0  x)) (and (>= (idx (child0  x)) 0) (< (idx (child0  x)) N)))))))

; THE PREMISE: the invariant holds before.
(assert (forall ((x Int)) (=> (and (>= x 0) (< x N))
  (=> ((_ is none) (parent0 x)) ((_ is none) (prev0 x))))))

; The body of `unlink`, in order. The last write to a place wins, so `x = s` is outermost.
(define-fun prev1 ((x Int)) Opt
  (ite (= x s) none
    (ite (and ((_ is some) (next0 s)) (= x (idx (next0 s)))) (prev0 s)
      (prev0 x))))
(define-fun next1 ((x Int)) Opt
  (ite (= x s) none
    (ite (and ((_ is some) (prev0 s)) (= x (idx (prev0 s)))) (next0 s)
      (next0 x))))
(define-fun parent1 ((x Int)) Opt
  (ite (= x s) none (parent0 x)))
(define-fun child1 ((x Int)) Opt
  (ite (= x s) none
    (ite (and ((_ is none) (prev0 s)) ((_ is some) (parent0 s)) (= x (idx (parent0 s))))
         (next0 s)
      (child0 x))))


; ADDED for the second run: `L02`, the MUTUAL sibling chain -- `slots[s.next].prev == s`
; and its mirror. `F01.gab`:181-183 says in its own comment that `pred` CANNOT state this:
; «B14», the resolution of an `option index into` inside a predicate. So this premise is
; available to a Lean specification and NOT to a Gabbro `table … invariant`.
(assert (forall ((x Int)) (=> (and (>= x 0) (< x N))
  (and (=> ((_ is some) (next0 x)) (= (prev0 (idx (next0 x))) (some x)))
       (=> ((_ is some) (prev0 x)) (= (next0 (idx (prev0 x))) (some x)))))))

; THE GOAL, negated: is there a state in which the invariant FAILS afterwards?
;   unsat  -> the obligation holds     (GabbroV: passed)
;   sat    -> counterexample           (GabbroV: refuted)
;   unknown-> the solver does not get through (GabbroV: undecided)
(assert (not (forall ((x Int)) (=> (and (>= x 0) (< x N))
  (=> ((_ is none) (parent1 x)) ((_ is none) (prev1 x)))))))

(check-sat)
(get-model)
