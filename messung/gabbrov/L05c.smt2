; L05c -- the SHARPER question the first two runs raised, and the one this lane did not
; set out to ask.
;
; Run 1 refuted `unlink maintains cdt_wohlgeformt`; run 2 showed the only premise that
; repairs it is `s = WURZEL`, which contradicts what `unlink` is for. That points at the
; invariant rather than the body, so:
;
;     `cdt_wohlgeformt` = forall s in slots of c : c.slots[s] reaches WURZEL via parent
;
; quantifies over the WHOLE table -- `slots of c`, not "the used slots of c". A slot that is
; not in the tree has `parent == None` and is not `WURZEL`, and `reachesIn` returns `false`
; on `.absent` (`V1.lean`, the `| _ => false` arm).
;
; THE QUESTION: can the invariant hold at the same time as a single detached slot?
;   unsat -> the invariant FORBIDS a free slot, and `release_slot` (`F01.gab`:233) leaves
;            exactly one behind. Then no removal path in F1 can restore it.
;   sat   -> the reading above is wrong and this run says so.
;
; Bound 6 is enough: it is a question about ONE slot, not about a chain.

(set-option :timeout 60000)
(set-option :produce-models true)
(declare-datatypes ((Opt 0)) (((none) (some (idx Int)))))
(declare-const N Int)
(declare-const WURZEL Int)
(assert (= WURZEL 0))
(assert (> N 1))
(declare-fun parent0 (Int) Opt)
(assert (forall ((x Int)) (=> (and (>= x 0) (< x N))
  (=> ((_ is some) (parent0 x)) (and (>= (idx (parent0 x)) 0) (< (idx (parent0 x)) N))))))

; `cdt_wohlgeformt`, unrolled to depth 6.
(define-fun r6 ((x Int)) Bool
  (ite (= x WURZEL) true (ite ((_ is some) (parent0 x))
  (ite (= (idx (parent0 x)) WURZEL) true (ite ((_ is some) (parent0 (idx (parent0 x))))
  (ite (= (idx (parent0 (idx (parent0 x)))) WURZEL) true false) false)) false)))
(assert (forall ((x Int)) (=> (and (>= x 0) (< x N)) (r6 x))))

; And ONE detached slot -- the state `release_slot` leaves behind.
(declare-const u Int)
(assert (and (>= u 0) (< u N)))
(assert (not (= u WURZEL)))
(assert ((_ is none) (parent0 u)))

(check-sat)
(get-model)
