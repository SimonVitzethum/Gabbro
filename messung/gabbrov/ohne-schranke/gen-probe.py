#!/usr/bin/env python3
"""The control that decides whether the rank file above says anything: is the PREMISE alone
satisfiable at this N? An unsatisfiable premise makes every VC `unsat` and every obligation
`passed` -- the exact shape `GABBROV.md` §5 calls vacuity, one level down."""
import sys
N = sys.argv[1]
print(f"""(set-option :timeout 60000)
(set-option :produce-models true)
(declare-datatypes ((Opt 0)) (((none) (some (idx Int)))))
(declare-const N Int) (declare-const WURZEL Int)
(assert (= WURZEL 0)) (assert (= N {N}))
(declare-fun parent0 (Int) Opt) (declare-fun rank0 (Int) Int)
(assert (forall ((x Int)) (=> (and (>= x 0) (< x N))
  (=> ((_ is some) (parent0 x)) (and (>= (idx (parent0 x)) 0) (< (idx (parent0 x)) N))))))
(assert (= (rank0 WURZEL) 0))
(assert (forall ((x Int)) (=> (and (>= x 0) (< x N) (distinct x WURZEL))
  (and ((_ is some) (parent0 x)) (>= (rank0 x) 1) (< (rank0 x) N)
       (= (rank0 x) (+ 1 (rank0 (idx (parent0 x)))))))))
(check-sat)
(get-model)""")
