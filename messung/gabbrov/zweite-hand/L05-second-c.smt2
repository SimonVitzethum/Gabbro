(set-option :produce-models true)
(set-option :timeout 60000)

; ===========================================================================
;  FOLLOW-UP (c) -- the same question as (b), but for an ARBITRARY table size.
;  (b) pinned N = 4 to stay quantifier-free.  Here N is a symbolic positive
;  integer and `forall s in slots of c` is a real universal quantifier, so an
;  `unsat` covers EVERY table size at once.
;
;  Plain satisfiability question again:
;      sat   => some table of some size carries the invariant with a free slot
;      unsat => no table of ANY size does
; ===========================================================================

(declare-datatype Value
  ((vint (ival Int)) (vbool (bval Bool)) (vabsent) (vpresent (pidx Int))))
(declare-datatype Fld
  ((F_used) (F_gen) (F_object) (F_rights) (F_badge)
   (F_parent) (F_first_child) (F_next_sibling) (F_prev_sibling)))
(declare-datatype Place ((mkslot (sidx Int) (sfld Fld))))
(define-sort World () (Array Place Value))
(define-fun par ((w World) (i Int)) Value (select w (mkslot i F_parent)))

(define-fun rch0 ((w World) (s Int) (t Int)) Bool (= s t))
(define-fun rch1 ((w World) (s Int) (t Int)) Bool
  (ite (= s t) true (let ((v (par w s))) (and ((_ is vpresent) v) (rch0 w (pidx v) t)))))
(define-fun rch2 ((w World) (s Int) (t Int)) Bool
  (ite (= s t) true (let ((v (par w s))) (and ((_ is vpresent) v) (rch1 w (pidx v) t)))))
(define-fun rch3 ((w World) (s Int) (t Int)) Bool
  (ite (= s t) true (let ((v (par w s))) (and ((_ is vpresent) v) (rch2 w (pidx v) t)))))
(define-fun rch4 ((w World) (s Int) (t Int)) Bool
  (ite (= s t) true (let ((v (par w s))) (and ((_ is vpresent) v) (rch3 w (pidx v) t)))))
(define-fun rch5 ((w World) (s Int) (t Int)) Bool
  (ite (= s t) true (let ((v (par w s))) (and ((_ is vpresent) v) (rch4 w (pidx v) t)))))
(define-fun rch6 ((w World) (s Int) (t Int)) Bool
  (ite (= s t) true (let ((v (par w s))) (and ((_ is vpresent) v) (rch5 w (pidx v) t)))))

(define-fun ROOT () Int 0)

(declare-const N Int)
(assert (> N 0))
(declare-const w World)
(declare-const u Int)

; `forall s in slots of c : c.slots[s] reaches WURZEL via parent`
(assert (forall ((s Int))
  (=> (and (<= 0 s) (< s N)) (rch6 w s ROOT))))

; one slot u of the table, not the root, with `parent == None`
(assert (and (<= 0 u) (< u N)))
(assert (not (= u ROOT)))
(assert (= (par w u) vabsent))

(check-sat)
(get-model)
