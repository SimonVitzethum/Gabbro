(set-option :produce-models true)
(set-option :timeout 60000)

; ===========================================================================
;  FOLLOW-UP (b) -- is `cdt_wohlgeformt` SATISFIABLE AT ALL over a table that
;  has one slot with `parent == None` that is not the root?
;
;  This is NOT a VC with a negated goal.  It is a plain satisfiability
;  question, so the reading is the OTHER way round:
;      sat   => yes, such a table exists; the invariant is livable
;      unsat => NO such table exists; `cdt_wohlgeformt` is INCOMPATIBLE with
;               a single non-root slot whose parent field is absent
;
;  Why this is the question that matters.  `cdt_wohlgeformt` quantifies
;      forall s in slots of c
;  -- over the WHOLE table, with no `used` guard anywhere in the source.  And
;  `release_slot` (same fragment) sets `used = false` and NEVER clears
;  `parent`; conversely `unlink` clears `parent` and never clears `used`.  So
;  a free slot in this table is a slot that is still in the quantifier's
;  domain.  `reachesIn` returns FALSE the moment it meets an `absent` parent
;  on a slot that is not already the target -- there is no "stop, this slot is
;  not in the tree" case in the helper.
;
;  N = 4, quantifier-free, therefore DECIDABLE.
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
(define-fun N () Int 4)

; `cdt_wohlgeformt(c) = forall s in slots of c : c.slots[s] reaches WURZEL via parent`
; -- the domain is the whole table, exactly as written.
(define-fun cdtWf ((w World)) Bool
  (and (rch6 w 0 ROOT) (rch6 w 1 ROOT) (rch6 w 2 ROOT) (rch6 w 3 ROOT)))

(define-fun rangeok ((w World) (i Int) (f Fld)) Bool
  (let ((v (select w (mkslot i f))))
    (or ((_ is vabsent) v)
        (and ((_ is vpresent) v) (<= 0 (pidx v)) (< (pidx v) N)))))

(declare-const w World)
(declare-const u Int)

(assert (and (rangeok w 0 F_parent) (rangeok w 1 F_parent)
             (rangeok w 2 F_parent) (rangeok w 3 F_parent)))

; ONE slot u, a slot of this table, not the root, with `parent == None`.
(assert (and (<= 0 u) (< u N)))
(assert (not (= u ROOT)))
(assert (= (par w u) vabsent))

; ... and the invariant holds at the same time.
(assert (cdtWf w))

(check-sat)
(get-model)
