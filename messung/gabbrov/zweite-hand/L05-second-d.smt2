(set-option :produce-models true)
(set-option :timeout 60000)

; ===========================================================================
;  FOLLOW-UP (d) -- REPAIR CANDIDATE.
;
;  (b)/(c) showed `cdt_wohlgeformt` as written is unsatisfiable over any table
;  holding a non-root slot with `parent == None`.  The obvious repair is to
;  guard the quantifier with `used`:
;
;      forall s in slots of c : c.slots[s].used
;                               => c.slots[s] reaches WURZEL via parent
;
;  Question: does THAT make it satisfiable together with a freed slot?
;  Plain satisfiability again:  sat => the repair is livable.
;
;  The freed slot is modelled the way `release_slot` actually leaves it:
;      gen += 1;  used = false;  badge = 0;      -- and `parent` UNTOUCHED.
;  So we do NOT assert that a free slot's parent is absent; we let it be
;  either.  N = 4, quantifier-free.
; ===========================================================================

(declare-datatype Value
  ((vint (ival Int)) (vbool (bval Bool)) (vabsent) (vpresent (pidx Int))))
(declare-datatype Fld
  ((F_used) (F_gen) (F_object) (F_rights) (F_badge)
   (F_parent) (F_first_child) (F_next_sibling) (F_prev_sibling)))
(declare-datatype Place ((mkslot (sidx Int) (sfld Fld))))
(define-sort World () (Array Place Value))
(define-fun par ((w World) (i Int)) Value (select w (mkslot i F_parent)))
(define-fun usd ((w World) (i Int)) Bool
  (= (select w (mkslot i F_used)) (vbool true)))

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

; THE REPAIRED INVARIANT -- quantifier guarded by `used`.
(define-fun cdtWfUsed ((w World)) Bool
  (and (=> (usd w 0) (rch6 w 0 ROOT))
       (=> (usd w 1) (rch6 w 1 ROOT))
       (=> (usd w 2) (rch6 w 2 ROOT))
       (=> (usd w 3) (rch6 w 3 ROOT))))

(define-fun rangeok ((w World) (i Int) (f Fld)) Bool
  (let ((v (select w (mkslot i f))))
    (or ((_ is vabsent) v)
        (and ((_ is vpresent) v) (<= 0 (pidx v)) (< (pidx v) N)))))

(declare-const w World)
(declare-const u Int)

(assert (and (rangeok w 0 F_parent) (rangeok w 1 F_parent)
             (rangeok w 2 F_parent) (rangeok w 3 F_parent)))
(assert (and (or (usd w 0) (not (usd w 0)))))   ; `used` is a plain bool
(assert (= (select w (mkslot 0 F_used)) (vbool true)))  ; the root is in use

; one slot u, not the root, that is FREE and whose parent is absent
(assert (and (<= 0 u) (< u N)))
(assert (not (= u ROOT)))
(assert (not (usd w u)))
(assert (= (par w u) vabsent))

; ... and at least one OTHER slot still in use, so the table is not trivial
(declare-const v Int)
(assert (and (<= 0 v) (< v N)))
(assert (not (= v ROOT)))
(assert (not (= v u)))
(assert (usd w v))

(assert (cdtWfUsed w))

(check-sat)
(get-model)
(echo "--- witness readout ---")
(get-value (u v))
(get-value ((usd w 0) (usd w 1) (usd w 2) (usd w 3)))
(get-value ((par w 0) (par w 1) (par w 2) (par w 3)))
