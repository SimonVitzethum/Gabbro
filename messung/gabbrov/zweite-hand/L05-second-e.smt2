(set-option :produce-models true)
(set-option :timeout 60000)

; ===========================================================================
;  FOLLOW-UP (e) -- does the REPAIRED invariant survive `unlink`?
;
;  (d) showed the `used`-guarded invariant is satisfiable.  That only makes it
;  a candidate.  This file re-runs the ORIGINAL L05 verification condition
;  with `cdt_wohlgeformt` replaced by the repaired form, i.e.
;
;    cdtWfUsed(pre) AND unlink's body ran  ==>  cdtWfUsed(post)
;
;  VC convention again: premises + body + NEGATED goal.
;      unsat => the repair rescues L05
;      sat   => the repair does NOT rescue L05; the defect is elsewhere too
;
;  Note what `unlink` does and does not touch: it clears `parent`,
;  `first_child`, `next_sibling`, `prev_sibling` of slot s.  It does NOT touch
;  `used` -- and its own `requires` says `c.slots[s].used` is TRUE on entry.
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

(define-fun cdtWfUsed ((w World)) Bool
  (and (=> (usd w 0) (rch6 w 0 ROOT))
       (=> (usd w 1) (rch6 w 1 ROOT))
       (=> (usd w 2) (rch6 w 2 ROOT))
       (=> (usd w 3) (rch6 w 3 ROOT))))

(define-fun rangeok ((w World) (i Int) (f Fld)) Bool
  (let ((v (select w (mkslot i f))))
    (or ((_ is vabsent) v)
        (and ((_ is vpresent) v) (<= 0 (pidx v)) (< (pidx v) N)))))

(declare-const w0 World)
(declare-const x  Int)

(assert (and (<= 0 x) (< x N)))
(assert (and (rangeok w0 0 F_parent) (rangeok w0 0 F_first_child)
             (rangeok w0 0 F_next_sibling) (rangeok w0 0 F_prev_sibling)
             (rangeok w0 1 F_parent) (rangeok w0 1 F_first_child)
             (rangeok w0 1 F_next_sibling) (rangeok w0 1 F_prev_sibling)
             (rangeok w0 2 F_parent) (rangeok w0 2 F_first_child)
             (rangeok w0 2 F_next_sibling) (rangeok w0 2 F_prev_sibling)
             (rangeok w0 3 F_parent) (rangeok w0 3 F_first_child)
             (rangeok w0 3 F_next_sibling) (rangeok w0 3 F_prev_sibling)))
(assert (= (select w0 (mkslot x F_used)) (vbool true)))   ; `requires`
(assert (cdtWfUsed w0))                                   ; repaired pre-state

; ------------------------- the body of `unlink` ----------------------------
(define-fun ps0 () Value (select w0 (mkslot x F_prev_sibling)))
(define-fun pa0 () Value (select w0 (mkslot x F_parent)))
(define-fun ns0 () Value (select w0 (mkslot x F_next_sibling)))
(define-fun w1 () World
  (ite ((_ is vpresent) ps0)
       (store w0 (mkslot (pidx ps0) F_next_sibling) ns0)
       (ite ((_ is vpresent) pa0)
            (store w0 (mkslot (pidx pa0) F_first_child) ns0)
            w0)))
(define-fun ns1 () Value (select w1 (mkslot x F_next_sibling)))
(define-fun ps1 () Value (select w1 (mkslot x F_prev_sibling)))
(define-fun w2 () World
  (ite ((_ is vpresent) ns1)
       (store w1 (mkslot (pidx ns1) F_prev_sibling) ps1)
       w1))
(define-fun w3 () World (store w2 (mkslot x F_parent)       vabsent))
(define-fun w4 () World (store w3 (mkslot x F_first_child)  vabsent))
(define-fun w5 () World (store w4 (mkslot x F_next_sibling) vabsent))
(define-fun w6 () World (store w5 (mkslot x F_prev_sibling) vabsent))

(assert (not (cdtWfUsed w6)))

(check-sat)
(get-model)
(echo "--- witness readout ---")
(get-value (x))
(get-value ((usd w0 0) (usd w0 1) (usd w0 2) (usd w0 3)))
(get-value ((par w0 0) (par w0 1) (par w0 2) (par w0 3)))
(get-value ((usd w6 0) (usd w6 1) (usd w6 2) (usd w6 3)))
(get-value ((par w6 0) (par w6 1) (par w6 2) (par w6 3)))
