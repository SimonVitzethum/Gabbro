; ============================================================================
; L01 -- BASE premises only, ground at N = 3, with every degeneracy forbidden.
;
; The quantified robustness file `L01-second-e.smt2` returned `unknown` after
; 60 s, so it decides nothing.  This is the same question, quantifier-free:
; with N = 3 the guard `In u` is exactly u in {0,1,2}, so instantiating each
; guarded quantifier at 0,1,2 is EQUIVALENT to the quantified form.
;
; Forbidden here, to show the refutation is not an artefact of a degenerate
; model: any self-pointer in the pre-state, t = s, the predecessor sibling of
; `s` being its own parent, and a self-loop in the post-state prev_sibling.
;   sat => the counterexample survives all of that.
; ============================================================================

(set-option :timeout 60000)
(set-option :produce-models true)
(set-logic ALL)

(declare-datatypes ((OptIdx 0)) (((absent) (present (idx Int)))))

(define-fun N () Int 3)
(define-fun WURZEL () Int 0)
(define-fun In ((u Int)) Bool (and (<= 0 u) (< u N)))

(declare-fun par0 (Int) OptIdx)
(declare-fun prv0 (Int) OptIdx)
(declare-fun nxt0 (Int) OptIdx)
(declare-fun fc0  (Int) OptIdx)
(declare-fun rank (Int) Int)

(declare-const s Int)
(declare-const t Int)

(define-fun ranged ((u Int)) Bool
  (and (=> ((_ is present) (par0 u)) (In (idx (par0 u))))
       (=> ((_ is present) (prv0 u)) (In (idx (prv0 u))))
       (=> ((_ is present) (nxt0 u)) (In (idx (nxt0 u))))
       (=> ((_ is present) (fc0  u)) (In (idx (fc0  u))))))
(assert (ranged 0)) (assert (ranged 1)) (assert (ranged 2))

(define-fun inv0 ((u Int)) Bool (=> (= (par0 u) absent) (= (prv0 u) absent)))
(assert (inv0 0)) (assert (inv0 1)) (assert (inv0 2))

(define-fun wf ((u Int)) Bool
  (and (>= (rank u) 0)
       (=> (not (= u WURZEL))
           (and ((_ is present) (par0 u))
                (< (rank (idx (par0 u))) (rank u))))))
(assert (wf 0)) (assert (wf 1)) (assert (wf 2))

(assert (In s))

; ---- the body of `unlink`, identical to the base file ---------------------
(define-fun nxt1 ((i Int)) OptIdx
  (ite (and ((_ is present) (prv0 s)) (= i (idx (prv0 s)))) (nxt0 s) (nxt0 i)))
(define-fun fc1 ((i Int)) OptIdx
  (ite (and (= (prv0 s) absent) ((_ is present) (par0 s)) (= i (idx (par0 s))))
       (nxt0 s) (fc0 i)))
(define-fun par1 ((i Int)) OptIdx (par0 i))
(define-fun prv1 ((i Int)) OptIdx (prv0 i))
(define-fun prv2 ((i Int)) OptIdx
  (ite (and ((_ is present) (nxt1 s)) (= i (idx (nxt1 s)))) (prv1 s) (prv1 i)))
(define-fun par3 ((i Int)) OptIdx (ite (= i s) absent (par1 i)))
(define-fun fc3  ((i Int)) OptIdx (ite (= i s) absent (fc1  i)))
(define-fun nxt3 ((i Int)) OptIdx (ite (= i s) absent (nxt1 i)))
(define-fun prv3 ((i Int)) OptIdx (ite (= i s) absent (prv2 i)))

; ---- NEGATED goal ----------------------------------------------------------
(assert (In t))
(assert (= (par3 t) absent))
(assert (not (= (prv3 t) absent)))

; ---- every degeneracy forbidden --------------------------------------------
(assert (not (= t s)))
(assert (not (= (prv0 s) (par0 s))))
(assert (not (= (prv3 t) (present t))))
(define-fun noloop ((u Int)) Bool
  (and (not (= (par0 u) (present u))) (not (= (prv0 u) (present u)))
       (not (= (nxt0 u) (present u))) (not (= (fc0  u) (present u)))))
(assert (noloop 0)) (assert (noloop 1)) (assert (noloop 2))

(check-sat)
(get-model)
