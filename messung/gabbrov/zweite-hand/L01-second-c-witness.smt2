; ============================================================================
; L01, candidate premise (c) -- GROUND witness at N = 3.
;
; `L01-second-c.smt2` (the quantified form) returned `unknown` after 60 s, so
; it decides nothing.  This file settles it.  With N = 3 the guard `In u` is
; exactly u in {0,1,2}, so instantiating every guarded quantifier at 0, 1 and 2
; is EQUIVALENT to the quantified form, not weaker -- and the result is
; quantifier-free, hence decidable.
;
; Same convention: premises + body + NEGATED goal.
;   sat => the obligation is still REFUTED, i.e. premise (c) does NOT repair it.
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

; ---- (P1) plumbing range facts, instantiated at 0,1,2 ---------------------
(define-fun ranged ((u Int)) Bool
  (and (=> ((_ is present) (par0 u)) (In (idx (par0 u))))
       (=> ((_ is present) (prv0 u)) (In (idx (prv0 u))))
       (=> ((_ is present) (nxt0 u)) (In (idx (nxt0 u))))
       (=> ((_ is present) (fc0  u)) (In (idx (fc0  u))))))
(assert (ranged 0)) (assert (ranged 1)) (assert (ranged 2))

; ---- (P2) the invariant in the PRE-state ----------------------------------
(define-fun inv0 ((u Int)) Bool (=> (= (par0 u) absent) (= (prv0 u) absent)))
(assert (inv0 0)) (assert (inv0 1)) (assert (inv0 2))

; ---- (P3) cdt_wohlgeformt in the PRE-state (rank encoding) ----------------
(define-fun wf ((u Int)) Bool
  (and (>= (rank u) 0)
       (=> (not (= u WURZEL))
           (and ((_ is present) (par0 u))
                (< (rank (idx (par0 u))) (rank u))))))
(assert (wf 0)) (assert (wf 1)) (assert (wf 2))

; ---- (P4) s is a slot index ------------------------------------------------
(assert (In s))

; ---- CANDIDATE PREMISE (c): BACKWARD mutuality -----------------------------
;   c.slots[u].prev_sibling == Some(p)  =>  c.slots[p].next_sibling == Some(u)
(define-fun candC ((u Int)) Bool
  (=> ((_ is present) (prv0 u)) (= (nxt0 (idx (prv0 u))) (present u))))
(assert (candC 0)) (assert (candC 1)) (assert (candC 2))

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

; ---- non-degeneracy: no self-pointers, and the witness slot is not `s` -----
(assert (not (= t s)))
(define-fun noloop ((u Int)) Bool
  (and (not (= (par0 u) (present u))) (not (= (prv0 u) (present u)))
       (not (= (nxt0 u) (present u))) (not (= (fc0  u) (present u)))))
(assert (noloop 0)) (assert (noloop 1)) (assert (noloop 2))

(check-sat)
(get-model)
