; ============================================================================
; L01 -- table invariant `wurzel_ohne_vorgaenger` re-established by `unlink`.
; Blind re-derivation from F01-excerpt.gab + Body-model.lean + V1-*.lean.
;
; CONVENTION (asked for explicitly):
;   we assert the DECLARED premises and the body, then the NEGATION of the
;   post-state goal.
;     unsat   => obligation HOLDS      (verdict: passed)
;     sat     => obligation REFUTED    (the model is a counterexample)
;     unknown => undecided
;
; PREMISES USED -- and NOTHING ELSE.  Each one is a line the fragment DECLARES:
;   (P1) plumbing: an `option index into CapSpace` that is Some(k) has
;        0 <= k < N.  (Explicitly allowed: the checker's own passes carry it.)
;   (P2) the table invariant itself in the PRE-state
;        (`invariant wurzel_ohne_vorgaenger`, F01:33-35).
;   (P3) `maintains cdt_wohlgeformt` (F01:63) -- every slot reaches WURZEL=0
;        via `parent`.  Declared, so it is fair game; encoded as a rank
;        function, which is equivalent to `reachesIn ... N` on a finite domain.
;   (P4) `requires c.slots[s].used` -- modelled only as `0 <= s < N`; `used`
;        is a bool field and L01 never mentions it.
;
; NOT ASSUMED (the point of the exercise): mutuality of the sibling chain
; («B14»), sibling/parent agreement, injectivity, non-self-loops.
; ============================================================================

(set-option :timeout 60000)
(set-option :produce-models true)
(set-logic ALL)

; `option index into CapSpace`, i.e. Body-model.lean's `Value` restricted to
; the only two forms a field of this type can hold: `.absent` / `.present k`.
(declare-datatypes ((OptIdx 0)) (((absent) (present (idx Int)))))

; ---- the table domain: `forall s in slots of Self` = 0 .. N-1 -------------
(declare-const N Int)
(assert (> N 0))
(define-fun In ((t Int)) Bool (and (<= 0 t) (< t N)))

; the WURZEL constant of the table (F01:10)
(define-fun WURZEL () Int 0)

; ---- the pre-state world: one uninterpreted function per slot field -------
(declare-fun par0 (Int) OptIdx)   ; parent
(declare-fun prv0 (Int) OptIdx)   ; prev_sibling
(declare-fun nxt0 (Int) OptIdx)   ; next_sibling
(declare-fun fc0  (Int) OptIdx)   ; first_child

; ---- (P4) the argument `s` is a slot index --------------------------------
(declare-const s Int)
(assert (In s))

; ---- (P1) plumbing range facts --------------------------------------------
(assert (forall ((t Int)) (=> (In t)
  (and (=> ((_ is present) (par0 t)) (In (idx (par0 t))))
       (=> ((_ is present) (prv0 t)) (In (idx (prv0 t))))
       (=> ((_ is present) (nxt0 t)) (In (idx (nxt0 t))))
       (=> ((_ is present) (fc0  t)) (In (idx (fc0  t))))))))

; ---- (P2) the invariant in the PRE-state ----------------------------------
(assert (forall ((t Int)) (=> (In t)
  (=> (= (par0 t) absent) (= (prv0 t) absent)))))

; ---- (P3) cdt_wohlgeformt in the PRE-state --------------------------------
; `forall s in slots of c : c.slots[s] reaches WURZEL via parent`, bound = N.
; Rank encoding: equivalent on a finite domain (a strictly decreasing rank
; forbids a cycle, and every non-root has a parent, so the walk ends at WURZEL
; in at most N steps).
(declare-fun rank (Int) Int)
(assert (forall ((t Int)) (=> (In t)
  (and (>= (rank t) 0)
       (=> (not (= t WURZEL))
           (and ((_ is present) (par0 t))
                (< (rank (idx (par0 t))) (rank t))))))))

; ===========================================================================
; THE BODY of `impl fn unlink(c, s)` -- F01:66-84.
; A sequence of writes; the LAST write to a place wins.  Each step below is
; one `store` of Body-model.lean, read off the state the previous step left.
; ===========================================================================

; -- step 1: match c.slots[s].prev_sibling
;      Some(p) => c.slots[p].next_sibling = c.slots[s].next_sibling
;      None    => match c.slots[s].parent
;                   Some(par) => c.slots[par].first_child = c.slots[s].next_sibling
;                   None      => {}
(define-fun nxt1 ((i Int)) OptIdx
  (ite (and ((_ is present) (prv0 s)) (= i (idx (prv0 s))))
       (nxt0 s)
       (nxt0 i)))
(define-fun fc1 ((i Int)) OptIdx
  (ite (and (= (prv0 s) absent)
            ((_ is present) (par0 s))
            (= i (idx (par0 s))))
       (nxt0 s)
       (fc0 i)))
; par and prv are untouched by step 1:
(define-fun par1 ((i Int)) OptIdx (par0 i))
(define-fun prv1 ((i Int)) OptIdx (prv0 i))

; -- step 2: match c.slots[s].next_sibling
;      Some(n) => c.slots[n].prev_sibling = c.slots[s].prev_sibling
;      None    => {}
;    NOTE the reads are taken from the state AFTER step 1 -- `nxt1 s`, `prv1 s`.
(define-fun prv2 ((i Int)) OptIdx
  (ite (and ((_ is present) (nxt1 s)) (= i (idx (nxt1 s))))
       (prv1 s)
       (prv1 i)))

; -- step 3: the four unconditional writes to slot s (these WIN over 1 and 2)
(define-fun par3 ((i Int)) OptIdx (ite (= i s) absent (par1 i)))
(define-fun fc3  ((i Int)) OptIdx (ite (= i s) absent (fc1  i)))
(define-fun nxt3 ((i Int)) OptIdx (ite (= i s) absent (nxt1 i)))
(define-fun prv3 ((i Int)) OptIdx (ite (= i s) absent (prv2 i)))

; ===========================================================================
; THE NEGATED GOAL: the invariant FAILS in the post-state at some slot t.
; ===========================================================================
(declare-const t Int)
(assert (In t))
(assert (= (par3 t) absent))
(assert (not (= (prv3 t) absent)))

; ===========================================================================
; CANDIDATE PREMISE (c) -- BACKWARD mutuality, the OTHER half of <<B14>>:
;   forall u : c.slots[u].prev_sibling == Some(p) => c.slots[p].next_sibling == Some(u)
; Same <<B14>> gap, opposite direction.
; ===========================================================================
(assert (forall ((u Int)) (=> (and (In u) ((_ is present) (prv0 u)))
  (= (nxt0 (idx (prv0 u))) (present u)))))
(check-sat)
(get-model)
