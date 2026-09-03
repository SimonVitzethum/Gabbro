; ===================================================================
; L40, the LITERAL Lean Prop, as a cross-check on the reading.
;
; V1-L40.lean reads
;   L40 s s' := forall v, s.world DEVICE_STATUS = .int v ->
;                         s'.world DEVICE_STATUS = .int 0
; i.e. a pre/post relation.  Instantiated over the declared step relation
; -- the only pre/post pairs a checker has -- that is
;
;     (forall p q) step(p,q) -> q = 0
;
; This is the DEMONIC reading ("every declared step ends in 0"), where
; L40-second.smt2 takes the ANGELIC one ("from every state SOME declared
; step reaches 0").  Both are asserted here-or-there so the verdict does
; not hang on the choice.
;
; VERDICT CONVENTION (premises, then the NEGATION of the goal):
;   unsat   => holds     sat => refuted, model is the counterexample
;   Negation asserted below: (exists p q) step(p,q) /\ q /= 0
; ===================================================================

(set-option :timeout 60000)
(set-option :produce-models true)
(set-logic BV)

(define-fun ACK         () (_ BitVec 8) #x01)
(define-fun DRIVER      () (_ BitVec 8) #x02)
(define-fun DRIVER_OK   () (_ BitVec 8) #x04)
(define-fun FEATURES_OK () (_ BitVec 8) #x08)

; the four declared transitions, and no more -- byte-identical to L40
(define-fun step ((p (_ BitVec 8)) (q (_ BitVec 8))) Bool
  (or
    (and (= p #x00) (= q ACK))
    (and (= p ACK)  (= q (bvor ACK DRIVER)))
    (and (= p (bvor ACK DRIVER))
         (= q (bvor (bvor ACK DRIVER) FEATURES_OK)))
    (and (= p (bvor (bvor ACK DRIVER) FEATURES_OK))
         (= q (bvor (bvor (bvor ACK DRIVER) FEATURES_OK) DRIVER_OK)))))

(declare-const pre  (_ BitVec 8))
(declare-const post (_ BitVec 8))

; --- NEGATION of the literal L40 -------------------------------------
(assert (step pre post))
(assert (not (= post #x00)))

(check-sat)
(get-model)
