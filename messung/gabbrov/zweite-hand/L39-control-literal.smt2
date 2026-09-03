; ===================================================================
; L39 (drvok) in the LITERAL/demonic shape -- control for
; L40-literal-prop.smt2, so that reading is discriminating too.
;
;   Goal:     (forall p q) step(p,q) /\ p = ACK|DRIVER|FEATURES_OK
;                          -> q = ACK|DRIVER|FEATURES_OK|DRIVER_OK
;   Negation: (exists p q) step(p,q) /\ p = ... /\ q /= ...
;
;   unsat => holds     sat => refuted     unknown => undecided
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

(define-fun L39_pre  () (_ BitVec 8) (bvor (bvor ACK DRIVER) FEATURES_OK))
(define-fun L39_post () (_ BitVec 8) (bvor L39_pre DRIVER_OK))

(declare-const pre  (_ BitVec 8))
(declare-const post (_ BitVec 8))

(assert (step pre post))
(assert (= pre L39_pre))
(assert (not (= post L39_post)))

(check-sat)
(get-model)
