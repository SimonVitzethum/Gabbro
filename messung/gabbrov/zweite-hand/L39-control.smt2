; ===================================================================
; L39 (drvok) -- CONTROL for the L40 encoding.
;
; Same model, same premise supply, same goal SHAPE as L40-second.smt2 --
; only the row changes.  Its job is to prove the encoding discriminates:
; if this and L40 come back with the SAME verdict, the encoding is
; broken and that outranks either verdict.
;
; L39 (from V1-L40.lean, the neighbour above L40):
;   s.world DEVICE_STATUS = .int (ACK + DRIVER + FEATURES_OK)  ->
;   s'.world DEVICE_STATUS = .int (ACK + DRIVER + FEATURES_OK + DRIVER_OK)
; The four bits are disjoint, so Lean's `+` is the source's `|`.
;
; VERDICT CONVENTION (premises, then the NEGATION of the goal):
;   unsat   => the obligation HOLDS      (passed)
;   sat     => the obligation is REFUTED (the model is a counterexample)
;   unknown => undecided
;
;   Goal:     (forall p) p = ACK|DRIVER|FEATURES_OK ->
;                        (exists q) step(p,q) /\ q = ACK|DRIVER|FEATURES_OK|DRIVER_OK
;   Negation: (exists p) p = ACK|DRIVER|FEATURES_OK /\
;                        (forall q) not(step(p,q) /\ q = ...|DRIVER_OK)
; ===================================================================

(set-option :timeout 60000)
(set-option :produce-models true)
(set-logic BV)

(define-fun ACK         () (_ BitVec 8) #x01)   ; @0
(define-fun DRIVER      () (_ BitVec 8) #x02)   ; @1
(define-fun DRIVER_OK   () (_ BitVec 8) #x04)   ; @2
(define-fun FEATURES_OK () (_ BitVec 8) #x08)   ; @3

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

; --- the witness pre-state (skolem of the negated goal) --------------
(declare-const pre (_ BitVec 8))

; --- NEGATION of L39 -------------------------------------------------
(assert (= pre L39_pre))
(assert (forall ((q (_ BitVec 8)))
          (not (and (step pre q) (= q L39_post)))))

(check-sat)
(get-model)
