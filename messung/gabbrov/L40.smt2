; L40 -- "a reset applies from EVERY state".
;
; `PFLICHTEN.md` marks this row with a gap of its own: **«B26» -- no placeholder for the
; pre-state, so the transition table cannot be complete.** `messung/fragmente/F04.gab`:98
; says the same in its own comment: `transition reset { DEVICE_STATUS: any -> 0 }` is not
; writable.
;
; So the verification condition here is not "does the reset work". **It is: does the
; DECLARED transition table contain a transition that reaches 0 from an arbitrary state?**
; That is a question about the four transitions the fragment does declare, and a solver
; can answer it. The answer is the measurement of the gap.
;
; The four declared transitions (`F04.gab`:91-97), as one relation:
;     ack    0                          -> ACK
;     drv    ACK                        -> ACK|DRIVER
;     featok ACK|DRIVER                 -> ACK|DRIVER|FEATURES_OK
;     drvok  ACK|DRIVER|FEATURES_OK     -> ACK|DRIVER|FEATURES_OK|DRIVER_OK

(set-option :timeout 60000)
(set-option :produce-models true)

(define-fun ACK         () (_ BitVec 8) #x01)
(define-fun DRIVER      () (_ BitVec 8) #x02)
(define-fun DRIVER_OK   () (_ BitVec 8) #x04)
(define-fun FEATURES_OK () (_ BitVec 8) #x08)

(define-fun schritt ((a (_ BitVec 8)) (b (_ BitVec 8))) Bool
  (or (and (= a #x00)                             (= b ACK))
      (and (= a ACK)                              (= b (bvor ACK DRIVER)))
      (and (= a (bvor ACK DRIVER))                (= b (bvor ACK DRIVER FEATURES_OK)))
      (and (= a (bvor ACK DRIVER FEATURES_OK))
           (= b (bvor ACK DRIVER FEATURES_OK DRIVER_OK)))))

; `L40` in `V1.lean`: `forall v, status = v -> status' = 0`. Under the declared table that
; reads: from every pre-state there is a declared step to 0.
;
; The goal, negated: is there a pre-state from which NO declared step reaches 0?
(declare-const v (_ BitVec 8))
(assert (not (exists ((w (_ BitVec 8))) (and (schritt v w) (= w #x00)))))

(check-sat)
(get-model)
