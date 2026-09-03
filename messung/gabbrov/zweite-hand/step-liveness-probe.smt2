; Sanity probe (not a VC): is every one of the four declared clauses live
; in my `step`?  A dead clause would bias L40 towards `sat` for free.
; Each check is "does step contain exactly this pair?" -- expect sat x4,
; then one unsat showing there is no FIFTH pre-value with a successor.
(set-option :produce-models true)
(set-logic BV)

(define-fun ACK         () (_ BitVec 8) #x01)
(define-fun DRIVER      () (_ BitVec 8) #x02)
(define-fun DRIVER_OK   () (_ BitVec 8) #x04)
(define-fun FEATURES_OK () (_ BitVec 8) #x08)

(define-fun step ((p (_ BitVec 8)) (q (_ BitVec 8))) Bool
  (or
    (and (= p #x00) (= q ACK))
    (and (= p ACK)  (= q (bvor ACK DRIVER)))
    (and (= p (bvor ACK DRIVER))
         (= q (bvor (bvor ACK DRIVER) FEATURES_OK)))
    (and (= p (bvor (bvor ACK DRIVER) FEATURES_OK))
         (= q (bvor (bvor (bvor ACK DRIVER) FEATURES_OK) DRIVER_OK)))))

(echo "ack    0 -> 1  (expect sat)")
(push 1) (assert (step #x00 #x01)) (check-sat) (pop 1)
(echo "drv    1 -> 3  (expect sat)")
(push 1) (assert (step #x01 #x03)) (check-sat) (pop 1)
(echo "featok 3 -> 11 (expect sat)")
(push 1) (assert (step #x03 #x0b)) (check-sat) (pop 1)
(echo "drvok 11 -> 15 (expect sat)")
(push 1) (assert (step #x0b #x0f)) (check-sat) (pop 1)
(echo "a fifth pre-value with a successor (expect unsat)")
(declare-const p (_ BitVec 8))
(declare-const q (_ BitVec 8))
(assert (step p q))
(assert (not (or (= p #x00) (= p #x01) (= p #x03) (= p #x0b))))
(check-sat)
