; ===================================================================
; FOLLOW-UP 1, part a: is the L40 witness pre-state REACHABLE?
;
; A counterexample on an unreachable state would be an artefact of the
; encoding (the register is a u8, so 251 of its 256 values never occur
; in a run that starts at 0 and only takes declared steps).  So restrict
; the witness to the reachable set and ask again.
;
; Reachable set = closure of the initial state 0 under the four declared
; transitions.  `transition ack { DEVICE_STATUS: 0 -> ACK }` is the only
; clause with no predecessor, so 0 is the initial state, and the chain is
;     0 -> 1 -> 3 -> 11 -> 15   (0x00, 0x01, 0x03, 0x0b, 0x0f)
; and it stops there: no clause has 15 as its pre-value.
;
; VERDICT CONVENTION (premises, then the NEGATION of the goal):
;   unsat   => every REACHABLE state does have a declared step to 0
;   sat     => a REACHABLE state has none; the model names it
;   unknown => undecided
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

(define-fun reachable ((p (_ BitVec 8))) Bool
  (or (= p #x00) (= p #x01) (= p #x03) (= p #x0b) (= p #x0f)))

(declare-const pre (_ BitVec 8))

; --- NEGATION of L40, witness restricted to reachable states ---------
(assert (reachable pre))
(assert (forall ((q (_ BitVec 8)))
          (not (and (step pre q) (= q #x00)))))

(check-sat)
(get-model)
