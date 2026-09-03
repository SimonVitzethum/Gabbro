; ===================================================================
; L40 -- "a reset applies from EVERY state"
; Blind re-derivation, written from F04-excerpt.gab + Body-model.lean
; + V1-L40.lean only.  No other encoding of this row was consulted.
;
; VERDICT CONVENTION (premises asserted, then the NEGATION of the goal):
;   unsat   => the obligation HOLDS      (passed)
;   sat     => the obligation is REFUTED (the model is a counterexample)
;   unknown => undecided
;
; MODELLING DECISIONS
;  1. The Lean world is `Place -> Value`; the only place this row talks
;     about is `.global "DEVICE_STATUS"`, and the register is declared
;     `reg DEVICE_STATUS : u8`.  So the whole state is projected onto one
;     8-bit bitvector.  `Value.int v` is assumed total on that place (a u8
;     register never holds `.absent`/`.bool`; otherwise L40 would be
;     VACUOUSLY true, which would be an encoding artefact, not a proof).
;  2. Field bits from the source: ACK @0, DRIVER @1, DRIVER_OK @2,
;     FEATURES_OK @3  ->  1, 2, 4, 8.  (Matches the VirtIO status bits:
;     ACKNOWLEDGE=1, DRIVER=2, DRIVER_OK=4, FEATURES_OK=8.)  `|` is bvor.
;  3. The premise supply is EXACTLY the four declared `transition` clauses
;     and nothing else -- that is what a checker reading this manifest has.
;     `step p q` is their disjunction: 0->1, 1->3, 3->11, 11->15.
;  4. Reading of the row, taken from the task statement: "a reset applies
;     from every state" = from EVERY pre-state some declared step reaches 0.
;     Goal:      (forall p) (exists q) step(p,q) /\ q = 0
;     Negation:  (exists p) (forall q) not(step(p,q) /\ q = 0)
;     The existential p is skolemised into the constant `pre` so that
;     (get-model) hands back the witness pre-state by name.
; ===================================================================

(set-option :timeout 60000)
(set-option :produce-models true)
(set-logic BV)

(define-fun ACK         () (_ BitVec 8) #x01)   ; @0
(define-fun DRIVER      () (_ BitVec 8) #x02)   ; @1
(define-fun DRIVER_OK   () (_ BitVec 8) #x04)   ; @2
(define-fun FEATURES_OK () (_ BitVec 8) #x08)   ; @3

; the four declared transitions, and no more
(define-fun step ((p (_ BitVec 8)) (q (_ BitVec 8))) Bool
  (or
    ; transition ack    { DEVICE_STATUS: 0 -> ACK }
    (and (= p #x00) (= q ACK))
    ; transition drv    { DEVICE_STATUS: ACK -> ACK | DRIVER }
    (and (= p ACK)  (= q (bvor ACK DRIVER)))
    ; transition featok { ACK | DRIVER -> ACK | DRIVER | FEATURES_OK }
    (and (= p (bvor ACK DRIVER))
         (= q (bvor (bvor ACK DRIVER) FEATURES_OK)))
    ; transition drvok  { ACK | DRIVER | FEATURES_OK
    ;                  -> ACK | DRIVER | FEATURES_OK | DRIVER_OK }
    (and (= p (bvor (bvor ACK DRIVER) FEATURES_OK))
         (= q (bvor (bvor (bvor ACK DRIVER) FEATURES_OK) DRIVER_OK)))))

; --- the witness pre-state (skolem of the negated goal) --------------
(declare-const pre (_ BitVec 8))

; --- NEGATION of L40: from `pre`, NO declared step reaches 0 ---------
(assert (forall ((q (_ BitVec 8)))
          (not (and (step pre q) (= q #x00)))))

(check-sat)
(get-model)
