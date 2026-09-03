; ===================================================================
; FOLLOW-UP 1, the STRONGER claim.
;
; L40-second.smt2 shows SOME pre-state has no declared step to 0.
; The stronger reading of that failure is:
;
;     NO declared transition reaches 0 from ANY state.
;        (forall p q) step(p,q) -> q /= 0
;
; That is a claim about the manifest, not about one state, and it
; distinguishes "one state is missing a reset" from "reset is not in
; the transition table at all".
;
; VERDICT CONVENTION (premises, then the NEGATION of the goal):
;   unsat   => the STRONG claim HOLDS -- no declared step ever lands on 0
;   sat     => the strong claim is refuted; the model names a step to 0,
;              i.e. the failure really is only local
;   unknown => undecided
;
;   Negation asserted below: (exists p q) step(p,q) /\ q = 0
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

; --- NEGATION: some declared step DOES land on 0 ---------------------
(assert (step pre post))
(assert (= post #x00))

(check-sat)
(get-model)
