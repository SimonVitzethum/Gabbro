; L23 -- "`caller` and `reply_owner` are set together or not at all", the table invariant
; `antwortpflicht_paarig` of `messung/fragmente/F03.gab`:108-110, held against the two
; assignments of the fastpath (:197-198).
;
;     e.slots[core].caller      = Some(caller);
;     e.slots[core].reply_owner = Some(picked);
;
; This is the PRE/POST half of `L24`, and `L24` is row 1 of `dokumente/AUSNAHMEN.md`. The
; half that IS sayable is exactly this one, and the run is here to show what the solver
; does with the sayable half while the other half has no statement at all.

(set-option :timeout 60000)
(set-option :produce-models true)
(declare-datatypes ((Opt 0)) (((none) (some (idx Int)))))

(declare-const N Int)                     ; `table Endpoints count …`
(declare-const core Int)                  ; the endpoint being opened
(declare-const cl Int)                    ; `caller`
(declare-const pk Int)                    ; `picked`
(assert (> N 0))
(assert (and (>= core 0) (< core N)))

(declare-fun caller0 (Int) Opt)
(declare-fun owner0  (Int) Opt)

; THE PREMISE: the invariant holds before.
(assert (forall ((x Int)) (=> (and (>= x 0) (< x N))
  (= ((_ is none) (caller0 x)) ((_ is none) (owner0 x))))))

; The two assignments.
(define-fun caller1 ((x Int)) Opt (ite (= x core) (some cl) (caller0 x)))
(define-fun owner1  ((x Int)) Opt (ite (= x core) (some pk) (owner0  x)))

; The goal, negated.
(assert (not (forall ((x Int)) (=> (and (>= x 0) (< x N))
  (= ((_ is none) (caller1 x)) ((_ is none) (owner1 x)))))))

(check-sat)
(get-model)
