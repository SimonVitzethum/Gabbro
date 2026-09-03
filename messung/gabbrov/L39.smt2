; L39 -- `drvok`, the fourth declared transition of the virtio status register.
; `messung/fragmente/F04.gab`:95-97:
;
;     transition drvok { DEVICE_STATUS: ACK | DRIVER | FEATURES_OK
;                                    -> ACK | DRIVER | FEATURES_OK | DRIVER_OK }
;
; `reg DEVICE_STATUS : u8 @0x14 class rw fields { ACK @0, DRIVER @1, DRIVER_OK @2,
; FEATURES_OK @3 }`, so the bits are 1, 2, 4, 8.
;
; **The register is a `u8`, so this run is over BITVECTORS and not over integers**, and
; that is not a decoration: `V1.lean` writes the transition with `+` where the source
; writes `|`, on the stated ground that the bits are disjoint. THAT STEP IS PART OF THE
; VERIFICATION CONDITION here, and the solver checks it rather than the reader.

(set-option :timeout 60000)
(set-option :produce-models true)

(define-fun ACK         () (_ BitVec 8) #x01)
(define-fun DRIVER      () (_ BitVec 8) #x02)
(define-fun DRIVER_OK   () (_ BitVec 8) #x04)
(define-fun FEATURES_OK () (_ BitVec 8) #x08)

(declare-const status0 (_ BitVec 8))
(declare-const status1 (_ BitVec 8))

; The transition, as the SOURCE writes it: bitwise or on both sides.
(assert (=> (= status0 (bvor ACK DRIVER FEATURES_OK))
            (= status1 (bvor ACK DRIVER FEATURES_OK DRIVER_OK))))
(assert (= status0 (bvor ACK DRIVER FEATURES_OK)))

; The goal, negated -- and it is `V1.lean`'s form, with `+` where the source has `|`.
; If the disjointness argument is wrong anywhere, this is where it shows.
(assert (not (= status1 (bvadd ACK (bvadd DRIVER (bvadd FEATURES_OK DRIVER_OK))))))

(check-sat)
(get-model)
