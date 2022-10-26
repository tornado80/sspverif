(declare-datatype
  State_keys
  (
    (mk-state-keys
      (state-keys-T (Array Int (Maybe (Array Bool (Maybe Bits_n)))))
      (state-keys-z (Array Int (Maybe Bool)))
      (state-keys-flag (Array Int (Maybe Bool))))))



(define-fun project-State_Left_keys_top ((in State_Left_keys_top)) State_keys
  (mk-state-keys (state-Left-keys_top-T    in)
                 (state-Left-keys_top-z    in)
                 (state-Left-keys_top-flag in)))

(define-fun project-State_Right_keys_top ((in State_Right_keys_top)) State_keys
  (mk-state-keys (state-Right-keys_top-T    in)
                 (state-Right-keys_top-z    in)
                 (state-Right-keys_top-flag in)))

(define-fun project-State_Left_keys_bottom ((in State_Left_keys_bottom)) State_keys
  (mk-state-keys (state-Left-keys_bottom-T    in)
                 (state-Left-keys_bottom-z    in)
                 (state-Left-keys_bottom-flag in)))

(define-fun project-State_Right_keys_bottom ((in State_Right_keys_bottom)) State_keys
  (mk-state-keys (state-Right-keys_bottom-T    in)
                 (state-Right-keys_bottom-z    in)
                 (state-Right-keys_bottom-flag in)))


; layer handle:
(declare-const handle Int)

; possible input for SETBIT
(declare-const bit Bool)

; possible input for GBLG     oracle GBLG(h: Integer, l: Integer, r: Integer, op: fn Bool,Bool -> Bool, j: Integer) -> Table(Bits(p),Bool) {
(declare-const l Int)
(declare-const r Int)
(declare-const op (Array (Tuple2 Bool Bool) (Maybe Bool)))
(declare-const j Int)

; possible state arrays
(declare-const array-state-left-old (Array Int CompositionState-Left))
(declare-const length-state-left-old Int)
(declare-const array-state-right-old (Array Int CompositionState-Right))
(declare-const length-state-right-old Int)
(declare-const array-state-left-new (Array Int CompositionState-Left))
(declare-const length-state-left-new Int)
(declare-const array-state-right-new (Array Int CompositionState-Right))
(declare-const length-state-right-new Int)

; possible state
(declare-const state-left-old CompositionState-Left)
(declare-const state-right-old CompositionState-Right)
(declare-const state-right-after-EVAL CompositionState-Right)
(declare-const state-left-new CompositionState-Left)
(declare-const state-right-new CompositionState-Right)

; return value for GBLG call
(declare-const return-left Return_Left_gate_GBLG)
(declare-const return-right Return_Right_simgate_GBLG)
(declare-const is-abort-left Bool)
(declare-const is-abort-right Bool)
(declare-const y-left  (Maybe (Array Bits_p (Maybe Bool))))
(declare-const y-right (Maybe (Array Bits_p (Maybe Bool))))

; sampled value Z and associated values
(declare-const Z-left  (Array Bool (Maybe Bits_n)))
(declare-const Z-right (Array Bool (Maybe Bits_n)))
(declare-const ctr-r-left Int)
(declare-const ctr-r-right Int)
(declare-const ctr-rr-left Int)
(declare-const ctr-rr-right Int)
(declare-const ctr-r-left-new Int)
(declare-const ctr-r-right-new Int)
(declare-const ctr-rr-left-new Int)
(declare-const ctr-rr-right-new Int)
(declare-const r-left Bits_n)
(declare-const r-right Bits_n)
(declare-const rr-left Bits_n)
(declare-const rr-right Bits_n)

(push 1)
(assert true)
(check-sat) ;2
(pop 1)


(assert
(and

              ;assignment of return (value,state)
              (= return-left      (oracle-Left-gate-GBLG array-state-left-old length-state-left-old handle l r op j))
              (= return-right     (oracle-Right-simgate-GBLG array-state-right-old length-state-right-old handle l r op j))

              ;assignment of return values
              (= y-left       (return-Left-gate-GBLG-value return-left))
              (= y-right      (return-Right-simgate-GBLG-value return-right))

              ;assignment of abort values
              (= is-abort-left    (return-Left-gate-GBLG-is-abort return-left))
              (= is-abort-right   (return-Right-simgate-GBLG-is-abort return-right))

              ;assignment of return state
              (= array-state-left-new   (return-Left-gate-GBLG-state return-left))
              (= array-state-right-new  (return-Right-simgate-GBLG-state return-right))

              ;assignment of return length
              (= length-state-left-new   (return-Left-gate-GBLG-state-length return-left))
              (= length-state-right-new  (return-Right-simgate-GBLG-state-length return-right))

              ;initial state list contains only one state
              (= length-state-left-old 1)
              (= length-state-right-old 1)
)
)

(push 1)
(assert true)
(check-sat) ;3
(pop 1)


; special-purpose glue for this particular project
(assert
(and
              ;op should be total
(not (= (select op (mk-tuple2 true  true ))(as mk-none (Maybe Bool))))
(not (= (select op (mk-tuple2 true  false))(as mk-none (Maybe Bool))))
(not (= (select op (mk-tuple2 false true ))(as mk-none (Maybe Bool))))
(not (= (select op (mk-tuple2 false false))(as mk-none (Maybe Bool))))
))

(push 1)
(assert true)
(check-sat) ;4
(pop 1)

(assert
;;;;;;Pre-condition (randomness mapping):
;equality of values of the sample functions for the lower Key package
(forall ((ctr Int))
(and
              (= (__sample-rand-Left-Bits_n 3 ctr)
                 (__sample-rand-Right-Bits_n 1 ctr))
              (= (__sample-rand-Left-Bits_n 4 ctr)
                 (__sample-rand-Right-Bits_n 2 ctr)))))

;(push 1)
;(assert true)
;(check-sat) ;4
;(pop 1)

(assert
(forall ((ctr Int))
(and
;equality of values of the sample functions for the encryptions
              (= (__sample-rand-Left-Bits_n   9 ctr)
                 (__sample-rand-Right-Bits_n  9 ctr))
              (= (__sample-rand-Left-Bits_n  11 ctr)
                 (__sample-rand-Right-Bits_n 10 ctr))
              (= (__sample-rand-Left-Bits_n   9 (+ 1 ctr))
                 (__sample-rand-Right-Bits_n 11 ctr))
              (= (__sample-rand-Left-Bits_n  11 (+ 1 ctr))
                 (__sample-rand-Right-Bits_n 12 ctr))
              (= (__sample-rand-Left-Bits_n   9 (+ 2 ctr))
                 (__sample-rand-Right-Bits_n 13 ctr))
              (= (__sample-rand-Left-Bits_n  11 (+ 2 ctr))
                 (__sample-rand-Right-Bits_n 14 ctr))
              (= (__sample-rand-Left-Bits_n   9 (+ 3 ctr))
                 (__sample-rand-Right-Bits_n 15 ctr))
              (= (__sample-rand-Left-Bits_n  11 (+ 3 ctr))
                 (__sample-rand-Right-Bits_n 16 ctr))

)
)
)