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

; special-purpose glue for this particular project
(assert
(and
              ;op should be total
(not (= (select op (mk-tuple2 true  true ))(as mk-none (Maybe Bool))))
(not (= (select op (mk-tuple2 true  false))(as mk-none (Maybe Bool))))
(not (= (select op (mk-tuple2 false true ))(as mk-none (Maybe Bool))))
(not (= (select op (mk-tuple2 false false))(as mk-none (Maybe Bool))))


;;;;;;Pre-condition (randomness mapping):
;equality of values of the sample functions for the lower Key package
(forall ((ctr Int))
(and
              (= (__sample-rand-Left-Bits_n 3 ctr)
                 (__sample-rand-Right-Bits_n 1 ctr))
              (= (__sample-rand-Left-Bits_n 4 ctr)
                 (__sample-rand-Right-Bits_n 2 ctr))

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
              (= (__sample-rand-Left-Bits_n   9  (+ 3 ctr))
                 (__sample-rand-Right-Bits_n 15 ctr))
              (= (__sample-rand-Left-Bits_n  11 (+ 3 ctr))
                 (__sample-rand-Right-Bits_n 16 ctr))

)
)
)
);(;let (
;
;              ;retrieving return state from the list
;              (= (select array-state-left-old 1) state-left-old)
;              (= (select array-state-right-old 1) state-right-old)
;              (= (select array-state-left-new length-state-left-new) state-left-new)
;              (= (select array-state-right-new length-state-right-new) state-right;-new)
;
;              (= (select array-state-right-new 5) state-right-after-EVAL)
;
;
;              ;assignment of the ctr of the sample instructions for the lower Key package
;              (= ctr-r-left   (composition-rand-Left-3  state-left-old))
;              (= ctr-r-right  (composition-rand-Right-1 state-right-old))
;              (= ctr-rr-left  (composition-rand-Left-4  state-left-old))
;              (= ctr-rr-right (composition-rand-Right-2 state-right-old))
;
;              ;assignment of the ctr of the sample instructions for the lower Key package on new state
;              (= ctr-r-left-new   (composition-rand-Left-3  state-left-new))
;              (= ctr-r-right-new  (composition-rand-Right-1 state-right-new))
;              (= ctr-rr-left-new  (composition-rand-Left-4  state-left-new))
;              (= ctr-rr-right-new (composition-rand-Right-2 state-right-new))
;
;              ;assignment of the sampled values for the lower Key package
;              (= r-left   (__sample-rand-Left-Bits_n 3 ctr-r-left))
;              (= r-right  (__sample-rand-Right-Bits_n 1 ctr-r-right))
;              (= rr-left  (__sample-rand-Left-Bits_n 4 ctr-rr-left))
;              (= rr-right (__sample-rand-Right-Bits_n 2 ctr-rr-left))
;
;              ;assignment of the sampled values for the lower Key package as a table
;              (= (mk-some  r-left)  (select Z-left   true))
;              (= (mk-some rr-left)  (select Z-left  false))
;              (= (mk-some  r-right) (select Z-right  true))
;              (= (mk-some rr-right) (select Z-right false))
;
;              ;variable for the state of the upper/lower key package left/right before/after call
;              (= table-top-left-new   (state-Left-keys_top-T    (composition-pkgstate-Left-keys_top     state-left-new)))
;              (= table-top-right-after-EVAL (state-Right-keys_top-T    (composition-pkgstate-Right-keys_top    state-right-after-EVAL)))
;              (= table-top-right-new (state-Right-keys_top-T    (composition-pkgstate-Right-keys_top    state-right-new)))
;              (= table-bottom-left-new   (state-Left-keys_bottom-T (composition-pkgstate-Left-keys_bottom  state-left-new)))
;              (= table-bottom-right-after-EVAL (state-Right-keys_bottom-T (composition-pkgstate-Right-keys_bottom state-right-after-EVAL)))
;              (= table-bottom-right-new (state-Right-keys_bottom-T (composition-pkgstate-Right-keys_bottom state-right-new)))
;              (= table-top-left-old   (state-Left-keys_top-T    (composition-pkgstate-Left-keys_top     state-left-old)))
;              (= table-top-right-old (state-Right-keys_top-T    (composition-pkgstate-Right-keys_top    state-right-old)))
;              (= table-bottom-left-old   (state-Left-keys_bottom-T (composition-pkgstate-Left-keys_bottom  state-left-old)))
;              (= table-bottom-right-old (state-Right-keys_bottom-T (composition-pkgstate-Right-keys_bottom state-right-old)))
;
;              ;variable for the bit state of the upper/lower key package left/right before/after call
;              (= table-z-top-left-new   (state-Left-keys_top-z    (composition-pkgstate-Left-keys_top     state-left-new)))
;              (= table-z-top-right-after-EVAL (state-Right-keys_top-z    (composition-pkgstate-Right-keys_top    state-right-after-EVAL))) 
;            (= table-z-top-right-new (state-Right-keys_top-z    (composition-pkgstate-Right-keys_top    state-right-new)))
;              (= table-z-bottom-left-new   (state-Left-keys_bottom-z (composition-pkgstate-Left-keys_bottom  state-left-new)))
;              (= table-z-bottom-right-after-EVAL (state-Right-keys_bottom-z (composition-pkgstate-Right-keys_bottom state-right-after-EVAL)))
;              (= table-z-bottom-right-new (state-Right-keys_bottom-z (composition-pkgstate-Right-keys_bottom state-right-new)))
;              (= table-z-top-left-old   (state-Left-keys_top-z    (composition-pkgstate-Left-keys_top     state-left-old)))
;              (= table-z-top-right-old (state-Right-keys_top-z    (composition-pkgstate-Right-keys_top    state-right-old)))
;              (= table-z-bottom-left-old   (state-Left-keys_bottom-z (composition-pkgstate-Left-keys_bottom  state-left-old)))
;              (= table-z-bottom-right-old (state-Right-keys_bottom-z (composition-pkgstate-Right-keys_bottom state-right-old)))
;
;             ;variable for the flag state of the upper/lower key package left/right before/after call
;              (= table-flag-top-left-new   (state-Left-keys_top-flag    (composition-pkgstate-Left-keys_top     state-left-new)))
;              (= table-flag-top-right-new (state-Right-keys_top-flag    (composition-pkgstate-Right-keys_top    state-right-new)))
;              (= table-flag-bottom-left-new   (state-Left-keys_bottom-flag (composition-pkgstate-Left-keys_bottom  state-left-new)))
;              (= table-flag-bottom-right-new (state-Right-keys_bottom-flag (composition-pkgstate-Right-keys_bottom state-right-new)))
;              (= table-flag-top-left-old   (state-Left-keys_top-flag    (composition-pkgstate-Left-keys_top     state-left-old)))
;              (= table-flag-top-right-old (state-Right-keys_top-flag    (composition-pkgstate-Right-keys_top    state-right-old)))
;              (= table-flag-bottom-left-old   (state-Left-keys_bottom-flag (composition-pkgstate-Left-keys_bottom  state-left-old)))
;              (= table-flag-bottom-right-old (state-Right-keys_bottom-flag (composition-pkgstate-Right-keys_bottom state-right-old)))
;
;              ;assignment of the ctr of the sample instructions for the 8 encryptions on the left
;              (= ctr-rin-left  (composition-rand-Left-9  state-left-old))
;              (= ctr-rout-left (composition-rand-Left-11 state-left-old))
;              ; Note that the counter is increased 4 times
;
;              ;assignment of the sampled values for the 8 encryptions on the left
;              (= (rin-left false false)    (__sample-rand-Left-Bits_n 9  ctr-r-left))
;              (= (rin-left true false)     (__sample-rand-Left-Bits_n 9  (+ 1 ctr-r-left)))
;              (= (rin-left false true)     (__sample-rand-Left-Bits_n 9  (+ 2 ctr-r-left)))
;              (= (rin-left true true)      (__sample-rand-Left-Bits_n 9  (+ 3 ctr-r-left)))
;              (= (rout-left false false)   (__sample-rand-Left-Bits_n 11 ctr-r-left))
;              (= (rout-left true false)    (__sample-rand-Left-Bits_n 11 (+ 1 ctr-r-left)))
;              (= (rout-left false true)    (__sample-rand-Left-Bits_n 11 (+ 2 ctr-r-left)))
;              (= (rout-left true true)     (__sample-rand-Left-Bits_n 11 (+ 3 ctr-r-left)))
;
;              ;assignment of the ctr of the sample instructions for the 8 encryptions on the right
;              (= ctr-rin-oo-right  (composition-rand-Right-9  state-right-old))
;              (= ctr-rout-oo-right (composition-rand-Right-10 state-right-old))
;              (= ctr-rin-io-right  (composition-rand-Right-11 state-right-old))
;              (= ctr-rout-io-right (composition-rand-Right-12 state-right-old))
;              (= ctr-rin-oi-right  (composition-rand-Right-13 state-right-old))
;              (= ctr-rout-oi-right (composition-rand-Right-14 state-right-old))
;              (= ctr-rin-ii-right  (composition-rand-Right-15 state-right-old))
;              (= ctr-rout-ii-right (composition-rand-Right-16 state-right-old))
;
;              ;assignment of the sampled values for the 8 encryptions on the right
;              (= (rin-right  false false)  (__sample-rand-Right-Bits_n 9  ctr-rin-oo-right))
;              (= (rout-right false false)  (__sample-rand-Right-Bits_n 10 ctr-rout-oo-right))
;              (= (rin-right  true false)   (__sample-rand-Right-Bits_n 11 ctr-rin-io-right))
;              (= (rout-right true false)   (__sample-rand-Right-Bits_n 12 ctr-rout-io-right))
;              (= (rin-right  false true)   (__sample-rand-Right-Bits_n 13 ctr-rin-oi-right))
;              (= (rout-right false true)   (__sample-rand-Right-Bits_n 14 ctr-rout-oi-right))
;              (= (rin-right  true true)    (__sample-rand-Right-Bits_n 15 ctr-rin-ii-right))
;              (= (rout-right true true)    (__sample-rand-Right-Bits_n 16 ctr-rout-ii-right))
;
;              ;assignment of the active bit on the right
;              (= (mk-some z1) (select table-z-top-right-old l)) ;is this a cheat?
;              (= (mk-some z2) (select table-z-top-right-old r))
;
;))
;
;;(push 1)
;
;;(assert true)
;;(check-sat) ;2
;
;;(pop 1)
;
;
;
;)

; catches corner cases of tables
;
; - entries for T are mk-none or a total table (which points to Bits_n and not to none)
;
(define-fun well-defined ((T (Array Int (Maybe (Array Bool (Maybe Bits_n)))))) Bool
  (forall ((h Int))
    (ite
      (not
        (= (select T h) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
      )
      (forall ((b Bool))
        (not
          (= (select (maybe-get (select T h)) b) (as mk-none (Maybe Bits_n)))
        )
      )
      true
    )
  )
)

; captures the possible states which a Key package can be in when
; the "top" queries are GETKEYS queries 
;
(define-fun well-defined-Key-bool ((key-state State_keys)) Bool
(let ((T    (state-keys-T    key-state))
      (flag (state-keys-flag key-state))
      (z    (state-keys-z    key-state)))

;Key tables in the key packages are either completely defined or completely undefined
(well-defined T)

; flag is true <=> key has been chosen 
(and
(forall ((hhh Int)) (=
                    (not (= (select flag hhh) (mk-some true)))
                    (or
                    (= (select T hhh) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
                    (and
                    (= (select (maybe-get (select T hhh)) true) (as mk-none (Maybe Bits_n)))
                    (= (select (maybe-get (select T hhh)) false) (as mk-none (Maybe Bits_n))))
                    )))

; z table is completely undefined
(forall ((hhh Int))
(= (select T hhh) (as mk-none (Maybe (Array Bool (Maybe Bits_n))))

)
)
)))

; captures the possible states which a Key package can be in when
; the "top" queries are GETA and SETBIT queries 
;
(define-fun well-defined-Key-active ((key-state State_keys)) Bool
(let ((T    (state-keys-T    key-state))
      (flag (state-keys-flag key-state))
      (z    (state-keys-z    key-state)))

(and
; Table entries either bot or well-defined
(well-defined T)

; flag has been set => bit has been set
(forall ((hhh Int)) (ite (=  (mk-some true)  (select flag hhh))  
                (or (=  (mk-some true)  (select z hhh))
                    (=  (mk-some false) (select z hhh)))
                    true
                    ))


; key has been set => flag has been set
(forall ((hhh Int)) (ite
                    (not
                    (or
                    (= (select T hhh) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
                    (= (select (maybe-get (select T hhh)) true) (as mk-none (Maybe Bits_n)))))
                    (not
                    (= (select flag hhh) (as mk-none (Maybe Bool))))
                    true
                    ))
)))
(define-fun invariant-keys ((state-left CompositionState-Left)(state-right CompositionState-Right)) Bool


(let

; state of the key packages
(
(top-key-package-left (project-State_Left_keys_top(composition-pkgstate-Left-keys_top state-left)))
(top-key-package-right (project-State_Right_keys_top(composition-pkgstate-Right-keys_top state-right)))
(bottom-key-package-left (project-State_Left_keys_bottom (composition-pkgstate-Left-keys_bottom state-left)))
(bottom-key-package-right (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right)))
)

(let

; table of the bottom key package
(
(table-bottom-left (state-keys-T bottom-key-package-left))
(table-bottom-right (state-keys-T bottom-key-package-left))
)

(and
;top key package states are equal
;(= top-key-package-left top-key-package-left)

;for bottom key package, tables are equal
;(= table-bottom-left table-bottom-right)

;top key packages behave like a key packages
(well-defined-Key-active top-key-package-left)
(well-defined-Key-active top-key-package-right)

;bottom key packages behave like a key packages
(well-defined-Key-bool bottom-key-package-left)
(well-defined-Key-active bottom-key-package-right)

))))


(define-fun invariant-ctr ((state-left CompositionState-Left)(state-right CompositionState-Right)) Bool

(let

; counter values
(
              (ctr-rin-oo-right  (composition-rand-Right-9  state-right))
              (ctr-rout-oo-right (composition-rand-Right-10 state-right))
;assignment of the ctr of the sample instructions for the 8 encryptions on the left
              (ctr-rin-left  (composition-rand-Left-9  state-left))
              (ctr-rout-left (composition-rand-Left-11 state-left))
)


;compatibility of the counter values
(= ctr-rin-left (* 4 ctr-rin-oo-right))
(= ctr-rout-left (* 4 ctr-rout-oo-right))

)
)

(push 1)

(check-sat) ;2
;(get-model)
(pop 1)

(push 1)

(assert (and (invariant-keys state-left-old state-right-old)
             (invariant-ctr state-left-old state-right-old)
             (not is-abort-right)
             (not is-abort-left)
             (not (invariant-keys state-left-old state-right-after-EVAL))))
(check-sat) ;2
;(get-model)
(pop 1)

(push 1)

(assert (and (invariant-keys state-left-old state-right-old)
             (invariant-keys state-left-new state-right-after-EVAL)
             (invariant-ctr state-left-old state-right-old)
             (not is-abort-right)
             (not is-abort-left)
             (not (invariant-keys state-left-new state-right-new))))
(check-sat) ;2
;(get-model)
(pop 1)




(push 1)

(assert (and (invariant-keys state-left-old state-right-old)
             (invariant-ctr state-left-old state-right-old)
             (invariant-keys state-left-new state-right-new)
             (not is-abort-right)
             (not is-abort-left)
             (not (invariant-ctr state-left-new state-right-new))))
(check-sat) ;3
;(get-model)
(pop 1)

(push 1)

(assert (and (invariant-keys state-left-old state-right-old)
             (invariant-ctr state-left-old state-right-old)
             (invariant-keys state-left-new state-right-new)
             (invariant-ctr state-left-new state-right-new)
             (not is-abort-right)
             (not is-abort-left)
             (y-left y-right)
             ))
(check-sat) ;4
;(get-model)
(pop 1)
