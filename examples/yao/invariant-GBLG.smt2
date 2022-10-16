; layer handle:
(declare-const handle Int)

; possible input for SETBIT
(declare-const bit Bool)

; possible input for GBLG     oracle GBLG(h: Integer, l: Integer, r: Integer, op: fn Bool,Bool -> Bool, j: Integer) -> Table(Bits(p),Bool) {
(declare-const l Int)
(declare-const r Int)
(declare-const op (Array (Tuple2 Bool Bool) (Maybe Bool)))
(declare-const j Int)

; possible state
(declare-const state-left-old CompositionState-Left)
(declare-const state-right-old CompositionState-Right)
(declare-const state-right-after-EVAL CompositionState-Right)
(declare-const state-left-new CompositionState-Left)
(declare-const state-right-new CompositionState-Right)

; possible state arrays
(declare-const array-state-left-old (Array Int CompositionState-Left))
(declare-const length-state-left-old Int)
(declare-const array-state-right-old (Array Int CompositionState-Right))
(declare-const length-state-right-old Int)
(declare-const array-state-left-new (Array Int CompositionState-Left))
(declare-const length-state-left-new Int)
(declare-const array-state-right-new (Array Int CompositionState-Right))
(declare-const length-state-right-new Int)



; return value for GBLG call
(declare-const return-left Return_Left_gate_GBLG)
(declare-const return-right Return_Right_simgate_GBLG)
(declare-const is-abort-left Bool)
(declare-const is-abort-right Bool)
(declare-const value-left (Array Bits_p (Maybe Bool)))
(declare-const value-right (Array Bits_p (Maybe Bool)))

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

(declare-const table-top-left-old     (Array Int (Maybe (Array Bool (Maybe Bits_n)))))
(declare-const table-top-left-new     (Array Int (Maybe (Array Bool (Maybe Bits_n)))))
(declare-const table-bottom-left-old  (Array Int (Maybe (Array Bool (Maybe Bits_n)))))
(declare-const table-bottom-left-new  (Array Int (Maybe (Array Bool (Maybe Bits_n)))))
(declare-const table-top-right-old    (Array Int (Maybe (Array Bool (Maybe Bits_n)))))
(declare-const table-top-right-after-EVAL    (Array Int (Maybe (Array Bool (Maybe Bits_n)))))
(declare-const table-top-right-new    (Array Int (Maybe (Array Bool (Maybe Bits_n)))))
(declare-const table-bottom-right-old (Array Int (Maybe (Array Bool (Maybe Bits_n)))))
(declare-const table-bottom-right-after-EVAL (Array Int (Maybe (Array Bool (Maybe Bits_n)))))
(declare-const table-bottom-right-new (Array Int (Maybe (Array Bool (Maybe Bits_n)))))

(declare-const table-z-top-left-old     (Array Int (Maybe Bool)))
(declare-const table-z-top-left-new     (Array Int (Maybe Bool)))
(declare-const table-z-bottom-left-old  (Array Int (Maybe Bool)))
(declare-const table-z-bottom-left-new  (Array Int (Maybe Bool)))
(declare-const table-z-top-right-old    (Array Int (Maybe Bool)))
(declare-const table-z-top-right-after-EVAL    (Array Int (Maybe Bool)))
(declare-const table-z-top-right-new    (Array Int (Maybe Bool)))
(declare-const table-z-bottom-right-old (Array Int (Maybe Bool)))
(declare-const table-z-bottom-right-after-EVAL (Array Int (Maybe Bool)))
(declare-const table-z-bottom-right-new (Array Int (Maybe Bool)))

(declare-const table-flag-top-left-old     (Array Int (Maybe Bool)))
(declare-const table-flag-top-left-new     (Array Int (Maybe Bool)))
(declare-const table-flag-bottom-left-old  (Array Int (Maybe Bool)))
(declare-const table-flag-bottom-left-new  (Array Int (Maybe Bool)))
(declare-const table-flag-top-right-old    (Array Int (Maybe Bool)))
(declare-const table-flag-top-right-after-EVAL    (Array Int (Maybe Bool)))
(declare-const table-flag-top-right-new    (Array Int (Maybe Bool)))
(declare-const table-flag-bottom-right-old (Array Int (Maybe Bool)))
(declare-const table-flag-bottom-right-after-EVAL (Array Int (Maybe Bool)))
(declare-const table-flag-bottom-right-new (Array Int (Maybe Bool)))

;randomness for encryption
(declare-fun rin-right (Bool Bool) Bits_n)
(declare-fun rin-left (Bool Bool) Bits_n)
(declare-fun rout-right (Bool Bool) Bits_n)
(declare-fun rout-left (Bool Bool) Bits_n)

(declare-const ctr-rin-left Int)
(declare-const ctr-rout-left Int)
(declare-const ctr-rin-oo-right  Int)
(declare-const ctr-rout-oo-right Int)
(declare-const ctr-rin-io-right  Int)
(declare-const ctr-rout-io-right Int)
(declare-const ctr-rin-oi-right  Int)
(declare-const ctr-rout-oi-right Int)
(declare-const ctr-rin-ii-right  Int)
(declare-const ctr-rout-ii-right Int)

;active bits
(declare-const z1 Bool)
(declare-const z2 Bool)



(assert (and  ;assignment of return (value,state)
              (= return-left      (oracle-Left-gate-GBLG array-state-left-old length-state-left-old handle l r op j))
              (= return-right     (oracle-Right-simgate-GBLG array-state-right-old length-state-right-old handle l r op j))

              ;assignment of return values
              (= value-left       (return-Left-gate-GBLG-value return-left))
              (= value-right      (return-Right-simgate-GBLG-value return-right))

              ;assignment of abort values
              (= is-abort-left    (= mk-abort-Left-gate-GBLG return-left))
              (= is-abort-right   (= mk-abort-Right-simgate-GBLG return-right))

              ;assignment of return state
              (= array-state-left-new   (return-Left-gate-GBLG-state return-left))
              (= array-state-right-new  (return-Right-simgate-GBLG-state return-right))

              ;assignment of return length
              (= length-state-left-new   (return-Left-gate-GBLG-state-length return-left))
              (= length-state-right-new  (return-Right-simgate-GBLG-state-length return-right))

              ;initial state list contains only one state
              (= length-state-left-old 1)
              (= length-state-right-old 1)

              ;retrieving return state from the list
              (= (select array-state-left-old 1) state-left-old)
              (= (select array-state-right-old 1) state-right-old)
              (= (select array-state-left-new length-state-left-new) state-left-new)
              (= (select array-state-right-new length-state-right-new) state-right-new)

              (= (select array-state-right-new 5) state-right-after-EVAL)


              ;assignment of the ctr of the sample instructions for the lower Key package
              (= ctr-r-left   (composition-rand-Left-3  state-left-old))
              (= ctr-r-right  (composition-rand-Right-1 state-right-old))
              (= ctr-rr-left  (composition-rand-Left-4  state-left-old))
              (= ctr-rr-right (composition-rand-Right-2 state-right-old))

              ;assignment of the ctr of the sample instructions for the lower Key package on new state
              (= ctr-r-left-new   (composition-rand-Left-3  state-left-new))
              (= ctr-r-right-new  (composition-rand-Right-1 state-right-new))
              (= ctr-rr-left-new  (composition-rand-Left-4  state-left-new))
              (= ctr-rr-right-new (composition-rand-Right-2 state-right-new))

              ;assignment of the sampled values for the lower Key package
              (= r-left   (__sample-rand-Left-Bits_n 3 ctr-r-left))
              (= r-right  (__sample-rand-Right-Bits_n 1 ctr-r-right))
              (= rr-left  (__sample-rand-Left-Bits_n 4 ctr-rr-left))
              (= rr-right (__sample-rand-Right-Bits_n 2 ctr-rr-left))

              ;assignment of the sampled values for the lower Key package as a table
              (= (mk-some  r-left)  (select Z-left   true))
              (= (mk-some rr-left)  (select Z-left  false))
              (= (mk-some  r-right) (select Z-right  true))
              (= (mk-some rr-right) (select Z-right false))

              ;variable for the state of the upper/lower key package left/right before/after call
              (= table-top-left-new   (state-Left-keys_top-T    (composition-pkgstate-Left-keys_top     state-left-new)))
              (= table-top-right-after-EVAL (state-Right-keys_top-T    (composition-pkgstate-Right-keys_top    state-right-after-EVAL)))
              (= table-top-right-new (state-Right-keys_top-T    (composition-pkgstate-Right-keys_top    state-right-new)))
              (= table-bottom-left-new   (state-Left-keys_bottom-T (composition-pkgstate-Left-keys_bottom  state-left-new)))
              (= table-bottom-right-after-EVAL (state-Right-keys_bottom-T (composition-pkgstate-Right-keys_bottom state-right-after-EVAL)))
              (= table-bottom-right-new (state-Right-keys_bottom-T (composition-pkgstate-Right-keys_bottom state-right-new)))
              (= table-top-left-old   (state-Left-keys_top-T    (composition-pkgstate-Left-keys_top     state-left-old)))
              (= table-top-right-old (state-Right-keys_top-T    (composition-pkgstate-Right-keys_top    state-right-old)))
              (= table-bottom-left-old   (state-Left-keys_bottom-T (composition-pkgstate-Left-keys_bottom  state-left-old)))
              (= table-bottom-right-old (state-Right-keys_bottom-T (composition-pkgstate-Right-keys_bottom state-right-old)))

              ;variable for the bit state of the upper/lower key package left/right before/after call
              (= table-z-top-left-new   (state-Left-keys_top-z    (composition-pkgstate-Left-keys_top     state-left-new)))
              (= table-z-top-right-after-EVAL (state-Right-keys_top-z    (composition-pkgstate-Right-keys_top    state-right-after-EVAL))) 
            (= table-z-top-right-new (state-Right-keys_top-z    (composition-pkgstate-Right-keys_top    state-right-new)))
              (= table-z-bottom-left-new   (state-Left-keys_bottom-z (composition-pkgstate-Left-keys_bottom  state-left-new)))
              (= table-z-bottom-right-after-EVAL (state-Right-keys_bottom-z (composition-pkgstate-Right-keys_bottom state-right-after-EVAL)))
              (= table-z-bottom-right-new (state-Right-keys_bottom-z (composition-pkgstate-Right-keys_bottom state-right-new)))
              (= table-z-top-left-old   (state-Left-keys_top-z    (composition-pkgstate-Left-keys_top     state-left-old)))
              (= table-z-top-right-old (state-Right-keys_top-z    (composition-pkgstate-Right-keys_top    state-right-old)))
              (= table-z-bottom-left-old   (state-Left-keys_bottom-z (composition-pkgstate-Left-keys_bottom  state-left-old)))
              (= table-z-bottom-right-old (state-Right-keys_bottom-z (composition-pkgstate-Right-keys_bottom state-right-old)))

             ;variable for the flag state of the upper/lower key package left/right before/after call
              (= table-flag-top-left-new   (state-Left-keys_top-flag    (composition-pkgstate-Left-keys_top     state-left-new)))
              (= table-flag-top-right-new (state-Right-keys_top-flag    (composition-pkgstate-Right-keys_top    state-right-new)))
              (= table-flag-bottom-left-new   (state-Left-keys_bottom-flag (composition-pkgstate-Left-keys_bottom  state-left-new)))
              (= table-flag-bottom-right-new (state-Right-keys_bottom-flag (composition-pkgstate-Right-keys_bottom state-right-new)))
              (= table-flag-top-left-old   (state-Left-keys_top-flag    (composition-pkgstate-Left-keys_top     state-left-old)))
              (= table-flag-top-right-old (state-Right-keys_top-flag    (composition-pkgstate-Right-keys_top    state-right-old)))
              (= table-flag-bottom-left-old   (state-Left-keys_bottom-flag (composition-pkgstate-Left-keys_bottom  state-left-old)))
              (= table-flag-bottom-right-old (state-Right-keys_bottom-flag (composition-pkgstate-Right-keys_bottom state-right-old)))

              ;assignment of the ctr of the sample instructions for the 8 encryptions on the left
              (= ctr-rin-left  (composition-rand-Left-9  state-left-old))
              (= ctr-rout-left (composition-rand-Left-11 state-left-old))
              ; Note that the counter is increased 4 times

              ;assignment of the sampled values for the 8 encryptions on the left
              (= (rin-left false false)    (__sample-rand-Left-Bits_n 9  ctr-r-left))
              (= (rin-left true false)     (__sample-rand-Left-Bits_n 9  (+ 1 ctr-r-left)))
              (= (rin-left false true)     (__sample-rand-Left-Bits_n 9  (+ 2 ctr-r-left)))
              (= (rin-left true true)      (__sample-rand-Left-Bits_n 9  (+ 3 ctr-r-left)))
              (= (rout-left false false)   (__sample-rand-Left-Bits_n 11 ctr-r-left))
              (= (rout-left true false)    (__sample-rand-Left-Bits_n 11 (+ 1 ctr-r-left)))
              (= (rout-left false true)    (__sample-rand-Left-Bits_n 11 (+ 2 ctr-r-left)))
              (= (rout-left true true)     (__sample-rand-Left-Bits_n 11 (+ 3 ctr-r-left)))

              ;assignment of the ctr of the sample instructions for the 8 encryptions on the right
              (= ctr-rin-oo-right  (composition-rand-Right-9  state-right-old))
              (= ctr-rout-oo-right (composition-rand-Right-10 state-right-old))
              (= ctr-rin-io-right  (composition-rand-Right-11 state-right-old))
              (= ctr-rout-io-right (composition-rand-Right-12 state-right-old))
              (= ctr-rin-oi-right  (composition-rand-Right-13 state-right-old))
              (= ctr-rout-oi-right (composition-rand-Right-14 state-right-old))
              (= ctr-rin-ii-right  (composition-rand-Right-15 state-right-old))
              (= ctr-rout-ii-right (composition-rand-Right-16 state-right-old))

              ;assignment of the sampled values for the 8 encryptions on the right
              (= (rin-right  false false)  (__sample-rand-Right-Bits_n 9  ctr-rin-oo-right))
              (= (rout-right false false)  (__sample-rand-Right-Bits_n 10 ctr-rout-oo-right))
              (= (rin-right  true false)   (__sample-rand-Right-Bits_n 11 ctr-rin-io-right))
              (= (rout-right true false)   (__sample-rand-Right-Bits_n 12 ctr-rout-io-right))
              (= (rin-right  false true)   (__sample-rand-Right-Bits_n 13 ctr-rin-oi-right))
              (= (rout-right false true)   (__sample-rand-Right-Bits_n 14 ctr-rout-oi-right))
              (= (rin-right  true true)    (__sample-rand-Right-Bits_n 15 ctr-rin-ii-right))
              (= (rout-right true true)    (__sample-rand-Right-Bits_n 16 ctr-rout-ii-right))

              ;assignment of the active bit on the right
              (= (mk-some z1) (select table-z-top-right-old l)) ;is this a cheat?
              (= (mk-some z2) (select table-z-top-right-old r))

))

;(push 1)

;(assert true)
;(check-sat) ;2

;(pop 1)
; At each entry, the table is either none or a total table
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

(declare-const hhh Int)
(define-fun well-defined-ish ((T (Array Int (Maybe (Array Bool (Maybe Bits_n)))))(hhh Int)) Bool
    (ite
      (not
        (= (select T hhh) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
      )
      (forall ((b Bool))
        (not
          (= (select (maybe-get (select T hhh)) b) (as mk-none (Maybe Bits_n)))
        )
      )
      true
    )
  )


;(push 1)
;
;(assert true)
;(check-sat) ;3
;
;(pop 1)
(declare-const precondition-holds Bool)
(assert (= precondition-holds (and

;;;;;;Pre-condition (part of the invariant):

;All tables in the key packages are either completely defined or completely undefined, left, right, top, bottom
(well-defined table-top-left-old)
(well-defined table-top-right-old)
(well-defined table-bottom-left-old)
(well-defined table-bottom-right-old)

;top/bottom key package tables left and right are equal (before the call)
(= table-top-left-old table-top-right-old)
(= table-bottom-left-old table-bottom-right-old)

;top key z/flag tables left and right are equal (before the call)
(= table-z-top-left-old table-z-top-right-old)
(= table-flag-top-left-old table-flag-top-right-old)

;top key package: flag is set => bit is set
(forall ((hhh Int))
(ite
(= (select table-flag-top-left-old hhh) (mk-some true))
(or
(= (select table-z-top-left-old hhh) (mk-some true))
(= (select table-z-top-left-old hhh) (mk-some true))
)
true
))

;lower key package: flag has been set on left <=> bit has been set on right
(forall ((hhh Int))
(=
(= (select table-flag-bottom-left-old hhh) (mk-some true))
   (or
   (= (select table-z-bottom-right-old hhh) (mk-some true))
   (= (select table-z-bottom-right-old hhh) (mk-some false))
   )
)
)


;lower key z table left are completely undefined 
(forall ((hhh Int))
(= (select table-z-bottom-left-old hhh) (as mk-none (Maybe Bool))))

; top Key package and bottom key package right
; flag has been set => bit has been set
; key has been set => flag has been set

(forall ((hhh Int)) (ite (=  (mk-some true)  (select table-flag-top-left-old hhh))  
                (or (=  (mk-some true)  (select table-z-top-left-old hhh))
                    (=  (mk-some false) (select table-z-top-left-old hhh)))
                    true
                    ))

(forall ((hhh Int)) (ite (=  (mk-some true) (select table-flag-top-right-old hhh))  
                (or (=  (mk-some true)  (select table-z-top-right-old hhh))
                    (=  (mk-some false) (select table-z-top-right-old hhh)))
                    true
                    ))

(forall ((hhh Int)) (ite (=  (mk-some true)  (select table-flag-bottom-right-old hhh))  
                (or (=  (mk-some true)  (select table-z-bottom-right-old hhh))
                    (=  (mk-some false) (select table-z-bottom-right-old hhh)))
                    true
                    ))

(forall ((hhh Int)) (ite
                    (or
                    (= (select table-top-left-old hhh) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
                    (= (select (maybe-get (select table-top-left-old hhh)) true) (as mk-none (Maybe Bits_n))))
                    (= (select table-flag-top-left-old hhh) (as mk-none (Maybe Bool)))
                    true
                    ))

(forall ((hhh Int)) (ite
                    (or
                    (= (select table-top-right-old hhh) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
                    (= (select (maybe-get (select table-top-right-old hhh)) true) (as mk-none (Maybe Bits_n))))
                    (= (select table-flag-top-right-old hhh) (as mk-none (Maybe Bool)))
                    true
                    ))

(forall ((hhh Int)) (ite
                    (or
                    (= (select table-bottom-right-old hhh) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
                    (= (select (maybe-get (select table-bottom-right-old hhh)) true) (as mk-none (Maybe Bits_n))))
                    (= (select table-flag-bottom-right-old hhh) (as mk-none (Maybe Bool)))
                    true
                    ))



; Bottom Key package
; key has been set <=> flag has been set

(forall ((hhh Int)) (=
                    (= (select table-flag-bottom-left-old hhh)
                       (as mk-none (Maybe Bool)))
                    (or
                    (= (select table-bottom-left-old hhh) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
                    (= (select (maybe-get (select table-bottom-left-old hhh)) true) (as mk-none (Maybe Bits_n))))))



;The randomness ctr left and right are equal (before the call)
(= ctr-r-left ctr-r-right)
(= ctr-rr-left ctr-rr-right)

;;;;;;Pre-condition (randomness mapping):
;equality of values of the sample instructions for the lower Key package
(= r-left r-right)
(= rr-left rr-right)

;compatibility of the counter values
(= ctr-rin-left (* 4 ctr-rin-oo-right))
(= ctr-rout-left (* 4 ctr-rout-oo-right))


;equality of values of the sample instructions for the encryptions
(forall ((b1 Bool) (b2 Bool))
(and
(= (rin-left b1 b2) (rin-right (xor b1 z1) (xor b2 z2)))
(= (rin-left b1 b2) (rout-right (xor b1 z1) (xor b2 z2)))
))

;;;;;; Pre-condition "Glue" 

;op is a total table.
(not (= (select op (mk-tuple2 true  true ))(as mk-none (Maybe Bool))))
(not (= (select op (mk-tuple2 true  false))(as mk-none (Maybe Bool))))
(not (= (select op (mk-tuple2 false true ))(as mk-none (Maybe Bool))))
(not (= (select op (mk-tuple2 false false))(as mk-none (Maybe Bool))))

)))

;(push 1)

;(assert true)
;(check-sat) ;4

;(pop 1)
(declare-const lemmas-hold Bool)
(declare-const lemma1 Bool)
(declare-const lemma2 Bool)
(declare-const lemma3 Bool)
(declare-const lemma4 Bool)
(declare-const lemma5 Bool)

(assert (= lemmas-hold (and
lemma1
lemma2
lemma3
lemma4
lemma5)))

(assert (= lemma1 (and
;;;; Lemma on key tables
(well-defined table-top-left-new)
(well-defined table-top-right-after-EVAL)
(well-defined table-top-right-new)
(well-defined table-bottom-left-new)
(well-defined table-bottom-right-after-EVAL)
(well-defined table-bottom-right-new)
)))

(declare-const debug-top-left Bool)
(declare-const debug-top-right Bool)
(declare-const debug-bottom-left Bool)
(declare-const debug-bottom-right Bool)

(assert 
(and
(= (well-defined table-top-left-new) debug-top-left)
(= (well-defined table-top-right-new) debug-top-right)
(= (well-defined-ish table-bottom-left-new hhh) debug-bottom-left)
(= (well-defined-ish table-bottom-right-new hhh) debug-bottom-right)
))





(assert (= lemma2 (and
; top tables remain the same
(= table-top-left-old table-top-left-new)
(= table-top-right-after-EVAL table-top-right-new)
(= table-top-right-old table-top-right-new)
)))

(assert (= lemma3 (and
; left: bottom tables are mostly equal and where they are not equal, there is Z
(forall ((hh Int))
(ite
(not
(and (= j hh) (= (select table-bottom-left-old hh) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))))
;(= (select table-bottom-left-new hh) (mk-some Z-left))
(= (select table-bottom-left-old hh) (select table-bottom-left-new hh))
true
))
)))

;(declare-const hhh Int)

(assert (= lemma4 (and
; right: bottom tables are mostly equal and where they are not equal, there is Z
(forall ((hh Int))
(ite
(and (= j hh) (= (select table-bottom-right-old hh) (as mk-none (Maybe (Array Bool (Maybe Bits_n))))))
(= (select table-bottom-right-new hh) (mk-some Z-right))
(= (select table-bottom-right-old hh) (select table-bottom-right-new hh))
))
))
)

;(push 1)

;(assert true)
;(check-sat) ;5

;(pop 1)

(declare-const postcondition-holds Bool)
(assert (= postcondition-holds (and

;All tables in the key packages are either completely defined or completely undefined, left, right, top, bottom
(well-defined table-top-left-new)
(well-defined table-top-right-new)
(well-defined table-bottom-left-new)
(well-defined table-bottom-right-new)

;top/bottom key package tables left and right are equal (before the call)
(= table-top-left-new table-top-right-new)
(= table-bottom-left-new table-bottom-right-new)

;top key z/flag tables left and right are equal (before the call)
(= table-z-top-left-new table-z-top-right-new)
(= table-flag-top-left-new table-flag-top-right-new)

(forall ((hhh Int))
(ite
(= (select table-flag-top-left-new hhh) (mk-some true))
(or
(= (select table-z-top-left-new hhh) (mk-some true))
(= (select table-z-top-left-new hhh) (mk-some true))
)
true
))

;lower key package: flag has been set on left <=> bit has been set on right
(forall ((hhh Int))
(=
(= (select table-flag-bottom-left-new hhh) (mk-some true))
   (or
   (= (select table-z-bottom-right-new hhh) (mk-some true))
   (= (select table-z-bottom-right-new hhh) (mk-some false))
    )
)
)

;lower key z table left are completely undefined 
(forall ((hhh Int))
(= (select table-z-bottom-left-new hhh) (as mk-none (Maybe Bool))))

; top Key package and bottom key package right
; flag has been set => bit has been set
; key has been set => flag has been set

(forall ((hhh Int)) (ite (=  (mk-some true)  (select table-flag-top-left-new hhh))  
                (or (=  (mk-some true)  (select table-z-top-left-new hhh))
                    (=  (mk-some false) (select table-z-top-left-new hhh)))
                    true
                    ))

(forall ((hhh Int)) (ite (=  (mk-some true) (select table-flag-top-right-new hhh))  
                (or (=  (mk-some true)  (select table-z-top-right-new hhh))
                    (=  (mk-some false) (select table-z-top-right-new hhh)))
                    true
                    ))

(forall ((hhh Int)) (ite (=  (mk-some true)  (select table-flag-bottom-right-new hhh))  
                (or (=  (mk-some true)  (select table-z-bottom-right-new hhh))
                    (=  (mk-some false) (select table-z-bottom-right-new hhh)))
                    true
                    ))

(forall ((hhh Int)) (ite
                    (or
                    (= (select table-top-left-new hhh) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
                    (= (select (maybe-get (select table-top-left-new hhh)) true) (as mk-none (Maybe Bits_n))))
                    (= (select table-flag-top-left-new hhh) (as mk-none (Maybe Bool)))
                    true
                    ))

(forall ((hhh Int)) (ite
                    (or
                    (= (select table-top-right-new hhh) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
                    (= (select (maybe-get (select table-top-right-new hhh)) true) (as mk-none (Maybe Bits_n))))
                    (= (select table-flag-top-right-new hhh) (as mk-none (Maybe Bool)))
                    true
                    ))

(forall ((hhh Int)) (ite
                    (or
                    (= (select table-bottom-right-new hhh) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
                    (= (select (maybe-get (select table-bottom-right-new hhh)) true) (as mk-none (Maybe Bits_n))))
                    (= (select table-flag-bottom-right-new hhh) (as mk-none (Maybe Bool)))
                    true
                    ))



; Bottom Key package
; key has been set <=> flag has been set

(forall ((hhh Int)) (=
                    (= (select table-flag-bottom-left-new hhh)
                       (as mk-none (Maybe Bool)))
                    (or
                    (= (select table-bottom-left-new hhh) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
                    (= (select (maybe-get (select table-bottom-left-new hhh)) true) (as mk-none (Maybe Bits_n))))))



;The randomness ctr left and right are equal (before the call)
(= ctr-r-left-new ctr-r-right-new)
(= ctr-rr-left-new ctr-rr-right-new)

)))
;(declare-const standard-postcondition-holds Bool)
;(assert (= standard-postcondition-holds 
;            (= value-left value-right))
;)

;(declare-const identical-aborts Bool)
;(assert (= identical-aborts 
;            (= is-abort-right is-abort-left)
;            )
;)


;(push 1)

;(assert true)
;(check-sat) ;6

;(pop 1)
;;;;;;;;;;;; High-level goal
; pre-condition => (1) left-abort <=> right-abort
;                  (2) if no abort =>
;                               (a) pre-condition as post-condition
;                               (b) y-left = y-right
;(push 1)
;(assert precondition-holds)
;(check-sat) ;7
;(pop 1)
(push 1)

(assert (and precondition-holds
             (not is-abort-right)
             (not is-abort-left)
             (not lemma1)))
(check-sat) ;2 ;4 ;8
;(get-model)
(pop 1)





(push 1)

(assert (and precondition-holds
             lemma1
             (not is-abort-right)
             (not is-abort-left)
             (not lemma2)))
(check-sat) ;3 ;5 ;9
;(get-model)
(pop 1)

(push 1)
(assert (and precondition-holds
             lemma1
             lemma2
             (not is-abort-right)
             (not is-abort-left)
             (not lemma3)))
(check-sat) ;4 ;6 ;10
;(get-model)
(pop 1)

(push 1)
(assert (and precondition-holds
             lemma1
             lemma2
             lemma3
             (not is-abort-right)
             (not is-abort-left)
             (not lemma4)))
(check-sat) ;5 ;7 ;11
;(get-model)
(pop 1)

(push 1)


;pre-condition + lemmas => post-condition
(assert (and precondition-holds
             lemmas-hold
             (not is-abort-right)
             (not is-abort-left)
             (not postcondition-holds)))

(check-sat) ;6  ;12
;(get-model)
(pop 1)

(push 1)

;pre-condition + lemmas => standard post-condition
(assert (and precondition-holds 
             lemmas-hold
             postcondition-holds
             (not is-abort-right)
             (not is-abort-left)
             (not (= value-left value-right))))
(check-sat) ;7  ;13
(pop 1)

(push 1)
(assert (and precondition-holds
             is-abort-left
        (not is-abort-right))
)


(check-sat) ;8
;(get-model)
(pop 1)

(push 1)
(assert (and precondition-holds
             (or
 (= (select table-flag-top-right-old l) (as mk-none (Maybe Bool)))
 (= (select table-flag-top-right-old l) (mk-some false))
 (= (select table-flag-top-right-old r) (as mk-none (Maybe Bool)))
 (= (select table-flag-top-right-old r) (mk-some false))
             )
        (not is-abort-left))
)

(check-sat) ;9
;(get-model)
(pop 1)

(push 1)
(assert (and precondition-holds
        (not  (or
 (= (select table-flag-top-right-old l) (as mk-none (Maybe Bool)))
 (= (select table-flag-top-right-old l) (mk-some false))
 (= (select table-flag-top-right-old r) (as mk-none (Maybe Bool)))
 (= (select table-flag-top-right-old r) (mk-some false))
             ))
(or
 (= (select table-z-bottom-right-old j) (mk-some true))
 (= (select table-z-bottom-right-old j) (mk-some false))
)
             is-abort-right
        (not is-abort-left))
)

(check-sat) ;10
;(get-model)
(pop 1)

(push 1)

(assert (and precondition-holds
        (not  (or
 (= (select table-flag-top-right-old l) (as mk-none (Maybe Bool)))
 (= (select table-flag-top-right-old l) (mk-some false))
 (= (select table-z-top-right-old l) (as mk-none (Maybe Bool)))
 (= (select table-flag-top-right-old r) (as mk-none (Maybe Bool)))
 (= (select table-flag-top-right-old r) (mk-some false))
 (= (select table-z-top-right-old r) (as mk-none (Maybe Bool)))
 (= (select table-z-bottom-right-old j) (mk-some true))
 (= (select table-z-bottom-right-old j) (mk-some false))
        ))
 (= (select table-z-bottom-right-after-EVAL j) (as mk-none (Maybe Bool)))
        )
)




(check-sat) ;11
;(get-model)
(pop 1)

(push 1)

(assert (and precondition-holds
        (not  (or
 (= (select table-flag-top-right-old l) (as mk-none (Maybe Bool)))
 (= (select table-flag-top-right-old l) (mk-some false))
 (= (select table-z-top-right-old l) (as mk-none (Maybe Bool)))
 (= (select table-flag-top-right-old r) (as mk-none (Maybe Bool)))
 (= (select table-flag-top-right-old r) (mk-some false))
 (= (select table-z-top-right-old r) (as mk-none (Maybe Bool)))
 (= (select table-z-bottom-right-old j) (mk-some true))
 (= (select table-z-bottom-right-old j) (mk-some false))
        ))
             is-abort-right
        )
)

(check-sat) ;12
;(get-model)
(pop 1)


(push 1)
(assert (and precondition-holds
        (not  (or
 (= (select table-flag-top-right-old l) (as mk-none (Maybe Bool)))
 (= (select table-flag-top-right-old l) (mk-some false))
 (= (select table-flag-top-right-old r) (as mk-none (Maybe Bool)))
 (= (select table-flag-top-right-old r) (mk-some false))
 (= (select table-z-bottom-right-old j) (mk-some true))
 (= (select table-z-bottom-right-old j) (mk-some false))
        ))
             is-abort-right
        (not is-abort-left))
)

(check-sat) ;13
;(get-model)
(pop 1)
