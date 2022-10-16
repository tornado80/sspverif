(let (
              ;assignment of return (value,state)
              (= return-left      (oracle-Left-gate-GBLG array-state-left length-state-left handle l r op j))
              (= return-right     (oracle-Right-simgate-GBLG array-state-right length-state-right handle l r op j))

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



)