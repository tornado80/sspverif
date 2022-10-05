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
