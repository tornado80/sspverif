(declare-const precondition-holds Bool)
(assert (= precondition-holds (and

;;;;;;Pre-condition (part of the invariant):

;All tables in the key packages are either completely defined or completely undefined, left, right, top, bottom
(well-defined table-top-left-old)
(well-defined table-top-right-old)
(well-defined table-bottom-left-old)
(well-defined table-bottom-right-old)

;top/bottom key packages left and right are equal (before the call)
(= table-top-left-old table-top-right-old)
(= table-bottom-left-old table-bottom-right-old)
(= table-z-top-left-old table-z-top-right-old)
(= table-z-bottom-left-old table-z-bottom-right-old)
(= table-flag-top-left-old table-flag-top-right-old)
(= table-flag-bottom-left-old table-flag-bottom-right-old)

(forall ((hhh Int)) (ite (= (mk-some true)    (select table-flag-top-left-old hhh)) 
                (or (=  (mk-some true)  (select table-z-top-left-old hhh))
                    (=  (mk-some false) (select table-z-top-left-old hhh)))
                    true
                    ))

(forall ((hhh Int)) (ite (= (mk-some true)    (select table-flag-bottom-left-old hhh)) 
                (or (=  (mk-some true)  (select table-z-bottom-left-old hhh))
                    (=  (mk-some false) (select table-z-bottom-left-old hhh)))
                    true
                    ))

(forall ((hhh Int)) (ite (= (mk-some true)    (select table-flag-top-right-old hhh)) 
                (or (=  (mk-some true)  (select table-z-top-right-old hhh))
                    (=  (mk-some false) (select table-z-top-right-old hhh)))
                    true
                    ))

(forall ((hhh Int)) (ite (= (mk-some true)    (select table-flag-bottom-right-old hhh)) 
                (or (=  (mk-some true)  (select table-z-bottom-right-old hhh))
                    (=  (mk-some false) (select table-z-bottom-right-old hhh)))
                    true
                    ))


;The randomness ctr left and right are equal (before the call)
(= ctr-r-left ctr-r-right)
(= ctr-rr-left ctr-rr-right)

;;;;;;Pre-condition (randomness mapping):
;equality of values of the sample instructions for the lower Key package
(= r-left r-right)
(= rr-left rr-right)

;;;;;; Pre-condition "Glue" 

;op is a total table.
;op is a total table.
(not (= (select op (mk-tuple2 true  true ))(as mk-none (Maybe Bool))))
(not (= (select op (mk-tuple2 true  false))(as mk-none (Maybe Bool))))
(not (= (select op (mk-tuple2 false true ))(as mk-none (Maybe Bool))))
(not (= (select op (mk-tuple2 false false))(as mk-none (Maybe Bool))))

)))

(check-sat) ;4
