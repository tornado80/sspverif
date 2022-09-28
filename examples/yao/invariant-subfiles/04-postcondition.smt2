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

;lower key z/flag table left are completely undefined 
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
