(declare-const postcondition-holds Bool)
(assert (= postcondition-holds (and

;All tables in the key packages are either completely defined or completely undefined, left, right, top, bottom
(well-defined table-top-left-new)
(well-defined table-top-right-new)
(well-defined table-bottom-left-new)
(well-defined table-bottom-right-new)

;top/bottom key packages left and right are equal (after the call)
(= table-top-left-new table-top-right-new)
(= table-bottom-left-new table-bottom-right-new)
(= table-z-top-left-new table-z-top-right-new)
(= table-z-bottom-left-new table-z-bottom-right-new)
(= table-flag-top-left-new table-flag-top-right-new)
(= table-flag-bottom-left-new table-flag-bottom-right-new)


;The randomness ctr left and right are equal (before the call)
(= ctr-r-left-new ctr-r-right-new)
(= ctr-rr-left-new ctr-rr-right-new)

)))

;(check-sat) ;6
