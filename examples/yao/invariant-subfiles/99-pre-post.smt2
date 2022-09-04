(assert and

;;;;;;Pre-condition (part of the invariant):

;All tables in the key packages are either completely defined or completely undefined, left, right, top, bottom
(well-defined table-top-left-old)
(well-defined table-top-right-old)
(well-defined table-bottom-left-old)
(well-defined table-bottom-right-old)

;top/bottom key packages left and right are equal (before the call)
(= table-top-left-old table-top-right-old)
(= table-bottom-left-old table-bottom-right-old)

;The randomness ctr left and right are equal (before the call)
(= ctr-r-left ctr-r-right)
(= ctr-rr-left ctr-rr-right)

;;;;;;Pre-condition (randomness mapping):
;equality of values of the sample instructions for the lower Key package
(= r-left r-right)
(= rr-left rr-right)

;;;;;; Pre-condition "Glue" 

;op is a total table.
(not (= none op true true))




;;;;;Lemmata

;After a call to GBLG, the new top key package is identical to the old top key package, left, right



After a call to GBLG, the new bottom key package is identical to the old bottom key package except for position handle, left, right
After a call to GBLG, the new bottom key package at position handle is equal to the old bottom key package (if that was defined before) OR is equal to the randomness value, left, right
Post-condition:

pre-condition on new state
abort values left and right are identical
return values left and right are identical

; closing bracket of the assert
)