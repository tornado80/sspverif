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
