(declare-const standard-postcondition-holds Bool)
(assert (= standard-postcondition-holds 
            (ite
            (and
            (= is-abort-right is-abort-left)
            (= is-abort-right false)
            )
            (= value-left value-right)
            true
            )
        )
)

(declare-const identical-aborts Bool)
(assert (= identical-aborts 
            (= is-abort-right is-abort-left)
            )
)


;(push 1)

;(assert true)
;(check-sat) ;6

;(pop 1)
