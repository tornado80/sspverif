(declare-const standard-postcondition-holds Bool)
(assert (= standard-postcondition-holds 
            (and
            (= is-abort-right is-abort-left)
            (or 
            is-abort-left
            (= value-left value-right)
            )
            )
        )
)

