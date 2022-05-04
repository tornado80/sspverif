(declare-datatypes (
    (Tuple1 1)) (
        (par (T1) (
            (mk-tuple1 (el1 T1))
        ))
    )
)

(declare-const foo String)
(assert (= foo "foo"))

(declare-const foo_t1 (Tuple1 String))
(assert (= foo_t1 (mk-tuple1 foo)))

(declare-datatypes (
    (Tuple2 2)) (
        (par (T1 T2) (
            (mk-tuple2 (el1 T1) (el2 T2))
        ))
    )
)

(declare-const one Int)
(assert (= one 1))

(declare-const t2 (Tuple2 String Int))
(assert (= t2 (mk-tuple2 foo one)))

(declare-datatypes (
    (Tuple3 3)) (
        (par (T1 T2 T3) (
            (mk-tuple3 (el1 T1) (el2 T2) (el3 T3))
        ))
    )
)

(check-sat)
(get-model)