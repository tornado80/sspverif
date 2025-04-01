(define-fun randomness-mapping
    ( 
        (sample-ctr-old-Gks0 Int)
        (sample-ctr-old-Gks0Map Int)
        (sample-id-Gks0 Int)
        (sample-id-Gks0Map Int)
        (sample-ctr-Gks0 Int)
        (sample-ctr-Gks0Map Int)
    )
    Bool
    (or
        (and
            (= sample-ctr-Gks0 sample-ctr-old-Gks0)
            (= sample-ctr-Gks0Map sample-ctr-old-Gks0Map)
            (= sample-id-Gks0 3)
            (= sample-id-Gks0Map 3)
        )
        (and
            (= sample-ctr-Gks0 sample-ctr-old-Gks0)
            (= sample-ctr-Gks0Map sample-ctr-old-Gks0Map)
            (= sample-id-Gks0 2)
            (= sample-id-Gks0Map 2)
        )
        (and
            (= sample-ctr-Gks0 sample-ctr-old-Gks0)
            (= sample-ctr-Gks0Map sample-ctr-old-Gks0Map)
            (= sample-id-Gks0 1)
            (= sample-id-Gks0Map 1)
        )
        (and
            (= sample-ctr-Gks0 sample-ctr-old-Gks0)
            (= sample-ctr-Gks0Map sample-ctr-old-Gks0Map)
            (= sample-id-Gks0 0)
            (= sample-id-Gks0Map 0)
        )
    )
)