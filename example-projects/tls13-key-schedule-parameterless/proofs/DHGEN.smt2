(define-fun randomness-mapping-DHGEN
    ( 
        (sample-ctr-old-Gks0 Int)
        (sample-ctr-old-Gks0Map Int)
        (sample-id-Gks0 Int)
        (sample-id-Gks0Map Int)
        (sample-ctr-Gks0 Int)
        (sample-ctr-Gks0Map Int)
    ) 
    Bool
    (and
        (= sample-ctr-Gks0 sample-ctr-old-Gks0)
        (= sample-ctr-Gks0Map sample-ctr-old-Gks0Map)
        (= sample-id-Gks0 3)
        (= sample-id-Gks0Map 3)
    )
)