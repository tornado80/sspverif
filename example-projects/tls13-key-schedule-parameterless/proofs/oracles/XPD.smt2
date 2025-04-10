(define-fun randomness-mapping-XPD
    ( 
        (sample-ctr-old-Gks0 Int)
        (sample-ctr-old-Gks0Map Int)
        (sample-id-Gks0 Int)
        (sample-id-Gks0Map Int)
        (sample-ctr-Gks0 Int)
        (sample-ctr-Gks0Map Int)
    )
    Bool
    (randomness-mapping 
        sample-ctr-old-Gks0 
        sample-ctr-old-Gks0Map
        sample-id-Gks0
        sample-id-Gks0Map
        sample-ctr-Gks0
        sample-ctr-Gks0Map
    )
)

(define-fun invariant 
    (
        (state-Gks0 <GameState_Gks0_<$$>>)
        (state-Gks0Map <GameState_Gks0Map_<$$>>)
    )
    Bool
    (and
        (invariant-1 state-Gks0 state-Gks0Map)
        (invariant-2a-v state-Gks0 state-Gks0Map)
        (invariant-log-inverse state-Gks0 state-Gks0Map)
        (invariant-consistent-log-inverse state-Gks0 state-Gks0Map)
        (invariant-2e state-Gks0 state-Gks0Map)
        (invariant-5 state-Gks0 state-Gks0Map)
    )
)