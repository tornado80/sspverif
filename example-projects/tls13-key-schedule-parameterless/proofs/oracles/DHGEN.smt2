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

(define-fun <relation-all-invariants-before-game_Gks0-game_Gks0Map-DHGEN>
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-DHGEN-Gks0 <OracleReturn-Gks0-<$$>-DH-<$$>-DHGEN>)
        (return-DHGEN-Gks0Map <OracleReturn-Gks0Map-<$$>-Map-<$$>-DHGEN>)
        (group Int)
    )
    Bool
    (all-invariants old-state-Gks0 old-state-Gks0Map)
)

(define-fun <relation-all-invariants-after-game_Gks0-game_Gks0Map-DHGEN>
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-DHGEN-Gks0 <OracleReturn-Gks0-<$$>-DH-<$$>-DHGEN>)
        (return-DHGEN-Gks0Map <OracleReturn-Gks0Map-<$$>-Map-<$$>-DHGEN>)
        (group Int)
    )
    Bool
    (all-invariants <<game-state-game_Gks0-new-DHGEN>> <<game-state-game_Gks0Map-new-DHGEN>>)
)

(define-fun invariant
    (
        (state-Gks0 <GameState_Gks0_<$$>>)
        (state-Gks0Map <GameState_Gks0Map_<$$>>)
    )
    Bool
    ;(all-invariants state-Gks0 state-Gks0Map)
    (invariant-1 state-Gks0 state-Gks0Map)
)