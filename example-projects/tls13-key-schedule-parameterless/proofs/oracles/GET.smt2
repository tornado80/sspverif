(define-fun randomness-mapping-GET
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

(define-fun <relation-all-invariants-before-game_Gks0-game_Gks0Map-GET> 
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-GET-Gks0 <OracleReturn-Gks0-<$$>-OutputKeyGetter-<$$>-GET>)
        (return-GET-Gks0Map <OracleReturn-Gks0Map-<$$>-Map-<$$>-GET>)
        (n Int)
        (l Int)
        (h Bits_*)
    )
    Bool
    (all-invariants old-state-Gks0 old-state-Gks0Map)
)

(define-fun <relation-all-invariants-after-game_Gks0-game_Gks0Map-GET> 
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-GET-Gks0 <OracleReturn-Gks0-<$$>-OutputKeyGetter-<$$>-GET>)
        (return-GET-Gks0Map <OracleReturn-Gks0Map-<$$>-Map-<$$>-GET>)
        (n Int)
        (l Int)
        (h Bits_*)
    )
    Bool
    (all-invariants <<game-state-game_Gks0-new-GET>> <<game-state-game_Gks0Map-new-GET>>)
)

(define-fun invariant
    (
        (state-Gks0 <GameState_Gks0_<$$>>)
        (state-Gks0Map <GameState_Gks0Map_<$$>>)
    )
    Bool
    true
    ;(all-invariants state-Gks0 state-Gks0Map)
)