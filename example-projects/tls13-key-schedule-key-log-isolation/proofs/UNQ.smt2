(define-fun <relation-assume-other-invariants-game_Gks0-game_Gks0Map-UNQ> 
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-UNQ-Gks0 <OracleReturn-Gks0-<$$>-Log-<$$>-UNQ>)
        (return-UNQ-Gks0Map <OracleReturn-Gks0Map-<$$>-Log-<$$>-UNQ>)
        (n Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (and
        (updated-invariant-log-inverse old-state-Gks0 old-state-Gks0Map)
    )
)
(define-fun <relation-assume-invariant-2a-iii-game_Gks0-game_Gks0Map-UNQ> 
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-UNQ-Gks0 <OracleReturn-Gks0-<$$>-Log-<$$>-UNQ>)
        (return-UNQ-Gks0Map <OracleReturn-Gks0Map-<$$>-Log-<$$>-UNQ>)
        (n Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (assert-invariant-2a-iii old-state-Gks0 old-state-Gks0Map)
)
(define-fun <relation-assert-invariant-2a-iii-game_Gks0-game_Gks0Map-UNQ> 
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-UNQ-Gks0 <OracleReturn-Gks0-<$$>-Log-<$$>-UNQ>)
        (return-UNQ-Gks0Map <OracleReturn-Gks0Map-<$$>-Log-<$$>-UNQ>)
        (n Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (let 
        (
            (new-state-Gks0 (<oracle-return-Gks0-<$$>-Log-<$$>-UNQ-game-state> return-UNQ-Gks0))
            (new-state-Gks0Map (<oracle-return-Gks0Map-<$$>-Log-<$$>-UNQ-game-state> return-UNQ-Gks0Map))
        )
        (=>
            (and (= n KEY_dh) ((_ is mk-none) (<<func-level>> h)) (= n (<<func-name>> h)))
            (assert-invariant-2a-iii new-state-Gks0 new-state-Gks0Map)
        )
    )
)