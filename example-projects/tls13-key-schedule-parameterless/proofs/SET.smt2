(define-fun randomness-mapping-SET
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

(define-fun <relation-lemma-Gks0-output-game_Gks0-game_Gks0Map-SET>
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-SET-Gks0 <OracleReturn-Gks0-<$$>-ExternalPskSetter-<$$>-SET>)
        (return-SET-Gks0Map <OracleReturn-Gks0Map-<$$>-Map-<$$>-SET>)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (= 
        (return-value (<oracle-return-Gks0-<$$>-ExternalPskSetter-<$$>-SET-return-value-or-abort> return-SET-Gks0))
        h
    )
)

(define-fun <relation-lemma-Gks0Map-output-game_Gks0-game_Gks0Map-SET>
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-SET-Gks0 <OracleReturn-Gks0-<$$>-ExternalPskSetter-<$$>-SET>)
        (return-SET-Gks0Map <OracleReturn-Gks0Map-<$$>-Map-<$$>-SET>)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (= 
        (return-value (<oracle-return-Gks0Map-<$$>-Map-<$$>-SET-return-value-or-abort> return-SET-Gks0Map))
        h
    )
)

(define-fun <relation-lemma-Q-does-not-abort-game_Gks0-game_Gks0Map-SET>
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-SET-Gks0 <OracleReturn-Gks0-<$$>-ExternalPskSetter-<$$>-SET>)
        (return-SET-Gks0Map <OracleReturn-Gks0Map-<$$>-Map-<$$>-SET>)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (forall 
        (
            (state-Gks0 <GameState_Gks0_<$$>>)
            (state-Gks0Map <GameState_Gks0Map_<$$>>)
            (consts-Gks0 <GameConsts_Gks0>)
            (consts-Gks0Map <GameConsts_Gks0Map>)
            (n Int)
            (h Bits_*)
        )
        (and
            (not (= (as mk-abort (ReturnValue (Maybe Bits_*))) (<oracle-return-Gks0-<$$>-Log-<$$>-Q-return-value-or-abort> 
                (<oracle-Gks0-<$$>-Log-<$$>-Q> state-Gks0 consts-Gks0 n h)
            )))
            (not (= (as mk-abort (ReturnValue (Maybe Bits_*))) (<oracle-return-Gks0Map-<$$>-Log-<$$>-Q-return-value-or-abort> 
                (<oracle-Gks0Map-<$$>-Log-<$$>-Q> state-Gks0Map consts-Gks0Map n h)
            )))
        )
    )
)

(define-fun <relation-lemma-if-left-aborts-right-also-aborts-game_Gks0-game_Gks0Map-SET> 
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-SET-Gks0 <OracleReturn-Gks0-<$$>-ExternalPskSetter-<$$>-SET>)
        (return-SET-Gks0Map <OracleReturn-Gks0Map-<$$>-Map-<$$>-SET>)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (=>
        (=
            (as mk-abort (ReturnValue Bits_*))
            (<oracle-return-Gks0-<$$>-ExternalPskSetter-<$$>-SET-return-value-or-abort> return-SET-Gks0)
        )
        (=
            (as mk-abort (ReturnValue Bits_*))
            (<oracle-return-Gks0Map-<$$>-Map-<$$>-SET-return-value-or-abort> return-SET-Gks0Map)
        )
    )

)



(define-fun <relation-lemma-rand-is-eq-game_Gks0-game_Gks0Map-SET> 
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-SET-Gks0 <OracleReturn-Gks0-<$$>-ExternalPskSetter-<$$>-SET>)
        (return-SET-Gks0Map <OracleReturn-Gks0Map-<$$>-Map-<$$>-SET>)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (and
        (rand-is-eq 0 0 (<game-Gks0-<$$>-rand-0> old-state-Gks0) (<game-Gks0Map-<$$>-rand-0> old-state-Gks0Map))
        (rand-is-eq 1 1 (<game-Gks0-<$$>-rand-1> old-state-Gks0) (<game-Gks0Map-<$$>-rand-1> old-state-Gks0Map))
        (rand-is-eq 2 2 (<game-Gks0-<$$>-rand-2> old-state-Gks0) (<game-Gks0Map-<$$>-rand-2> old-state-Gks0Map))
    )

)

(define-fun <relation-lemma-randomness-mapping-game_Gks0-game_Gks0Map-SET> 
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-SET-Gks0 <OracleReturn-Gks0-<$$>-ExternalPskSetter-<$$>-SET>)
        (return-SET-Gks0Map <OracleReturn-Gks0Map-<$$>-Map-<$$>-SET>)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (and
        (randomness-mapping-SET (<game-Gks0-<$$>-rand-0> old-state-Gks0) (<game-Gks0Map-<$$>-rand-0> old-state-Gks0Map) 0 0 (<game-Gks0-<$$>-rand-0> old-state-Gks0) (<game-Gks0Map-<$$>-rand-0> old-state-Gks0Map))
        (randomness-mapping-SET (<game-Gks0-<$$>-rand-1> old-state-Gks0) (<game-Gks0Map-<$$>-rand-1> old-state-Gks0Map) 1 1 (<game-Gks0-<$$>-rand-1> old-state-Gks0) (<game-Gks0Map-<$$>-rand-1> old-state-Gks0Map))
        (randomness-mapping-SET (<game-Gks0-<$$>-rand-2> old-state-Gks0) (<game-Gks0Map-<$$>-rand-2> old-state-Gks0Map) 2 2 (<game-Gks0-<$$>-rand-2> old-state-Gks0) (<game-Gks0Map-<$$>-rand-2> old-state-Gks0Map))
    )
)