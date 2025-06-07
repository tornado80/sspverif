(define-fun randomness-mapping-XTR
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

(define-fun <relation-lemma-Gks0-output-game_Gks0-game_Gks0Map-XTR>
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-XTR-Gks0 <OracleReturn-Gks0-<$$>-Xtr-<$$>-XTR>)
        (return-XTR-Gks0Map <OracleReturn-Gks0Map-<$$>-Map-<$$>-XTR>)
        (n Int)
        (l Int)
        (h1 Bits_*)
        (h2 Bits_*)
    )
    Bool
    (= 
        (return-value (<oracle-return-Gks0-<$$>-Xtr-<$$>-XTR-return-value-or-abort> return-XTR-Gks0))
        (<<func-mk_xtr_handle>> n h1 h2)
    )
)

(define-fun <relation-lemma-Gks0Map-output-game_Gks0-game_Gks0Map-XTR>
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-XTR-Gks0 <OracleReturn-Gks0-<$$>-Xtr-<$$>-XTR>)
        (return-XTR-Gks0Map <OracleReturn-Gks0Map-<$$>-Map-<$$>-XTR>)
        (n Int)
        (l Int)
        (h1 Bits_*)
        (h2 Bits_*)
    )
    Bool
    (= 
        (return-value (<oracle-return-Gks0Map-<$$>-Map-<$$>-XTR-return-value-or-abort> return-XTR-Gks0Map))
        (<<func-mk_xtr_handle>> n h1 h2)
    )
)

(define-fun invariant 
    (
        (state-Gks0 <GameState_Gks0_<$$>>)
        (state-Gks0Map <GameState_Gks0Map_<$$>>)
    )
    Bool
    ;(all-invariants state-Gks0 state-Gks0Map)
    (and
        (invariant-1 state-Gks0 state-Gks0Map) ; can be proved
        (invariant-2a-v state-Gks0 state-Gks0Map) ; can be proved
        (invariant-2a-vi state-Gks0 state-Gks0Map) ; can be proved
        ;(invariant-log-inverse state-Gks0 state-Gks0Map) ; didn't terminate
        ;(invariant-consistent-log-inverse state-Gks0 state-Gks0Map) ; didn't terminate
        (invariant-2e state-Gks0 state-Gks0Map) ; can be proved
        (invariant-5 state-Gks0 state-Gks0Map) ; can be proved
    )
)