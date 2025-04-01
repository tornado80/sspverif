(define-fun randomness-mapping-DHEXP
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

(define-fun <relation-lemma-Gks0-output-game_Gks0-game_Gks0Map-DHEXP>
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-DHEXP-Gks0 <OracleReturn-Gks0-<$$>-DH-<$$>-DHEXP>)
        (return-DHEXP-Gks0Map <OracleReturn-Gks0Map-<$$>-Map-<$$>-DHEXP>)
        (X Bits_*)
        (Y Bits_*)
    )
    Bool
    (= 
        (return-value (<oracle-return-Gks0-<$$>-DH-<$$>-DHEXP-return-value-or-abort> return-DHEXP-Gks0))
        (<<func-proof-mk_dh_handle>> X Y)
    )
)

(define-fun <relation-lemma-Gks0Map-output-game_Gks0-game_Gks0Map-DHEXP>
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-DHEXP-Gks0 <OracleReturn-Gks0-<$$>-DH-<$$>-DHEXP>)
        (return-DHEXP-Gks0Map <OracleReturn-Gks0Map-<$$>-Map-<$$>-DHEXP>)
        (X Bits_*)
        (Y Bits_*)
    )
    Bool
    (= 
        (return-value (<oracle-return-Gks0Map-<$$>-Map-<$$>-DHEXP-return-value-or-abort> return-DHEXP-Gks0Map))
        (<<func-proof-mk_dh_handle>> X Y)
    )
)