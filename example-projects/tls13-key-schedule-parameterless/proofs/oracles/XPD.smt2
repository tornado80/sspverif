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

(define-fun <relation-lemma-Gks0-output-game_Gks0-game_Gks0Map-XPD>
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-XPD-Gks0 <OracleReturn-Gks0-<$$>-Check-<$$>-XPD>)
        (return-XPD-Gks0Map <OracleReturn-Gks0Map-<$$>-Check-<$$>-XPD>)
        (n Int)
        (l Int)
        (h Bits_*)
        (r Bool)
        (args Bits_*)
    )
    Bool
    (= 
        (return-value (<oracle-return-Gks0-<$$>-Check-<$$>-XPD-return-value-or-abort> return-XPD-Gks0))
        (<<func-mk_xpd_handle>> n (<<func-label1>> n r) h args)
    )
)

(define-fun <relation-lemma-Gks0Map-output-game_Gks0-game_Gks0Map-XPD>
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-XPD-Gks0 <OracleReturn-Gks0-<$$>-Check-<$$>-XPD>)
        (return-XPD-Gks0Map <OracleReturn-Gks0Map-<$$>-Check-<$$>-XPD>)
        (n Int)
        (l Int)
        (h Bits_*)
        (r Bool)
        (args Bits_*)
    )
    Bool
    (= 
        (return-value (<oracle-return-Gks0Map-<$$>-Check-<$$>-XPD-return-value-or-abort> return-XPD-Gks0Map))
        (<<func-mk_xpd_handle>> n (<<func-label1>> n r) h args)
    )
)

(define-fun invariant 
    (
        (state-Gks0 <GameState_Gks0_<$$>>)
        (state-Gks0Map <GameState_Gks0Map_<$$>>)
    )
    Bool
    (invariant-2a-v state-Gks0 state-Gks0Map)
    ;(all-invariants state-Gks0 state-Gks0Map)
)