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
    (randomness-mapping 
        sample-ctr-old-Gks0 
        sample-ctr-old-Gks0Map
        sample-id-Gks0
        sample-id-Gks0Map
        sample-ctr-Gks0
        sample-ctr-Gks0Map
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
        (<<func-mk_dh_handle>> X Y)
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
        (<<func-mk_dh_handle>> X Y)
    )
)

(define-fun <relation-all-invariants-before-game_Gks0-game_Gks0Map-DHEXP>
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-DHEXP-Gks0 <OracleReturn-Gks0-<$$>-DH-<$$>-DHEXP>)
        (return-DHEXP-Gks0Map <OracleReturn-Gks0Map-<$$>-Map-<$$>-DHEXP>)
        (X Bits_*)
        (Y Bits_*)
    )
    Bool
    (all-invariants old-state-Gks0 old-state-Gks0Map)
)

(define-fun <relation-all-invariants-after-game_Gks0-game_Gks0Map-DHEXP>
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-DHEXP-Gks0 <OracleReturn-Gks0-<$$>-DH-<$$>-DHEXP>)
        (return-DHEXP-Gks0Map <OracleReturn-Gks0Map-<$$>-Map-<$$>-DHEXP>)
        (X Bits_*)
        (Y Bits_*)
    )
    Bool
    (all-invariants <<game-state-game_Gks0-new-DHEXP>> <<game-state-game_Gks0Map-new-DHEXP>>)
)

(define-fun invariant
    (
        (state-Gks0 <GameState_Gks0_<$$>>)
        (state-Gks0Map <GameState_Gks0Map_<$$>>)
    )
    Bool
    ;(all-invariants state-Gks0 state-Gks0Map)
    (and 
        (invariant-1 state-Gks0 state-Gks0Map)
        (invariant-2a-v state-Gks0 state-Gks0Map)
    )
)