(define-fun randomness-mapping-PKGEN
    ( 
        (sample-ctr-old-monolithic_pke_cca_game Int)
        (sample-ctr-old-modular_pke_cca_game_with_real_kem Int)
        (sample-id-monolithic_pke_cca_game Int)
        (sample-id-modular_pke_cca_game_with_real_kem Int)
        (sample-ctr-monolithic_pke_cca_game Int)
        (sample-ctr-modular_pke_cca_game_with_real_kem Int)
    )
    Bool
    (or
        (and
            (= sample-ctr-monolithic_pke_cca_game sample-ctr-old-monolithic_pke_cca_game)
            (= sample-ctr-modular_pke_cca_game_with_real_kem sample-ctr-old-modular_pke_cca_game_with_real_kem)
            (= sample-id-monolithic_pke_cca_game 0)
            (= sample-id-modular_pke_cca_game_with_real_kem 0)
        )
        ;(and
        ;    (= sample-ctr-monolithic_pke_cca_game sample-ctr-old-monolithic_pke_cca_game)
        ;    (= sample-ctr-modular_pke_cca_game_with_real_kem sample-ctr-old-modular_pke_cca_game_with_real_kem)
        ;    (= sample-id-monolithic_pke_cca_game 1)
        ;    (= sample-id-modular_pke_cca_game_with_real_kem 1)
        ;)
    )
)

(define-fun randomness-mapping-PKENC
    ( 
        (sample-ctr-old-monolithic_pke_cca_game Int)
        (sample-ctr-old-modular_pke_cca_game_with_real_kem Int)
        (sample-id-monolithic_pke_cca_game Int)
        (sample-id-modular_pke_cca_game_with_real_kem Int)
        (sample-ctr-monolithic_pke_cca_game Int)
        (sample-ctr-modular_pke_cca_game_with_real_kem Int)
    )
    Bool
    false
)

(define-fun invariant
    (
        (state-monolithic_pke_cca_game <GameState_MonolithicPkeCcaGame_<$<!b!>$>>)
        (state-modular_pke_cca_game_with_real_kem <GameState_ModularPkeCcaGame_<$<!false!><!b!>$>>)
    )
    Bool
    true
)