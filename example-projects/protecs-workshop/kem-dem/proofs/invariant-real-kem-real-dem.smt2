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
            (= sample-id-modular_pke_cca_game_with_real_kem 2)
        )
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
    (or
        (and
            (= sample-ctr-monolithic_pke_cca_game sample-ctr-old-monolithic_pke_cca_game)
            (= sample-ctr-modular_pke_cca_game_with_real_kem sample-ctr-old-modular_pke_cca_game_with_real_kem)
            (= sample-id-monolithic_pke_cca_game 2)
            (= sample-id-modular_pke_cca_game_with_real_kem 1)
        )
        (and
            (= sample-ctr-monolithic_pke_cca_game sample-ctr-old-monolithic_pke_cca_game)
            (= sample-ctr-modular_pke_cca_game_with_real_kem sample-ctr-old-modular_pke_cca_game_with_real_kem)
            (= sample-id-monolithic_pke_cca_game 1)
            (= sample-id-modular_pke_cca_game_with_real_kem 3)
        )
    )
)

(define-fun invariant
    (
        (state-left <GameState_MonolithicPkeCcaGame_<$<!false!>$>>) ; left
        (state-right <GameState_ModularPkeCcaGame_<$<!false!><!false!>$>>) ; right
    )
    Bool
    (let
        (
            (left_pk (<pkg-state-MON_CCA-<$<!b!>$>-pk> (<game-MonolithicPkeCcaGame-<$<!false!>$>-pkgstate-pkg_MON_CCA> state-left)))
            (left_sk (<pkg-state-MON_CCA-<$<!b!>$>-sk> (<game-MonolithicPkeCcaGame-<$<!false!>$>-pkgstate-pkg_MON_CCA> state-left)))
            (right_pk_mod_cca (<pkg-state-MOD_CCA-<$$>-pk> (<game-ModularPkeCcaGame-<$<!false!><!false!>$>-pkgstate-pkg_MOD_CCA> state-right)))
            (right_pk_kem (<pkg-state-KEM-<$$>-pk> (<game-ModularPkeCcaGame-<$<!false!><!false!>$>-pkgstate-pkg_KEM> state-right)))
            (left_c (<pkg-state-MON_CCA-<$<!b!>$>-c> (<game-MonolithicPkeCcaGame-<$<!false!>$>-pkgstate-pkg_MON_CCA> state-left)))
            (right_c (<pkg-state-MOD_CCA-<$$>-c> (<game-ModularPkeCcaGame-<$<!false!><!false!>$>-pkgstate-pkg_MOD_CCA> state-right)))
            (right_kem_ek (<pkg-state-KEM-<$$>-ek> (<game-ModularPkeCcaGame-<$<!false!><!false!>$>-pkgstate-pkg_KEM> state-right)))
            (right_mod_cca_ek (<pkg-state-MOD_CCA-<$$>-ek> (<game-ModularPkeCcaGame-<$<!false!><!false!>$>-pkgstate-pkg_MOD_CCA> state-right)))
            (right_dem_c (<pkg-state-DEM-<$<!dem_idealization!>$>-c> (<game-ModularPkeCcaGame-<$<!false!><!false!>$>-pkgstate-pkg_DEM> state-right)))
            (right_key_k (<pkg-state-Key-<$<!key_idealization!>$>-k> (<game-ModularPkeCcaGame-<$<!false!><!false!>$>-pkgstate-pkg_Key> state-right)))
            (right_sk (<pkg-state-KEM-<$$>-sk> (<game-ModularPkeCcaGame-<$<!false!><!false!>$>-pkgstate-pkg_KEM> state-right)))
            (right_encaps_randomness (<pkg-state-KEM-<$$>-encaps_randomness> (<game-ModularPkeCcaGame-<$<!false!><!false!>$>-pkgstate-pkg_KEM> state-right)))
        )
        (and
            (= left_pk right_pk_mod_cca right_pk_kem) ; left_pk = right_pk
            (= ((_ is mk-none) left_pk) ((_ is mk-none) left_sk) ((_ is mk-none) right_pk_mod_cca) ((_ is mk-none) right_pk_kem) ((_ is mk-none) right_sk)) ; left_pk = None iff right_pk = None
            (= left_c right_c) ; left_challenge_ciphertext = right_challenge_ciphertext
            (= ((_ is mk-none) right_encaps_randomness) ((_ is mk-none) left_c) ((_ is mk-none) right_c) ((_ is mk-none) right_kem_ek) ((_ is mk-none) right_mod_cca_ek) ((_ is mk-none) right_dem_c) ((_ is mk-none) right_key_k)) ; left_challenge_ciphertext = None iff right_challenge_ciphertext = None iff right_encapsulation_challenge = None iff right_dem_challenge = None iff right_key_k = None
            (= left_sk right_sk) ; left_sk = right_sk
            (= right_mod_cca_ek right_kem_ek) ; right encapsulated keys
            (=> ((_ is mk-none) right_pk_kem) ((_ is mk-none) right_c)) ; if PKGEN is not called, PKENC can not be called
            (=>
                (not ((_ is mk-none) right_c))
                (= (maybe-get right_c) (mk-tuple2 (maybe-get right_mod_cca_ek) (maybe-get right_dem_c)))
            )
            (=>
                (not ((_ is mk-none) right_key_k))
                (and
                    (= (maybe-get right_key_k) (el2-1 (<<func-proof-kem_encaps>> (maybe-get right_encaps_randomness) (maybe-get right_pk_kem))))
                    (= (maybe-get right_kem_ek) (el2-2 (<<func-proof-kem_encaps>> (maybe-get right_encaps_randomness) (maybe-get right_pk_kem))))
                )
            )
        )
    )
)

(define-fun <relation-lemma-kem-correctness-monolithic_pke_cca_real_game-modular_pke_cca_game_with_real_kem-PKDEC>
    (
        (old-state-left <GameState_MonolithicPkeCcaGame_<$<!false!>$>>)
        (old-state-right <GameState_ModularPkeCcaGame_<$<!false!><!false!>$>>)
        (return-left <OracleReturn-MonolithicPkeCcaGame-<$<!false!>$>-MON_CCA-<$<!b!>$>-PKDEC>)
        (return-right <OracleReturn-ModularPkeCcaGame-<$<!false!><!false!>$>-MOD_CCA-<$$>-PKDEC>)
        (ek_ctxt (Tuple2 Bits_400 Bits_*))
    )
    Bool
    (let
        (
            (pk (<pkg-state-KEM-<$$>-pk> (<game-ModularPkeCcaGame-<$<!false!><!false!>$>-pkgstate-pkg_KEM> old-state-right)))
            (sk (<pkg-state-KEM-<$$>-sk> (<game-ModularPkeCcaGame-<$<!false!><!false!>$>-pkgstate-pkg_KEM> old-state-right)))
        )
        (=>
            (not ((_ is mk-none) pk))
            (forall 
                (
                    (r Bits_3000)
                )
                (let
                    (
                        (k (el2-1 (<<func-proof-kem_encaps>> r (maybe-get pk))))
                        (ek (el2-2 (<<func-proof-kem_encaps>> r (maybe-get pk))))
                    )
                    (= k (<<func-proof-kem_decaps>> (maybe-get sk) ek))
                )
            )
        )
    )
)

(define-fun <relation-lemma-rand-is-eq-monolithic_pke_cca_game-modular_pke_cca_game_with_real_kem-PKENC>
    (
        (old-state-left <GameState_MonolithicPkeCcaGame_<$<!false!>$>>)
        (old-state-right <GameState_ModularPkeCcaGame_<$<!false!><!false!>$>>)
        (return-left <OracleReturn-MonolithicPkeCcaGame-<$<!false!>$>-MON_CCA-<$<!b!>$>-PKENC>)
        (return-right <OracleReturn-ModularPkeCcaGame-<$<!false!><!false!>$>-MOD_CCA-<$$>-PKENC>)
        (m Bits_*)
    )
    Bool 
    (and
        (rand-is-eq 2 1 (<game-MonolithicPkeCcaGame-<$<!false!>$>-rand-2> old-state-left) (<game-ModularPkeCcaGame-<$<!false!><!false!>$>-rand-1> old-state-right))
        (rand-is-eq 1 3 (<game-MonolithicPkeCcaGame-<$<!false!>$>-rand-1> old-state-left) (<game-ModularPkeCcaGame-<$<!false!><!false!>$>-rand-3> old-state-right))
    )
)