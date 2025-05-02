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
        ; Following causes unknown:
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
    (or
        (and
            (= sample-ctr-monolithic_pke_cca_game sample-ctr-old-monolithic_pke_cca_game)
            (= sample-ctr-modular_pke_cca_game_with_real_kem sample-ctr-old-modular_pke_cca_game_with_real_kem)
            (= sample-id-monolithic_pke_cca_game 1)
            (= sample-id-modular_pke_cca_game_with_real_kem 1)
        )
    )
)

(define-fun randomness-mapping-PKDEC
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
        (state-left <GameState_MonolithicPkeCcaGame_<$<!b!>$>>) ; left
        (state-right <GameState_ModularPkeCcaGame_<$<!false!><!b!>$>>) ; right
    )
    Bool
    (let
        (
            (left_pk (<pkg-state-MON_CCA-<$<!b!>$>-pk> (<game-MonolithicPkeCcaGame-<$<!b!>$>-pkgstate-pkg_MON_CCA> state-left)))
            (left_sk (<pkg-state-MON_CCA-<$<!b!>$>-sk> (<game-MonolithicPkeCcaGame-<$<!b!>$>-pkgstate-pkg_MON_CCA> state-left)))
            (right_pk_mod_cca (<pkg-state-MOD_CCA-<$$>-pk> (<game-ModularPkeCcaGame-<$<!false!><!b!>$>-pkgstate-pkg_MOD_CCA> state-right)))
            (right_pk_kem (<pkg-state-KEM-<$$>-pk> (<game-ModularPkeCcaGame-<$<!false!><!b!>$>-pkgstate-pkg_KEM> state-right)))
            (left_c (<pkg-state-MON_CCA-<$<!b!>$>-c> (<game-MonolithicPkeCcaGame-<$<!b!>$>-pkgstate-pkg_MON_CCA> state-left)))
            (right_c (<pkg-state-MOD_CCA-<$$>-c> (<game-ModularPkeCcaGame-<$<!false!><!b!>$>-pkgstate-pkg_MOD_CCA> state-right)))
            (right_kem_ek (<pkg-state-KEM-<$$>-ek> (<game-ModularPkeCcaGame-<$<!false!><!b!>$>-pkgstate-pkg_KEM> state-right)))
            (right_mod_cca_ek (<pkg-state-MOD_CCA-<$$>-ek> (<game-ModularPkeCcaGame-<$<!false!><!b!>$>-pkgstate-pkg_MOD_CCA> state-right)))
            (right_dem_c (<pkg-state-DEM-<$<!dem_idealization!>$>-c> (<game-ModularPkeCcaGame-<$<!false!><!b!>$>-pkgstate-pkg_DEM> state-right)))
            (right_key_k (<pkg-state-Key-<$<!key_idealization!>$>-k> (<game-ModularPkeCcaGame-<$<!false!><!b!>$>-pkgstate-pkg_Key> state-right)))
            (right_sk (<pkg-state-KEM-<$$>-sk> (<game-ModularPkeCcaGame-<$<!false!><!b!>$>-pkgstate-pkg_KEM> state-right)))
        )
        (and
            (= left_pk right_pk_mod_cca right_pk_kem) ; left_pk = right_pk
            (= ((_ is mk-none) left_pk) ((_ is mk-none) left_sk) ((_ is mk-none) right_pk_mod_cca) ((_ is mk-none) right_pk_kem) ((_ is mk-none) right_sk)) ; left_pk = None iff right_pk = None
            (= left_c right_c) ; left_challenge_ciphertext = right_challenge_ciphertext
            (= ((_ is mk-none) left_c) ((_ is mk-none) right_c) ((_ is mk-none) right_kem_ek) ((_ is mk-none) right_mod_cca_ek) ((_ is mk-none) right_dem_c) ((_ is mk-none) right_key_k)) ; left_challenge_ciphertext = None iff right_challenge_ciphertext = None iff right_encapsulation_challenge = None iff right_dem_challenge = None iff right_key_k = None
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
                    (= (maybe-get right_key_k) (el2-1 (<<func-proof-kem_encaps>> (maybe-get right_pk_kem))))
                    (= (maybe-get right_kem_ek) (el2-2 (<<func-proof-kem_encaps>> (maybe-get right_pk_kem))))
                )
            )
        )
    )
)

(define-fun <relation-lemma-left-output-monolithic_pke_cca_game-modular_pke_cca_game_with_real_kem-PKDEC>
    (
        (old-state-left <GameState_MonolithicPkeCcaGame_<$<!b!>$>>)
        (old-state-right <GameState_ModularPkeCcaGame_<$<!false!><!b!>$>>)
        (return-left <OracleReturn-MonolithicPkeCcaGame-<$<!b!>$>-MON_CCA-<$<!b!>$>-PKDEC>)
        (return-right <OracleReturn-ModularPkeCcaGame-<$<!false!><!b!>$>-MOD_CCA-<$$>-PKDEC>)
        (ek_ctxt (Tuple2 Bits_400 Bits_*))
    )
    Bool
    (let
        (
            (sk (maybe-get (<pkg-state-MON_CCA-<$<!b!>$>-sk> (<game-MonolithicPkeCcaGame-<$<!b!>$>-pkgstate-pkg_MON_CCA> old-state-left))))
            (ek    (el2-1 ek_ctxt))
            (ctxt  (el2-2 ek_ctxt))
            (output (return-value (<oracle-return-MonolithicPkeCcaGame-<$<!b!>$>-MON_CCA-<$<!b!>$>-PKDEC-return-value-or-abort> return-left)))
        )
        (= 
            output
            (<<func-proof-dem_dec>> (<<func-proof-kem_decaps>> sk ek) ctxt)
        )
    )
)

(define-fun <relation-lemma-right-output-monolithic_pke_cca_game-modular_pke_cca_game_with_real_kem-PKDEC>
    (
        (old-state-left <GameState_MonolithicPkeCcaGame_<$<!b!>$>>)
        (old-state-right <GameState_ModularPkeCcaGame_<$<!false!><!b!>$>>)
        (return-left <OracleReturn-MonolithicPkeCcaGame-<$<!b!>$>-MON_CCA-<$<!b!>$>-PKDEC>)
        (return-right <OracleReturn-ModularPkeCcaGame-<$<!false!><!b!>$>-MOD_CCA-<$$>-PKDEC>)
        (ek_ctxt (Tuple2 Bits_400 Bits_*))
    )
    Bool
    (let
        (
            (sk (maybe-get (<pkg-state-KEM-<$$>-sk> (<game-ModularPkeCcaGame-<$<!false!><!b!>$>-pkgstate-pkg_KEM> old-state-right))))
            (ek (maybe-get (<pkg-state-KEM-<$$>-ek> (<game-ModularPkeCcaGame-<$<!false!><!b!>$>-pkgstate-pkg_KEM> old-state-right))))
            (encapsk (el2-1 ek_ctxt))
            (ctxt (el2-2 ek_ctxt))
            (k (maybe-get (<pkg-state-Key-<$<!key_idealization!>$>-k> (<game-ModularPkeCcaGame-<$<!false!><!b!>$>-pkgstate-pkg_Key> old-state-right))))
            (output (return-value (<oracle-return-ModularPkeCcaGame-<$<!false!><!b!>$>-MOD_CCA-<$$>-PKDEC-return-value-or-abort> return-right)))
        )
        (and
            (=>
                (not (= ek encapsk))
                (=
                    output
                    (<<func-proof-dem_dec>> (<<func-proof-kem_decaps>> sk encapsk) ctxt)
                    (<<func-proof-dem_dec>> (<<func-proof-kem_decaps>> sk encapsk) ctxt)
                )
            )
            (=>
                (and 
                    (= ek encapsk)
                    ;(= k (<<func-proof-kem_decaps>> sk ek))
                )
                (=
                    output
                    (<<func-proof-dem_dec>> (<<func-proof-kem_decaps>> sk encapsk) ctxt)
                    (<<func-proof-dem_dec>> (<<func-proof-kem_decaps>> sk encapsk) ctxt)
                )
            )
        )
    )
)

(define-fun <relation-lemma-kem-correctness-monolithic_pke_cca_game-modular_pke_cca_game_with_real_kem-PKDEC>
    (
        (old-state-left <GameState_MonolithicPkeCcaGame_<$<!b!>$>>)
        (old-state-right <GameState_ModularPkeCcaGame_<$<!false!><!b!>$>>)
        (return-left <OracleReturn-MonolithicPkeCcaGame-<$<!b!>$>-MON_CCA-<$<!b!>$>-PKDEC>)
        (return-right <OracleReturn-ModularPkeCcaGame-<$<!false!><!b!>$>-MOD_CCA-<$$>-PKDEC>)
        (ek_ctxt (Tuple2 Bits_400 Bits_*))
    )
    Bool
    (let
        (
            (pk (<pkg-state-KEM-<$$>-pk> (<game-ModularPkeCcaGame-<$<!false!><!b!>$>-pkgstate-pkg_KEM> old-state-right)))
            (sk (<pkg-state-KEM-<$$>-sk> (<game-ModularPkeCcaGame-<$<!false!><!b!>$>-pkgstate-pkg_KEM> old-state-right)))
        )
        (=>
            (not ((_ is mk-none) pk))
            (let
                (
                    (k (el2-1 (<<func-proof-kem_encaps>> (maybe-get pk))))
                    (ek (el2-2 (<<func-proof-kem_encaps>> (maybe-get pk))))
                )
                (= k (<<func-proof-kem_decaps>> (maybe-get sk) ek))
            )
        )
    )
)