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

(define-fun <relation-lemma-DHEXP-SET-does-not-abort-game_Gks0-game_Gks0Map-DHEXP>
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-DHEXP-Gks0 <OracleReturn-Gks0-<$$>-DH-<$$>-DHEXP>)
        (return-DHEXP-Gks0Map <OracleReturn-Gks0Map-<$$>-Map-<$$>-DHEXP>)
        (X Bits_*)
        (Y Bits_*)
    )
    Bool
    (forall 
        (
            (<game-state> <GameState_Gks0_<$$>>)
            (<game-consts> <GameConsts_Gks0>)
            (h Bits_*)
            (hon Bool)
            (k Bits_*)
        )
        (let
            (
                (return-SET (<oracle-Gks0-<$$>-Key-<$$>-SET> <game-state> <game-consts> 16 0 h hon (<<func-pkg-game_Gks0-pkg_DH-encode_group_member>> k)))
            )
            (not 
                (=
                    (as mk-abort (ReturnValue Bits_*))
                    (<oracle-return-Gks0-<$$>-Key-<$$>-SET-return-value-or-abort> return-SET)
                )
            )
        )
    )
)

(define-fun <relation-lemma-Gks0-Key-SET-dh-does-not-map-game_Gks0-game_Gks0Map-DHEXP>
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-DHEXP-Gks0 <OracleReturn-Gks0-<$$>-DH-<$$>-DHEXP>)
        (return-DHEXP-Gks0Map <OracleReturn-Gks0Map-<$$>-Map-<$$>-DHEXP>)
        (X Bits_*)
        (Y Bits_*)
    )
    Bool
    (forall 
        (
            (<game-state> <GameState_Gks0_<$$>>)
            (<game-consts> <GameConsts_Gks0>)
            (h Bits_*)
            (hon Bool)
            (k Bits_*)
        )
        (let
            (
                (return-SET (<oracle-Gks0-<$$>-Key-<$$>-SET> <game-state> <game-consts> 16 0 h hon (<<func-pkg-game_Gks0-pkg_DH-encode_group_member>> k)))
            )
            (not 
                (=
                    h
                    (return-value (<oracle-return-Gks0-<$$>-Key-<$$>-SET-return-value-or-abort> return-SET))
                )
            )
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

(define-fun <relation-lemma-Gks0-aborts-game_Gks0-game_Gks0Map-DHEXP>
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-DHEXP-Gks0 <OracleReturn-Gks0-<$$>-DH-<$$>-DHEXP>)
        (return-DHEXP-Gks0Map <OracleReturn-Gks0Map-<$$>-Map-<$$>-DHEXP>)
        (X Bits_*)
        (Y Bits_*)
    )
    Bool
    (and
        ((_ is mk-abort) (<oracle-return-Gks0-<$$>-DH-<$$>-DHEXP-return-value-or-abort> return-DHEXP-Gks0))
        (not 
            ((_ is mk-abort) (<oracle-return-Gks0Map-<$$>-Map-<$$>-DHEXP-return-value-or-abort> return-DHEXP-Gks0Map))
        )
    )
)

(define-fun <relation-lemma-Gks0Map-aborts-game_Gks0-game_Gks0Map-DHEXP>
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-DHEXP-Gks0 <OracleReturn-Gks0-<$$>-DH-<$$>-DHEXP>)
        (return-DHEXP-Gks0Map <OracleReturn-Gks0Map-<$$>-Map-<$$>-DHEXP>)
        (X Bits_*)
        (Y Bits_*)
    )
    Bool
    (and
        ((_ is mk-abort) (<oracle-return-Gks0Map-<$$>-Map-<$$>-DHEXP-return-value-or-abort> return-DHEXP-Gks0Map))
        (not 
            ((_ is mk-abort) (<oracle-return-Gks0-<$$>-DH-<$$>-DHEXP-return-value-or-abort> return-DHEXP-Gks0))
        )
    )
)

(define-fun invariant
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
    )
    Bool
    (and 
        ; E_left = E_right
        (let
            (
                (E_left  (<pkg-state-DH-<$$>-E> (<game-Gks0-<$$>-pkgstate-pkg_DH> old-state-Gks0)))
                (E_right (<pkg-state-DH-<$$>-E> (<game-Gks0Map-<$$>-pkgstate-pkg_DH> old-state-Gks0Map)))
            )
            (= E_left E_right)
        )
        ; Log[(dh, h)] = some(h, hon, k) or none
        (let
            (
                (Log (<pkg-state-Log-<$$>-Log> (<game-Gks0-<$$>-pkgstate-pkg_Log> old-state-Gks0)))
            )
            (forall
                (
                    (h Bits_*)
                )
                (let 
                    (
                        (log_entry (select Log (mk-tuple2 16 h)))
                    )
                    (=>
                        (not ((_ is mk-none) log_entry))
                        (= (el3-1 (maybe-get log_entry)) h)
                    )
                )
            )
        )
    )
)

(assert 
    (= 
        (<<func-proof-log_package_parameters>> 0 true false false false) ; Gks0 is 0, is_dh = true, is_psk = is_internal = is_output = false
        (mk-tuple2 0 0) ; pattern = 0 (Z) and mapping = 0
    )
)

(assert 
    (= 
        (<<func-proof-log_package_parameters>> 1 true false false false) ; Gks0Map is 1, is_dh = true, is_psk = is_internal = is_output = false
        (mk-tuple2 0 2) ; pattern = 0 (Z) and mapping = infinity
    )
)