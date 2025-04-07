(define-fun log_inverse_level_zero_invariant
    (
        (Log (Array (Tuple2 Int Bits_*) (Maybe (Tuple3 Bits_* Bool Bits_*))))
        (h (Maybe Bits_*))
        (k Bits_*)
    )
    Bool
    (=>
        (not ((_ is mk-none) h))
        (and
            (let
                (
                    (entry (select Log (mk-tuple2 0 (maybe-get h))))
                )
                (and
                    (not ((_ is mk-none) entry))
                    (=
                        (el3-2 (maybe-get entry))
                        false
                    )
                    (=
                        (el3-3 (maybe-get entry))
                        k
                    )
                )
            )
            (=
                (<<func-proof-level>> (maybe-get h))
                0
            )
        )
    )

)
(define-fun log_inverse_level_non_zero_invariant
    (
        (Log (Array (Tuple2 Int Bits_*) (Maybe (Tuple3 Bits_* Bool Bits_*))))
        (h (Maybe Bits_*))
        (k Bits_*)
    )
    Bool
    (=>
        (not ((_ is mk-none) h))
        (and 
            (let
                (
                    (entry (select Log (mk-tuple2 0 (maybe-get h))))
                )
                (and
                    (not ((_ is mk-none) entry))
                    (=
                        (el3-2 (maybe-get entry))
                        false
                    )
                    (=
                        (el3-3 (maybe-get entry))
                        k
                    )
                )
            )
            (not
                (=
                    (<<func-proof-level>> (maybe-get h))
                    0
                )
            )
        )
    )
)
(define-fun log_inverse_invariant
    (
        (Log (Array (Tuple2 Int Bits_*) (Maybe (Tuple3 Bits_* Bool Bits_*))))
        (h (Maybe Bits_*))
        (n Int)
        (k Bits_*)
    )
    Bool
    (=>
        (not ((_ is mk-none) h))
        (let
            (
                (entry (select Log (mk-tuple2 0 (maybe-get h))))
            )
            (and
                (not ((_ is mk-none) entry))
                (=
                    (el3-2 (maybe-get entry))
                    false
                )
                (=
                    (el3-3 (maybe-get entry))
                    k
                )
            )
        )
    )
)
(define-fun invariant
    (
        (state-Gks0 <GameState_Gks0_<$$>>)
        (state-Gks0Map <GameState_Gks0Map_<$$>>)
    )
    Bool
    (and 
        ; Invariant (1) : E_left = E_right
        (let
            (
                (E_left  (<pkg-state-DH-<$$>-E> (<game-Gks0-<$$>-pkgstate-pkg_DH> state-Gks0)))
                (E_right (<pkg-state-DH-<$$>-E> (<game-Gks0Map-<$$>-pkgstate-pkg_DH> state-Gks0Map)))
            )
            (= E_left E_right)
        )
        ; Invariant (2v) : Log_gks0[(n, h)] = some(h, hon, k) or none
        (let
            (
                (Log (<pkg-state-Log-<$$>-Log> (<game-Gks0-<$$>-pkgstate-pkg_Log> state-Gks0)))
            )
            (forall
                (
                    (h Bits_*)
                    (n Int)
                )
                (let 
                    (
                        (log_entry (select Log (mk-tuple2 n h)))
                    )
                    (=>
                        (not ((_ is mk-none) log_entry))
                        (= (el3-1 (maybe-get log_entry)) h)
                    )
                )
            )
        )
        ; Inverse maps
        ; Log[0, LogInverseDishonestLevelZero[k]] = (_, 0, k) and level(LogInverseDishonestLevelZero[k]) = 0
        ; Log[0, LogInverseDishonestLevelNonZero[k]] = (_, 0, k) and level(LogInverseDishonestLevelZero[k]) != 0
        ; Log[0, LogInverseDishonest[(0, k)]] = (_, 0, k)
        (let
            (
                (Log_left (<pkg-state-Log-<$$>-Log> (<game-Gks0-<$$>-pkgstate-pkg_Log> state-Gks0)))
                (Log_right (<pkg-state-Log-<$$>-Log> (<game-Gks0Map-<$$>-pkgstate-pkg_Log> state-Gks0Map)))
                (LogInverseDishonest_left (<pkg-state-Log-<$$>-LogInverseDishonest> (<game-Gks0-<$$>-pkgstate-pkg_Log> state-Gks0)))
                (LogInverseDishonest_right (<pkg-state-Log-<$$>-LogInverseDishonest> (<game-Gks0Map-<$$>-pkgstate-pkg_Log> state-Gks0Map)))
                (LogInverseDishonestLevelNonZero_left (<pkg-state-Log-<$$>-LogInverseDishonestLevelNonZero> (<game-Gks0-<$$>-pkgstate-pkg_Log> state-Gks0)))
                (LogInverseDishonestLevelNonZero_right (<pkg-state-Log-<$$>-LogInverseDishonestLevelNonZero> (<game-Gks0Map-<$$>-pkgstate-pkg_Log> state-Gks0Map)))
                (LogInverseDishonestLevelZero_left (<pkg-state-Log-<$$>-LogInverseDishonestLevelZero> (<game-Gks0-<$$>-pkgstate-pkg_Log> state-Gks0)))
                (LogInverseDishonestLevelZero_right (<pkg-state-Log-<$$>-LogInverseDishonestLevelZero> (<game-Gks0Map-<$$>-pkgstate-pkg_Log> state-Gks0Map)))
            )
            (forall
                (
                    (k Bits_*)
                )
                (let 
                    (
                        (log_inverse_level_zero_left (select LogInverseDishonestLevelZero_left k))
                        (log_inverse_level_zero_right (select LogInverseDishonestLevelZero_right k))
                        (log_inverse_level_non_zero_left (select LogInverseDishonestLevelNonZero_left k))
                        (log_inverse_level_non_zero_right (select LogInverseDishonestLevelNonZero_right k))
                        (log_inverse_left (select LogInverseDishonest_left (mk-tuple2 0 k)))
                        (log_inverse_right (select LogInverseDishonest_right (mk-tuple2 0 k)))
                    )
                    (and
                        (log_inverse_level_zero_invariant Log_left log_inverse_level_zero_left k)
                        (log_inverse_level_zero_invariant Log_right log_inverse_level_zero_right k)
                        (log_inverse_level_non_zero_invariant Log_left log_inverse_level_non_zero_left k)
                        (log_inverse_level_non_zero_invariant Log_right log_inverse_level_non_zero_right k)
                        (log_inverse_invariant Log_left log_inverse_left 0 k)
                        (log_inverse_invariant Log_right log_inverse_right 0 k)
                    )
                )
            )
        )
        ; Invariant (5) for inverse maps on input keys
        ; LogInverseDishonestLevelZero_left[k] = None iff LogInverseDishonestLevelZero_right[k] = None
        ; LogInverseDishonestLevelNonZero_left[k] = None iff LogInverseDishonestLevelNonZero_right[k] = None
        ; LogInverseDishonest_left[(0, k)] = None iff LogInverseDishonest_right[(0, k)] = None
        (let
            (
                (LogInverseDishonest_left (<pkg-state-Log-<$$>-LogInverseDishonest> (<game-Gks0-<$$>-pkgstate-pkg_Log> state-Gks0)))
                (LogInverseDishonest_right (<pkg-state-Log-<$$>-LogInverseDishonest> (<game-Gks0Map-<$$>-pkgstate-pkg_Log> state-Gks0Map)))
                (LogInverseDishonestLevelNonZero_left (<pkg-state-Log-<$$>-LogInverseDishonestLevelNonZero> (<game-Gks0-<$$>-pkgstate-pkg_Log> state-Gks0)))
                (LogInverseDishonestLevelNonZero_right (<pkg-state-Log-<$$>-LogInverseDishonestLevelNonZero> (<game-Gks0Map-<$$>-pkgstate-pkg_Log> state-Gks0Map)))
                (LogInverseDishonestLevelZero_left (<pkg-state-Log-<$$>-LogInverseDishonestLevelZero> (<game-Gks0-<$$>-pkgstate-pkg_Log> state-Gks0)))
                (LogInverseDishonestLevelZero_right (<pkg-state-Log-<$$>-LogInverseDishonestLevelZero> (<game-Gks0Map-<$$>-pkgstate-pkg_Log> state-Gks0Map)))
            )
            (forall
                (
                    (k Bits_*)
                )
                (let
                    (
                        (dishonest_level_zero_psk_left (select LogInverseDishonestLevelZero_left k))
                        (dishonest_level_zero_psk_right (select LogInverseDishonestLevelZero_right k))
                        (dishonest_level_non_zero_psk_left (select LogInverseDishonestLevelNonZero_left k))
                        (dishonest_level_non_zero_psk_right (select LogInverseDishonestLevelNonZero_right k))
                        (dishonest_psk_left (select LogInverseDishonest_left (mk-tuple2 0 k)))
                        (dishonest_psk_right (select LogInverseDishonest_right (mk-tuple2 0 k)))
                    )
                    (and
                        (=
                            ((_ is mk-none) dishonest_level_zero_psk_left)
                            ((_ is mk-none) dishonest_level_zero_psk_right)
                        )
                        (=
                            ((_ is mk-none) dishonest_level_non_zero_psk_left)
                            ((_ is mk-none) dishonest_level_non_zero_psk_right)
                        )
                        (=
                            ((_ is mk-none) dishonest_psk_left)
                            ((_ is mk-none) dishonest_psk_right)
                        )
                    )
                )
            )
        )
        ; Invariant (2e)
        ; forall k: (
        ;    LogInverseDishonestLevelZero_right[k] != None and 
        ;    LogInverseDishonestLevelNonZero_right[k] != None and 
        ;    LogInverseDishonestLevelZero_right[k] != LogInverseDishonestLevelNonZero_right[k]
        ; ) => J[k] = true
        (let 
            (
                (LogInverseDishonestLevelZero_right (<pkg-state-Log-<$$>-LogInverseDishonestLevelZero> (<game-Gks0Map-<$$>-pkgstate-pkg_Log> state-Gks0Map)))
                (LogInverseDishonestLevelNonZero_right (<pkg-state-Log-<$$>-LogInverseDishonestLevelNonZero> (<game-Gks0Map-<$$>-pkgstate-pkg_Log> state-Gks0Map)))
                (J (<pkg-state-Log-<$$>-J> (<game-Gks0Map-<$$>-pkgstate-pkg_Log> state-Gks0Map)))
            )
            (forall 
                (
                    (k Bits_*)
                )
                (let
                    (
                        (dishonest_level_zero_psk_right (select LogInverseDishonestLevelZero_right k))
                        (dishonest_level_non_zero_psk_right (select LogInverseDishonestLevelNonZero_right k))
                    )
                    (=>
                        (and 
                            (not ((_ is mk-none) dishonest_level_zero_psk_right))
                            (not ((_ is mk-none) dishonest_level_non_zero_psk_right))
                        )
                        (=
                            (select J k)
                            (mk-some true)
                        )
                    )
                )
            )
        )
        ; Invariant (5) : Log_left[(psk, h)] = None iff Log_right[(psk, h)] = None
        (let
            (
                (Log_left (<pkg-state-Log-<$$>-Log> (<game-Gks0-<$$>-pkgstate-pkg_Log> state-Gks0)))
                (Log_right (<pkg-state-Log-<$$>-Log> (<game-Gks0Map-<$$>-pkgstate-pkg_Log> state-Gks0Map)))
            )
            (forall
                (
                    (h Bits_*)
                    (n Int)
                )
                (=>
                    (or
                        (and (= n 0) (= (<<func-proof-level>> h) 0)); level zero psk
                        (= n 16) ; dh
                    )
                    (let 
                        (
                            (left_entry (select Log_left (mk-tuple2 n h)))
                            (right_entry (select Log_right (mk-tuple2 n h)))
                        )
                        (=
                            ((_ is mk-none) left_entry)
                            ((_ is mk-none) right_entry)
                        )
                    )
                )
            )
        )
    )
)