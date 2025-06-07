(define-fun randomness-mapping-UNQ
    ( 
        (sample-ctr-old-Gks0 Int)
        (sample-ctr-old-Gks0Map Int)
        (sample-id-Gks0 Int)
        (sample-id-Gks0Map Int)
        (sample-ctr-Gks0 Int)
        (sample-ctr-Gks0Map Int)
    )
    Bool
    false
)

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
    (or
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


(define-fun none-aware-level
    (
        (h Bits_*)
    )
    Int
    (let 
        (
            (level (<<func-level>> h))
        )
        (ite 
            ((_ is mk-none) level)
            0
            (maybe-get level)
        )
    )
)
(define-fun invariant-2a-i
    (
        (n Int)
        (l Int)
        (h Bits_*)
        (Log (Array (Tuple2 Int Bits_*) (Maybe (Tuple3 Bits_* Bool Bits_*))))
        (K (Array (Tuple3 Int Int Bits_*) (Maybe (Tuple2 Bits_* Bool))))
    )
    Bool
    ; Invariant (2a) (i) : Log[(n, h)] = none => K[(n, l, h)] = none
    (=>
        ((_ is mk-none) (select Log (mk-tuple2 n h)))
        ((_ is mk-none) (select K (mk-tuple3 n l h)))
    )
)
(define-fun invariant-2a-ii
    (
        (n Int)
        (l Int)
        (h Bits_*)
        (Log (Array (Tuple2 Int Bits_*) (Maybe (Tuple3 Bits_* Bool Bits_*))))
        (K (Array (Tuple3 Int Int Bits_*) (Maybe (Tuple2 Bits_* Bool))))
    )
    Bool
    ; Invariant (2a) (ii) : Log[(n, h)] = (h', _, _) and h != h' => K[(n, l, h)] = none
    (=>
        (not (= h (el3-1 (maybe-get (select Log (mk-tuple2 n h))))))
        ((_ is mk-none) (select K (mk-tuple3 n l h)))
    )
)
(define-fun invariant-2a-iii
    (
        (n Int)
        (h Bits_*)
        (Log (Array (Tuple2 Int Bits_*) (Maybe (Tuple3 Bits_* Bool Bits_*))))
    )
    Bool
    ; Invariant (2a) (iii) : Log[(n, h)] = (h', hon, k) and h != h' => Log[(n, h')] = (h', hon, k) and hon = false
    (=> 
        (not ((_ is mk-none) (select Log (mk-tuple2 n h))))
        (let
            (
                (log_entry (maybe-get (select Log (mk-tuple2 n h))))
            )
            (let
                (
                    (mapped_h (el3-1 log_entry))
                    (hon (el3-2 log_entry))
                    (k (el3-3 log_entry))
                )
                (=>
                    (not (= h mapped_h))
                    (and
                        (not ((_ is mk-none) (select Log (mk-tuple2 n mapped_h))))
                        (let
                            (
                                (mapped_log_entry (maybe-get (select Log (mk-tuple2 n mapped_h))))
                            )
                            (and
                                (= mapped_h (el3-1 mapped_log_entry)) ; h
                                (= (el3-3 log_entry) (el3-3 mapped_log_entry)) ; k
                                (= false (el3-2 log_entry) (el3-2 mapped_log_entry)) ; hon
                            )
                        )
                    )
                )
            )
        )
    )
)
(define-fun invariant-2a-iv
    (
        (n Int)
        (l Int)
        (h Bits_*)
        (Log (Array (Tuple2 Int Bits_*) (Maybe (Tuple3 Bits_* Bool Bits_*))))
        (K (Array (Tuple3 Int Int Bits_*) (Maybe (Tuple2 Bits_* Bool))))
    )
    Bool
    ; Invariant (2a) (iv) : Log[(n, h)] = (h, hon, k) <=> K[(n, l, h)] = (k, hon) != none
    (let 
        (
            (log_entry (select Log (mk-tuple2 n h)))
            (key_entry (select K (mk-tuple3 n l h)))
        )
        (and 
            ; =>
            (=>
                (and 
                    (not ((_ is mk-none) log_entry))
                    (= (el3-1 (maybe-get log_entry)) h)
                )
                (and
                    (not ((_ is mk-none) key_entry))
                    (= (el2-1 (maybe-get key_entry)) (el3-3 (maybe-get log_entry))) ; k
                    (= (el2-2 (maybe-get key_entry)) (el3-2 (maybe-get log_entry))) ; hon
                )
            )
            ; <=
            (=>
                (not ((_ is mk-none) key_entry))
                (and
                    (not ((_ is mk-none) log_entry))
                    (= (el2-1 (maybe-get key_entry)) (el3-3 (maybe-get log_entry))) ; k
                    (= (el2-2 (maybe-get key_entry)) (el3-2 (maybe-get log_entry))) ; hon
                    (= (el3-1 (maybe-get log_entry)) h) ; h
                )
            )
        )
    )
)
(define-fun invariant-2a-vii
    (
        (m Int)
        (h Bits_*)
        (Log (Array (Tuple2 Int Bits_*) (Maybe (Tuple3 Bits_* Bool Bits_*))))
    )
    Bool
    ; Invariant (2a) (vii) : Log[(n', h)] != none => name(h) = n'
    (=>
        (not ((_ is mk-none) (select Log (mk-tuple2 m h))))
        (= m (<<func-name>> h))
    )
)
(define-fun invariant-2a-viii
    (
        (n Int)
        (h Bits_*)
        (Log (Array (Tuple2 Int Bits_*) (Maybe (Tuple3 Bits_* Bool Bits_*))))
    )
    Bool
    ; Invariant (2a) (viii) : Log[(n, h)] = (h', _, k) and n != dh => len(k) = len(h) = len(h') and alg(h) = alg(h')
    (let
        (
            (log_entry (select Log (mk-tuple2 n h)))
        )
        (=>
            (and (not ((_ is mk-none) log_entry)) (not (= n KEY_dh)))
            (let 
                (
                    (k (el3-3 (maybe-get log_entry)))
                    (mapped_h (el3-1 (maybe-get log_entry)))
                )
                (and
                    (= (<<func-handle_alg>> h) (<<func-handle_alg>> mapped_h))
                    (= (<<func-len_key>> k) (<<func-len_alg>> (<<func-handle_alg>> h)) (<<func-len_alg>> (<<func-handle_alg>> mapped_h)))
                )
            )
        )
    )
)
(define-fun invariant-2a-ix
    (
        (n Int)
        (h Bits_*)
        (K (Array (Tuple3 Int Int Bits_*) (Maybe (Tuple2 Bits_* Bool))))
    )
    Bool
    ; Invariant (2a) (ix) : n := name(h) in {0ikm, 0salt, dh} and K[(name(h), 0, h)] != none => level(h) = none
    (=>
        (and
            (or (= n KEY_dh) (= n KEY_0ikm) (= n KEY_0salt))
            (not ((_ is mk-none) (select K (mk-tuple3 n 0 h))))
        )
        ((_ is mk-none) (<<func-level>> h))
    )
)
(define-fun invariant-2a-x
    (
        (n Int)
        (h Bits_*)
        (K (Array (Tuple3 Int Int Bits_*) (Maybe (Tuple2 Bits_* Bool))))
    )
    Bool
    ; Invariant (2a) (x) : forall l: name(h) not in {0ikm, 0salt, dh} and K[(name(h), l, h)] != none => level(h) = l
    (forall 
        (
            (l Int)
        )
        (=>
            (and
                (not (or (= n KEY_dh) (= n KEY_0ikm) (= n KEY_0salt)))
                (not ((_ is mk-none) (select K (mk-tuple3 n l h))))
            )
            (= (maybe-get (<<func-level>> h)) l)
        )
    )
)
(define-fun invariant-2a-i-ii-iii-iv-vii-viii-ix-x-one-table
    (
        (Log (Array (Tuple2 Int Bits_*) (Maybe (Tuple3 Bits_* Bool Bits_*))))
        (K (Array (Tuple3 Int Int Bits_*) (Maybe (Tuple2 Bits_* Bool))))
    )
    Bool
    (forall
        (
            (h Bits_*)
            (m Int)
        )
        (let
            (
                (n (<<func-name>> h))
            )
            (let 
                (
                    (l (none-aware-level h))
                )
                (and
                    (invariant-2a-i n l h Log K)
                    (invariant-2a-ii n l h Log K)
                    ;(invariant-2a-iii n h Log)
                    ;(invariant-2a-iv n l h Log K)
                    (invariant-2a-vii m h Log)
                    ;(invariant-2a-viii n h Log)
                    ;(invariant-2a-ix n h K)
                    ;(invariant-2a-x n h K)
                )
            )
        )
    )
)
(define-fun invariant-2a-i-ii-iii-iv-vii-viii-ix-x
    (
        (state-Gks0 <GameState_Gks0_<$$>>)
        (state-Gks0Map <GameState_Gks0Map_<$$>>)
    )
    Bool
    (let 
        (
            (Log_left (<pkg-state-Log-<$$>-Log> (<game-Gks0-<$$>-pkgstate-pkg_Log> state-Gks0)))
            (Log_right (<pkg-state-Log-<$$>-Log> (<game-Gks0Map-<$$>-pkgstate-pkg_Log> state-Gks0Map)))
            (K_left (<pkg-state-Key-<$$>-K> (<game-Gks0-<$$>-pkgstate-pkg_Key> state-Gks0)))
            (K_right (<pkg-state-Key-<$$>-K> (<game-Gks0Map-<$$>-pkgstate-pkg_Key> state-Gks0Map)))
        )
        (and
            (invariant-2a-i-ii-iii-iv-vii-viii-ix-x-one-table Log_left K_left)
            (invariant-2a-i-ii-iii-iv-vii-viii-ix-x-one-table Log_right K_right)
        )
    )
)
(define-fun invariant-2a-v
    (
        (state-Gks0 <GameState_Gks0_<$$>>)
        (state-Gks0Map <GameState_Gks0Map_<$$>>)
    )
    Bool
    ; n = name(h)
    ; Invariant (2a) (v) : Log_left[(n, h)] = some(h, hon, k) or none
    (let
        (
            (Log_left (<pkg-state-Log-<$$>-Log> (<game-Gks0-<$$>-pkgstate-pkg_Log> state-Gks0)))
        )
        (forall
            (
                (h Bits_*)
            )
            (let
                (
                    (n (<<func-name>> h))
                )
                (let 
                    (
                        (log_entry (select Log_left (mk-tuple2 n h)))
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
(define-fun invariant-2a-vi
    (
        (state-Gks0 <GameState_Gks0_<$$>>)
        (state-Gks0Map <GameState_Gks0Map_<$$>>)
    )
    Bool
    ; Invariant (2a) (vi) : Log_right[h] != none and name(h) not in {psk, dh} => Log_right[h] = (h, _, _)
    (let
        (
            (Log_right (<pkg-state-Log-<$$>-Log> (<game-Gks0Map-<$$>-pkgstate-pkg_Log> state-Gks0Map)))
            (K_right (<pkg-state-Key-<$$>-K> (<game-Gks0Map-<$$>-pkgstate-pkg_Key> state-Gks0Map)))
        )
        (forall 
            (
                (h Bits_*)
            )
            (let
                (
                    (n (<<func-name>> h))
                )
                (=>
                    (and
                        (not
                            ((_ is mk-none) (select Log_right (mk-tuple2 n h)))
                        )
                        (not
                            (or (= n KEY_psk) (= n KEY_dh))
                        )
                    )
                    (= (el3-1 (maybe-get (select Log_right (mk-tuple2 n h)))) h)
                )
            )
        )
    )
)
(define-fun invariant-2a
    (
        (state-Gks0 <GameState_Gks0_<$$>>)
        (state-Gks0Map <GameState_Gks0Map_<$$>>)
    )
    Bool
    (and
        ;(invariant-2a-i-ii-iii-iv-vii-viii-ix-x state-Gks0 state-Gks0Map)
        (invariant-2a-v state-Gks0 state-Gks0Map)
        (invariant-2a-vi state-Gks0 state-Gks0Map)
    )
)
(define-fun invariant-2e
    (
        (state-Gks0 <GameState_Gks0_<$$>>)
        (state-Gks0Map <GameState_Gks0Map_<$$>>)
    )
    Bool
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
)
(define-fun invariant-2
    (
        (state-Gks0 <GameState_Gks0_<$$>>)
        (state-Gks0Map <GameState_Gks0Map_<$$>>)
    )
    Bool
    (and
        (invariant-2a state-Gks0 state-Gks0Map)
        ;(invariant-2e state-Gks0 state-Gks0Map)
    )
)
(define-fun invariant-consistent-log-for-dh-and-psk
    (
        (state-Gks0 <GameState_Gks0_<$$>>)
        (state-Gks0Map <GameState_Gks0Map_<$$>>)
    )
    Bool
    (let
        (
            (Log_left (<pkg-state-Log-<$$>-Log> (<game-Gks0-<$$>-pkgstate-pkg_Log> state-Gks0)))
            (Log_right (<pkg-state-Log-<$$>-Log> (<game-Gks0Map-<$$>-pkgstate-pkg_Log> state-Gks0Map)))
        )
        (forall
            (
                (h Bits_*)
            )
            (let
                (
                    (n (<<func-name>> h))
                )
                (=>
                    (or
                        (and (= n KEY_psk) (= (<<func-level>> h) (mk-some 0))); level zero psk
                        (= n KEY_dh) ; dh
                    )
                    (let 
                        (
                            (left_entry (select Log_left (mk-tuple2 n h)))
                            (right_entry (select Log_right (mk-tuple2 n h)))
                        )
                        (and
                            (=
                                ((_ is mk-none) left_entry)
                                ((_ is mk-none) right_entry)
                            )
                            (=>
                                (not ((_ is mk-none) left_entry))
                                (and
                                    (= (el3-2 (maybe-get left_entry)) (el3-2 (maybe-get right_entry))) ; hon
                                    (= (el3-3 (maybe-get left_entry)) (el3-3 (maybe-get right_entry))) ; k
                                    (= (el3-1 (maybe-get left_entry)) h) ; same handle
                                )
                            )
                        )

                    )
                )
            )
        )
    )
)
(define-fun invariant-consistent-log-inverse-level-zero-psk
    (
        (state-Gks0 <GameState_Gks0_<$$>>)
        (state-Gks0Map <GameState_Gks0Map_<$$>>)
    )
    Bool
    ; LogInverseDishonestLevelZero_left[k] = None <=> LogInverseDishonestLevelZero_right[k] = None
    (let
        (
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
                )
                (and
                    (=
                        ((_ is mk-none) dishonest_level_zero_psk_left)
                        ((_ is mk-none) dishonest_level_zero_psk_right)
                    )
                )
            )
        )
    )
)
(define-fun log_inverse_level_zero_invariant
    (
        (Log (Array (Tuple2 Int Bits_*) (Maybe (Tuple3 Bits_* Bool Bits_*))))
        (h (Maybe Bits_*))
        (k Bits_*)
    )
    Bool
    ; h != none => Log[(psk, h)] != none and Log[(psk, h)] = (_, false, k) and level(h) = 0
    (=>
        (not ((_ is mk-none) h))
        (and
            (let
                (
                    (entry (select Log (mk-tuple2 KEY_psk (maybe-get h))))
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
                (<<func-level>> (maybe-get h))
                (mk-some 0)
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
    ; h != none => Log[(psk, h)] != none and Log[(psk, h)] = (_, false, k) and level(h) != 0
    (=>
        (not ((_ is mk-none) h))
        (let
            (
                (entry (select Log (mk-tuple2 KEY_psk (maybe-get h))))
                (level (maybe-get (<<func-level>> (maybe-get h))))
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
                (not 
                    (= level 0)
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
    ; h != none => Log[(n, h)] != none and Log[(psk, h)] = (h, false, k)
    (=>
        (not ((_ is mk-none) h))
        (let
            (
                (entry (select Log (mk-tuple2 n (maybe-get h))))
            )
            (and
                (not ((_ is mk-none) entry))
                (=
                    (el3-1 (maybe-get entry))
                    (maybe-get h)
                )
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
(define-fun invariant-log-inverse
    (
        (state-Gks0 <GameState_Gks0_<$$>>)
        (state-Gks0Map <GameState_Gks0Map_<$$>>)
    )
    Bool
    ; Inverse maps
    ; Log[psk, LogInverseDishonestLevelZero[k]] = (_, false, k) and level(LogInverseDishonestLevelZero[k]) = 0
    ; Log[psk, LogInverseDishonestLevelNonZero[k]] = (_, false, k) and level(LogInverseDishonestLevelZero[k]) != 0
    ; Log[psk, LogInverseDishonest[(psk, k)]] = (_, false, k)
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
                    (log_inverse_left (select LogInverseDishonest_left (mk-tuple2 KEY_psk k)))
                    (log_inverse_right (select LogInverseDishonest_right (mk-tuple2 KEY_psk k)))
                )
                (and
                    (log_inverse_level_zero_invariant Log_left log_inverse_level_zero_left k)
                    (log_inverse_level_zero_invariant Log_right log_inverse_level_zero_right k)
                    (log_inverse_level_non_zero_invariant Log_left log_inverse_level_non_zero_left k)
                    (log_inverse_level_non_zero_invariant Log_right log_inverse_level_non_zero_right k)
                    (log_inverse_invariant Log_left log_inverse_left KEY_psk k)
                    (log_inverse_invariant Log_right log_inverse_right KEY_psk k)
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
    true
    ;(and
        ;(invariant-2 state-Gks0 state-Gks0Map)
        ;(invariant-log-inverse state-Gks0 state-Gks0Map)
        ;(invariant-consistent-log-inverse state-Gks0 state-Gks0Map)
    ;)
)
(define-fun invariant-log-preserves-name-one-table
    (
        (n Int)
        (h Bits_*)
        (Log (Array (Tuple2 Int Bits_*) (Maybe (Tuple3 Bits_* Bool Bits_*))))
    )
    Bool
    ; Invariant log preserves name : Log[(n, h)] = (h', _, _) => name(h) = name(h')
    (let
        (
            (log_entry (select Log (mk-tuple2 n h)))
        )
        (=>
            (and (not ((_ is mk-none) log_entry)))
            (let 
                (
                    (mapped_h (el3-1 (maybe-get log_entry)))
                )
                (= (<<func-name>> h) (<<func-name>> mapped_h))
            )
        )
    )
)
(define-fun invariant-log-preserves-name
    (
        (state-Gks0 <GameState_Gks0_<$$>>)
        (state-Gks0Map <GameState_Gks0Map_<$$>>)
    )
    Bool
    (let 
        (
            (Log_left (<pkg-state-Log-<$$>-Log> (<game-Gks0-<$$>-pkgstate-pkg_Log> state-Gks0)))
            (Log_right (<pkg-state-Log-<$$>-Log> (<game-Gks0Map-<$$>-pkgstate-pkg_Log> state-Gks0Map)))
        )
        (forall
            (
                (h Bits_*)
            )
            (let
                (
                    (n (<<func-name>> h))
                )
                (and
                    (invariant-log-preserves-name-one-table n h Log_left)
                    (invariant-log-preserves-name-one-table n h Log_right)
                )
            )
        )
    )
)
(define-fun invariant-log-inverse-name
    (
        (state-Gks0 <GameState_Gks0_<$$>>)
        (state-Gks0Map <GameState_Gks0Map_<$$>>)
    )
    Bool
    (let
        (
            (LogInverseDishonest_right (<pkg-state-Log-<$$>-LogInverseDishonest> (<game-Gks0Map-<$$>-pkgstate-pkg_Log> state-Gks0Map)))
            (LogInverseDishonestLevelNonZero_right (<pkg-state-Log-<$$>-LogInverseDishonestLevelNonZero> (<game-Gks0Map-<$$>-pkgstate-pkg_Log> state-Gks0Map)))
            (LogInverseDishonestLevelZero_right (<pkg-state-Log-<$$>-LogInverseDishonestLevelZero> (<game-Gks0Map-<$$>-pkgstate-pkg_Log> state-Gks0Map)))            
        )
        (forall
            (
                (k Bits_*)
            )
            (let 
                (
                    (log_inverse_right_dh (select LogInverseDishonest_right (mk-tuple2 KEY_dh k)))
                    (log_inverse_right_psk (select LogInverseDishonest_right (mk-tuple2 KEY_psk k)))
                    (log_inverse_right_non_zero (select LogInverseDishonestLevelNonZero_right k))
                    (log_inverse_right_zero (select LogInverseDishonestLevelZero_right k))
                )
                (and
                    (=>
                        (not ((_ is mk-none) log_inverse_right_dh))
                        (= KEY_dh (<<func-name>> (maybe-get log_inverse_right_dh)))
                    )
                    (=>
                        (not ((_ is mk-none) log_inverse_right_psk))
                        (= KEY_psk (<<func-name>> (maybe-get log_inverse_right_psk)))
                    )
                    (=>
                        (not ((_ is mk-none) log_inverse_right_non_zero))
                        (= KEY_psk (<<func-name>> (maybe-get log_inverse_right_non_zero)))
                    )
                    (=>
                        (not ((_ is mk-none) log_inverse_right_zero))
                        (= KEY_psk (<<func-name>> (maybe-get log_inverse_right_zero)))
                    )
                )
            )
        )
    )
)
(define-fun assert-invariant-2a-ix-and-2a-x 
    (
        (state-Gks0 <GameState_Gks0_<$$>>)
        (state-Gks0Map <GameState_Gks0Map_<$$>>)
    )
    Bool
    (let 
        (
            (K_left (<pkg-state-Key-<$$>-K> (<game-Gks0-<$$>-pkgstate-pkg_Key> state-Gks0)))
            (K_right (<pkg-state-Key-<$$>-K> (<game-Gks0Map-<$$>-pkgstate-pkg_Key> state-Gks0Map)))
        )
        (forall
            (
                (h Bits_*)
            )
            (let
                (
                    (n (<<func-name>> h))
                )
                (and
                    (invariant-2a-ix n h K_left)
                    (invariant-2a-x n h K_left)
                    (invariant-2a-ix n h K_right)
                    (invariant-2a-x n h K_right)
                )
            )
        )
    )
)
(define-fun assert-invariant-2a-iii
    (
        (state-Gks0 <GameState_Gks0_<$$>>)
        (state-Gks0Map <GameState_Gks0Map_<$$>>)
    )
    Bool
    (let 
        (
            (Log_left (<pkg-state-Log-<$$>-Log> (<game-Gks0-<$$>-pkgstate-pkg_Log> state-Gks0)))
            (Log_right (<pkg-state-Log-<$$>-Log> (<game-Gks0Map-<$$>-pkgstate-pkg_Log> state-Gks0Map)))
        )
        (forall
            (
                (h Bits_*)
            )
            (let
                (
                    (n (<<func-name>> h))
                )
                (and
                    (invariant-2a-iii n h Log_left)
                    (invariant-2a-iii n h Log_right)
                )
            )
        )
    )
)
(define-fun assert-invariant-2a-iv
    (
        (state-Gks0 <GameState_Gks0_<$$>>)
        (state-Gks0Map <GameState_Gks0Map_<$$>>)
    )
    Bool
    (let 
        (
            (Log_left (<pkg-state-Log-<$$>-Log> (<game-Gks0-<$$>-pkgstate-pkg_Log> state-Gks0)))
            (Log_right (<pkg-state-Log-<$$>-Log> (<game-Gks0Map-<$$>-pkgstate-pkg_Log> state-Gks0Map)))
            (K_left (<pkg-state-Key-<$$>-K> (<game-Gks0-<$$>-pkgstate-pkg_Key> state-Gks0)))
            (K_right (<pkg-state-Key-<$$>-K> (<game-Gks0Map-<$$>-pkgstate-pkg_Key> state-Gks0Map)))
        )
        (forall
            (
                (h Bits_*)
            )
            (let
                (
                    (n (<<func-name>> h))
                    (l (none-aware-level h))
                )
                (and
                    (invariant-2a-iv n l h Log_left K_left)
                    (invariant-2a-iv n l h Log_right K_right)
                )
            )
        )
    )
)
(define-fun assert-invariant-2a-vii
    (
        (state-Gks0 <GameState_Gks0_<$$>>)
        (state-Gks0Map <GameState_Gks0Map_<$$>>)
    )
    Bool
    (let 
        (
            (Log_left (<pkg-state-Log-<$$>-Log> (<game-Gks0-<$$>-pkgstate-pkg_Log> state-Gks0)))
            (Log_right (<pkg-state-Log-<$$>-Log> (<game-Gks0Map-<$$>-pkgstate-pkg_Log> state-Gks0Map)))
        )
        (forall
            (
                (m Int)
                (h Bits_*)
            )
            (and
                (invariant-2a-vii m h Log_left)
                (invariant-2a-vii m h Log_right)
            )
        )
    )
)
(define-fun assert-invariant-2a-viii
    (
        (state-Gks0 <GameState_Gks0_<$$>>)
        (state-Gks0Map <GameState_Gks0Map_<$$>>)
    )
    Bool
    (let 
        (
            (Log_left (<pkg-state-Log-<$$>-Log> (<game-Gks0-<$$>-pkgstate-pkg_Log> state-Gks0)))
            (Log_right (<pkg-state-Log-<$$>-Log> (<game-Gks0Map-<$$>-pkgstate-pkg_Log> state-Gks0Map)))
        )
        (forall
            (
                (h Bits_*)
            )
            (let
                (
                    (n (<<func-name>> h))
                )
                (and
                    (invariant-2a-viii n h Log_left)
                    (invariant-2a-viii n h Log_right)
                )
            )
        )
    )
)
(define-fun updated-invariant-log-inverse
    (
        (state-Gks0 <GameState_Gks0_<$$>>)
        (state-Gks0Map <GameState_Gks0Map_<$$>>)
    )
    Bool
    (let
        (
            (Log_right (<pkg-state-Log-<$$>-Log> (<game-Gks0Map-<$$>-pkgstate-pkg_Log> state-Gks0Map)))
            (LogInverseDishonest_right (<pkg-state-Log-<$$>-LogInverseDishonest> (<game-Gks0Map-<$$>-pkgstate-pkg_Log> state-Gks0Map)))
            (LogInverseDishonestLevelNonZero_right (<pkg-state-Log-<$$>-LogInverseDishonestLevelNonZero> (<game-Gks0Map-<$$>-pkgstate-pkg_Log> state-Gks0Map)))
            (LogInverseDishonestLevelZero_right (<pkg-state-Log-<$$>-LogInverseDishonestLevelZero> (<game-Gks0Map-<$$>-pkgstate-pkg_Log> state-Gks0Map)))            
        )
        (forall
            (
                (k Bits_*)
            )
            (let 
                (
                    (log_inverse_right_dh (select LogInverseDishonest_right (mk-tuple2 KEY_dh k)))
                    (log_inverse_right_psk (select LogInverseDishonest_right (mk-tuple2 KEY_psk k)))
                )
                (and
                    ;Log[dh, LogInverseDishonest[(dh, k)]] = (LogInverseDishonest[(dh, k)], false, k)
                    (log_inverse_invariant Log_right log_inverse_right_dh KEY_dh k)
                    ;Log[psk, LogInverseDishonest[(psk, k)]] = (LogInverseDishonest[(psk, k)], false, k)
                    (log_inverse_invariant Log_right log_inverse_right_psk KEY_psk k)
                    ;LogInverseDishonestLevelZero[k] = None and LogInverseDishonestLevelNonZero[k] != None => LogInverseDishonestLevelNonZero[k] = LogInverseDishonest[(psk, k)]
                    (=>
                        (and
                            ((_ is mk-none) (select LogInverseDishonestLevelZero_right k))
                            (not ((_ is mk-none) (select LogInverseDishonestLevelNonZero_right k)))
                        )
                        (= (select LogInverseDishonestLevelNonZero_right k) log_inverse_right_psk)
                    )
                    ;LogInverseDishonestLevelZero[k] != None and LogInverseDishonestLevelNonZero[k] = None => LogInverseDishonestLevelZero[k] = LogInverseDishonest[(psk, k)]
                    (=>
                        (and
                            ((_ is mk-none) (select LogInverseDishonestLevelNonZero_right k))
                            (not ((_ is mk-none) (select LogInverseDishonestLevelZero_right k)))
                        )
                        (= (select LogInverseDishonestLevelZero_right k) log_inverse_right_psk)
                    )
                )
            )
        )
    )
)
; check invariants hold in the beginning
; (push 1)
; (assert (all-invariants <<game-state-game_Gks0-old>> <<game-state-game_Gks0Map-old>>))
; (check-sat)
; (pop 1)

; Prove UNQ returns the same handle for keys other than psk and dh 
; in case of psk and dh, it returns LogInverseDishonest[(n, k)] or h or aborts
; Note that whenever we call UNQ, we know that Log[h] = None

; Prove a lemma that SET returns the same handle for keys other than psk and dh (proved)
; in case of psk and dh, it returns LogInverseDishonest[(n, k)] or h
; Why do we need to prove what SET returns?

; Rename log inverse tables to FirstDishonest[LevelZero/LevelNonZero]HandleWithKey[k]
;   Is it really first handle?
;       To answer, we should analyze when it is possible to rewrite LogInverseDishonest[LevelZero/LevelNonZero]
;          We write to LogInverseDishonest only in the end
;              If we reach the end, it means no mapping has happened and not abort has triggered.
;              Namely no A, D, F aborts and no mappings.
;          We write to LogInverseDishonestLevel[Zero/NonZero] both in the end and 1 mapping
;       When we have Z pattern,
;           If the mapping is 0, NO, all tables can be rewritten.
;           If the mapping is infinity, YES, it is indeed the first handle.
;       When we have D pattern,
;           If the mapping is 0,
;               no collision of dishonest keys are allowed so YES tables are not rewritten.
;           If the mapping is 1 [only for psk]
;               only the first collision of dishonest level zero and non zero level keys are allowed
;               but YES tables are not rewritten.
;       When we have A pattern, no dishonest level zero keys can collide
;           If the mapping is 0
;               a non zero level handle can collide with a level zero handle or another non zero level handle
;               therefore NO, all tables can be rewritten.
;           If the mapping is 1 [only for psk]
;               a non zero level handle can collide with a level zero handle or another non zero level handle
;               only the first collision is mapped and tables are not rewritten then (neither LogInverseDohonest nor the the Level ones because J[k] = None implies one of them is None)
;               therefore NO, all tables can be rewritten.
;       When we have F pattern, no keys (honest or dishonest) can collide so YES.

; Prove log inverse invariants for Key.SET calls
; Prove log inverse consistency for Key.SET calls
; Prove J invariants:
;   J = None or some(True)
;   J[k] = None => LogInverseDishonestLevelZero[k] = None or LogInverseDishonestLevelNonZero[k] = None

; Prove invariant 2a (i-ii-iii-iv) is preserved during Key.SET call
;   2a (i) : Log[(n, h)] = None => K[(n, l, h)] = None
;       Proof by contradication: Imagine Log[h] = None but K[h] is not. When K[h] is set, UNQ has returned h which means Log[h] = (h, ...).
;   2a (ii) : Log[h] = (h', ...) and h != h' => K[h] = None
;       Proof by contradication: Imagine Log[h] = (h', ...) and h != h' but K[h] is not. When K[h] is set, UNQ has returned h which means Log[h] = (h, ...).
;   2a (iii) : Log[h] = (h', hon, k) and h != h' => Log[h'] = (h', hon, k)
;       Log[h] is set either in a mapping or in the end of UNQ. Only in a mapping we have h != h'.
;       We should know as a lemma that what h maps to also maps to itself.
;       To prove this:
;           When Log[h] <- (h', hon, k) is set in Log package, we should argue Log[h'] = (h', hon, k)
;           Remark: There is small technicality here. We have a trouble proving this on the left side although we prove in 2a (v) that Log_left[h] = (h, ...)
;               However, the invariant holds for the new handle to be set and Log tables (old and new) 
;               can be proved to be either the same (returning from Q) or with just the additional entry after UNQ
;               Proving the invariant holds for already existing untouched entries, though, fails if Log_old and Log_new differs in the additional entry after UNQ
;               because if Log[hx] = (h', ...) where hx != h' and hx != h (h being the query to SET(h, hon, k))
;               We don't know h' != h which can map to None in Log_old and to (h, hon, k) in Log_new if no mapping occurs or (LogInverseDishonest[(dh, k)], false, k) if infitiy mapping occurs or (LogInverseDishonest[(psk, k)], false, k) if 1 mapping occurs
;               Therefore, we should prove h does not appear on the right hand of Log's if Log[h] = None (i.e. Log package has not seen this handle before)
;               We don't need to prove it separately because if h' = h, we know from the assumption that Log[h'] = (h' ,....) but Log[h] = None (as UNQ call happens after Q call)
;           1. dh mapping:
;               We map h to (LogInverseDishonest[(dh, k)], hon, k) where hon = false
;               We need the following as a lemma:
;                   Log[dh, LogInverseDishonest[(dh, k)]] = (LogInverseDishonest[(dh, k)], false, k)
;           2. psk 1 mapping:
;               We map h to LogInverseDishonestLevelZero[k] or LogInverseDishonestLevelNonZero[k]
;               which at their positions are equal to LogInverseDishonest[(psk, k)]
;               because due to J invariant one of them is none and due to the following, the other one is LogInverseDishonest[(psk, k)]
;                   LogInverseDishonestLevelZero[k] != None and LogInverseDishonestLevelNonZero[k] = None => LogInverseDishonestLevelZero[k] = LogInverseDishonest[(psk, k)]
;                   LogInverseDishonestLevelZero[k] = None and LogInverseDishonestLevelNonZero[k] != None => LogInverseDishonestLevelNonZero[k] = LogInverseDishonest[(psk, k)]
;               Finally due to the following we are done.
;                   Log[psk, LogInverseDishonest[(psk, k)]] = (LogInverseDishonest[(psk, k)], false, k)
;               Nevertheless we have the following: (not proved)
;                   LogInverseDishonestLevelZero[k] != None => level(LogInverseDishonestLevelZero[k]) = 0
;                   LogInverseDishonestLevelNonZero[k] != None => level(LogInverseDishonestLevelNonZero[k]) != 0
;                   Log[psk, LogInverseDishonestLevelZero[k]] = (LogInverseDishonest[(psk, k)], false, k)
;                   Log[psk, LogInverseDishonestLevelNonZero[k]] = (LogInverseDishonest[(psk, k)], false, k)
;           3. in the end:
;               We set Log[h] = (h, ...) so we are done
;       (In general whatever UNQ returns maps to itself)
;   2a (iv) : Log[h] = (h, hon, k) <=> K[h] = (hon, k)
;       <= 
;           When K is set, UNQ has returned the same handle. 
;           UNQ returns the same handle when it does not do any mapping and it returns in the end. 
;           Keys and honesty bits are also othe same because the values are passed to UNQ.
;       => 
;           no mapping has occured when Log[h] = (h, ...). Therefore UNQ returns h and K[h] is set as mentioned.
; Prove invariant 2a (vii, viii, ix, x) is preserved during Key.SET call
;   2a (viii): We need the preservation of name in logs
;               which in turn needs preservation of name in log inverse
;               The reason is viii states a property for n != dh and we need to make sure name(mapped_h) != dh but name(mapped_h) = name(h)
;               another approach is to prove len(k) = len(h) for inverse tables LogInverseDihonestLevelZero[k] = h
; Prove invariant 2a is preserved during XTR, XPD, SET_0psk, DHEXP
;   We can use invariant 2a preservence after Key.SET calls as a lemma. Log and Key tables are only modified there.
; Prove invariant 2b : [needs mapping] [one-sided -> viper]
;   M_right[h] = h' => Log_right[h'] = (h', ...) 
;   Proof: Since M is set with output of SET, we need to prove if h <- SET(...) then Log[h] = (h, ...)
;   Paper proves this by analyzing returning points of h' <- SET(h, ...).
;       returning Q output h': 
;           we know Log[h] = (h', ...) from Q code. 
;           If h = h', we are done. Otherwise, use 2a (iii) and conclude Log[h'] = (h', ...)
;       returning UNQ output h' when h' != h: 
;           we know a mapping has occured. (This should be itself a lemma, namely if UNQ returns something different then game is right and n = dh or n = psk)
;           Therefore Log[h] = (h', ...) (We can state a lemma for the output of UNQ)
;           use 2a (iii) to conclude Log[h'] = (h', ...)
;       returning h in the end: (i.e. initially Log[h] = None and UNQ returned h and no mapping occured)
;           UNQ sets Log[h] = (h, ...) so we are done
;   we can prove it as an individual lemma
; Prove invariant 2c : [needs mapping] [two-sided] M_right[h] = h' <=> Log_left[h] = (h, ...)
;   i.e. if h is defined in the left, it is mapped in the right.
; Prove invariant 2d : [needs mapping] [one-sided -> viper candidate]
; Prove invariant 2e is preserved during Key.SET call :
; Prove invariant 2e is preserved during XTR, XPD, SET_0psk, DHEXP :
; Prove invariant 3 : [needs mapping] [one-sided -> viper candidate]
; Prove invariant 4 is preserved during Key.SET call :
; Prove invariant 4 is preserved during XTR, XPD, SET_0psk, DHEXP :
; Prove invariant 6: [needs mapping] [two-sided]