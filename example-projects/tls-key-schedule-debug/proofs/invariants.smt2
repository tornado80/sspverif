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
    false
)


(define-fun none-aware-level
    (
        (h Bits_*)
    )
    Int
    (let 
        (
            (level (<<func-proof-level>> h))
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
        (l Int)
        (h Bits_*)
        (Log (Array (Tuple2 Int Bits_*) (Maybe (Tuple3 Bits_* Bool Bits_*))))
        (K (Array (Tuple3 Int Int Bits_*) (Maybe (Tuple2 Bits_* Bool))))
    )
    Bool
    ; Invariant (2a) (iii) : Log[(n, h)] = (h', hon, k) and h != h' => Log[(n, h')] = (h', hon, k) and hon = false
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
                (let
                    (
                        (mapped_log_entry (maybe-get (select Log (mk-tuple2 n mapped_h))))
                    )
                    (and
                        (= (el3-3 log_entry) (el3-3 mapped_log_entry)) ; k
                        (= false (el3-2 log_entry) (el3-2 mapped_log_entry)) ; hon
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
    ; Invariant (2a) (iv) : Log[(n, h)] = (h, hon, k) iff K[(n, l, h)] = (k, hon) != none
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
        (n Int)
        (m Int)
        (l Int)
        (h Bits_*)
        (Log (Array (Tuple2 Int Bits_*) (Maybe (Tuple3 Bits_* Bool Bits_*))))
        (K (Array (Tuple3 Int Int Bits_*) (Maybe (Tuple2 Bits_* Bool))))
    )
    Bool
    ; Invariant (2a) (vii) : Log[(n', h)] != none => name(h) = n'
    (=>
        (not ((_ is mk-none) (select Log (mk-tuple2 m h))))
        (= m (<<func-proof-name>> h))
    )
)
(define-fun invariant-2a-viii
    (
        (n Int)
        (l Int)
        (h Bits_*)
        (Log (Array (Tuple2 Int Bits_*) (Maybe (Tuple3 Bits_* Bool Bits_*))))
        (K (Array (Tuple3 Int Int Bits_*) (Maybe (Tuple2 Bits_* Bool))))
    )
    Bool
    ; Invariant (2a) (viii) : Log[(n, h)] = (h', _, k) => len(k) = len(h) = len(h') and alg(h) = alg(h')
    (let
        (
            (log_entry (select Log (mk-tuple2 n h)))
        )
        (=>
            (not ((_ is mk-none) log_entry))
            (let 
                (
                    (k (el3-3 (maybe-get log_entry)))
                    (mapped_h (el3-1 (maybe-get log_entry)))
                )
                (and
                    (= (<<func-proof-handle_alg>> h) (<<func-proof-handle_alg>> mapped_h))
                    (= (<<func-proof-len_key>> k) (<<func-proof-len_alg>> (<<func-proof-handle_alg>> h)) (<<func-proof-len_alg>> (<<func-proof-handle_alg>> mapped_h)))
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
        ((_ is mk-none) (<<func-proof-level>> h))
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
            (= (maybe-get (<<func-proof-level>> h)) l)
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
                (n (<<func-proof-name>> h))
            )
            (let 
                (
                    (l (none-aware-level h))
                )
                (and
                    (invariant-2a-i n l h Log K)
                    (invariant-2a-ii n l h Log K)
                    ;(invariant-2a-iii n l h Log K) ; needs more log inverse and Log[LogInverse[k]] = (LogInverse[k], ...)
                    ;(invariant-2a-iv n l h Log K)
                    (invariant-2a-vii n m l h Log K)
                    ;(invariant-2a-viii n l h Log K)
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
                    (n (<<func-proof-name>> h))
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
                    (n (<<func-proof-name>> h))
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
        (invariant-2a-i-ii-iii-iv-vii-viii-ix-x state-Gks0 state-Gks0Map)
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
(define-fun invariant-consistent-log-inverse
    (
        (state-Gks0 <GameState_Gks0_<$$>>)
        (state-Gks0Map <GameState_Gks0Map_<$$>>)
    )
    Bool
    ; Invariant (5) for inverse maps on input keys
    ; LogInverseDishonestLevelZero_left[k] = None iff LogInverseDishonestLevelZero_right[k] = None
    ; LogInverseDishonestLevelNonZero_left[k] = None iff LogInverseDishonestLevelNonZero_right[k] = None
    ; LogInverseDishonest_left[(psk, k)] = None iff LogInverseDishonest_right[(psk, k)] = None
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
                    (dishonest_psk_left (select LogInverseDishonest_left (mk-tuple2 KEY_psk k)))
                    (dishonest_psk_right (select LogInverseDishonest_right (mk-tuple2 KEY_psk k)))
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
)
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
                (<<func-proof-level>> (maybe-get h))
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
    (=>
        (not ((_ is mk-none) h))
        (let
            (
                (entry (select Log (mk-tuple2 KEY_psk (maybe-get h))))
                (level (maybe-get (<<func-proof-level>> (maybe-get h))))
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
    (=>
        (not ((_ is mk-none) h))
        (let
            (
                (entry (select Log (mk-tuple2 n (maybe-get h))))
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
(define-fun invariant-log-inverse
    (
        (state-Gks0 <GameState_Gks0_<$$>>)
        (state-Gks0Map <GameState_Gks0Map_<$$>>)
    )
    Bool
    ; Inverse maps
    ; Log[psk, LogInverseDishonestLevelZero[k]] = (_, 0, k) and level(LogInverseDishonestLevelZero[k]) = 0
    ; Log[psk, LogInverseDishonestLevelNonZero[k]] = (_, 0, k) and level(LogInverseDishonestLevelZero[k]) != 0
    ; Log[psk, LogInverseDishonest[(psk, k)]] = (_, 0, k)
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
    (and
        ;(invariant-2 state-Gks0 state-Gks0Map)
        (invariant-log-inverse state-Gks0 state-Gks0Map)
        ;(invariant-consistent-log-inverse state-Gks0 state-Gks0Map)
    )
)

; check invariants hold in the beginning
; (push 1)
; (assert (all-invariants <<game-state-game_Gks0-old>> <<game-state-game_Gks0Map-old>>))
; (check-sat)
; (pop 1)

; Proving a lemma that SET returns the same handle for keys other thank psk and dh
; in case of psk and dh, it return LogInverseDishonest[(n, k)] or h