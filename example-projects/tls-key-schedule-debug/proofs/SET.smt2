(define-fun <relation-lemma-SET-returns-same-handle-for-non-dh-and-psk-game_Gks0-game_Gks0Map-SET> 
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-SET-Gks0 <OracleReturn-Gks0-<$$>-Key-<$$>-SET>)
        (return-SET-Gks0Map <OracleReturn-Gks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (=>
        (and (not (= n KEY_psk)) (not (= n KEY_dh)))
        (=
            (return-value (<oracle-return-Gks0Map-<$$>-Key-<$$>-SET-return-value-or-abort> return-SET-Gks0Map))
            (return-value (<oracle-return-Gks0-<$$>-Key-<$$>-SET-return-value-or-abort> return-SET-Gks0))
            h
        )
    )
)
(define-fun <relation-lemma-UNQ-preserves-invariant-2a-iii-game_Gks0-game_Gks0Map-SET> 
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-SET-Gks0 <OracleReturn-Gks0-<$$>-Key-<$$>-SET>)
        (return-SET-Gks0Map <OracleReturn-Gks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    true
)
(define-fun J-invariants 
    (
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
    )
    Bool
    (let 
        (
            (J (<pkg-state-Log-<$$>-J> (<game-Gks0Map-<$$>-pkgstate-pkg_Log> old-state-Gks0Map)))
            (LogInverseDishonestLevelZero (<pkg-state-Log-<$$>-LogInverseDishonestLevelZero> (<game-Gks0Map-<$$>-pkgstate-pkg_Log> old-state-Gks0Map)))
            (LogInverseDishonestLevelNonZero (<pkg-state-Log-<$$>-LogInverseDishonestLevelNonZero> (<game-Gks0Map-<$$>-pkgstate-pkg_Log> old-state-Gks0Map)))
        )
        (forall
            (
                (k Bits_*)
            )
            (let 
                (
                    (J_k (select J k))
                    (LogInverseDishonestLevelZero_k (select LogInverseDishonestLevelZero k))
                    (LogInverseDishonestLevelNonZero_k (select LogInverseDishonestLevelNonZero k))
                )
                (and 
                    ;   J = None or some(True)
                    (or
                        ((_ is mk-none) J_k)
                        (= J_k (mk-some true))
                    )
                    ;   J[k] = None => LogInverseDishonestLevelZero[k] = None or LogInverseDishonestLevelNonZero[k] = None
                    (=>
                        ((_ is mk-none) J_k)
                        (or
                            ((_ is mk-none) LogInverseDishonestLevelZero_k)
                            ((_ is mk-none) LogInverseDishonestLevelNonZero_k)
                        )
                    )
                )
            )
        )
    )
)
(define-fun <relation-assume-other-invariants-game_Gks0-game_Gks0Map-SET> 
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-SET-Gks0 <OracleReturn-Gks0-<$$>-Key-<$$>-SET>)
        (return-SET-Gks0Map <OracleReturn-Gks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (and
        (updated-invariant-log-inverse old-state-Gks0 old-state-Gks0Map)
        (J-invariants old-state-Gks0Map)
    )
)
(define-fun <relation-assert-other-invariants-game_Gks0-game_Gks0Map-SET> 
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-SET-Gks0 <OracleReturn-Gks0-<$$>-Key-<$$>-SET>)
        (return-SET-Gks0Map <OracleReturn-Gks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (let 
        (
            (new-state-Gks0 (<oracle-return-Gks0-<$$>-Key-<$$>-SET-game-state> return-SET-Gks0))
            (new-state-Gks0Map (<oracle-return-Gks0Map-<$$>-Key-<$$>-SET-game-state> return-SET-Gks0Map))
        )
        (and
            (updated-invariant-log-inverse new-state-Gks0 new-state-Gks0Map)
            (J-invariants new-state-Gks0Map)
        )
    )
)
(define-fun <relation-assume-invariant-2a-iii-game_Gks0-game_Gks0Map-SET> 
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-SET-Gks0 <OracleReturn-Gks0-<$$>-Key-<$$>-SET>)
        (return-SET-Gks0Map <OracleReturn-Gks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (assert-invariant-2a-iii old-state-Gks0 old-state-Gks0Map)
)
(define-fun <relation-assert-invariant-2a-iii-game_Gks0-game_Gks0Map-SET> 
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-SET-Gks0 <OracleReturn-Gks0-<$$>-Key-<$$>-SET>)
        (return-SET-Gks0Map <OracleReturn-Gks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (let 
        (
            (new-state-Gks0 (<oracle-return-Gks0-<$$>-Key-<$$>-SET-game-state> return-SET-Gks0))
            (new-state-Gks0Map (<oracle-return-Gks0Map-<$$>-Key-<$$>-SET-game-state> return-SET-Gks0Map))
        )
        (let 
            (
                (Log_old (<pkg-state-Log-<$$>-Log> (<game-Gks0-<$$>-pkgstate-pkg_Log> old-state-Gks0)))
                (Log_new (<pkg-state-Log-<$$>-Log> (<game-Gks0-<$$>-pkgstate-pkg_Log> new-state-Gks0)))
                (returnPoint (<pkg-state-Log-<$$>-ReturnPoint> (<game-Gks0-<$$>-pkgstate-pkg_Log> new-state-Gks0)))
                (checkpoint (<pkg-state-Key-<$$>-checkpoint> (<game-Gks0-<$$>-pkgstate-pkg_Key> new-state-Gks0)))
            )
            (and 
                (assert-invariant-2a-iii new-state-Gks0 new-state-Gks0Map)
                (=>
                    false
                    (=> 
                        (= n KEY_dh)
                        (and 
                            (=>
                                ((_ is mk-none) (select Log_old (mk-tuple2 n h)))
                                (= Log_new (store Log_old (mk-tuple2 n h) (mk-some (mk-tuple3 h hon k))))
                            )
                            (or (= Log_new (store Log_old (mk-tuple2 n h) (mk-some (mk-tuple3 h hon k)))) (= Log_new Log_old))
                            (invariant-2a-iii (<<func-proof-name>> h) h Log_new)
                            (assert-invariant-2a-iii new-state-Gks0 new-state-Gks0Map)
                            (forall
                                (
                                    (hp Bits_*)
                                )
                                (let
                                    (
                                        (n (<<func-proof-name>> hp))
                                    )
                                    (=>
                                        (not (= hp h))
                                        (and 
                                            (let 
                                                (
                                                    (log_old_entry (select Log_old (mk-tuple2 n hp)))
                                                    (log_new_entry (select Log_new (mk-tuple2 n hp)))
                                                )
                                                (and
                                                    (= log_old_entry log_new_entry)
                                                    (=>
                                                        (not ((_ is mk-none) (select Log_old (mk-tuple2 n hp))))
                                                        (and 
                                                            (= (el3-1 (maybe-get log_old_entry)) (el3-1 (maybe-get log_new_entry)))
                                                            (= (el3-1 (maybe-get log_old_entry)) (el3-1 (maybe-get (select Log_old (mk-tuple2 n (el3-1 (maybe-get log_old_entry)))))) )
                                                            (not ((_ is mk-none) (select Log_old (mk-tuple2 n (el3-1 (maybe-get log_old_entry))))))
                                                            (=>
                                                                (not (= (el3-1 (maybe-get log_old_entry)) h))
                                                                (invariant-2a-iii n hp Log_new)
                                                            )
                                                            (=> 
                                                                (= (el3-1 (maybe-get log_old_entry)) h)
                                                                true
                                                                ;(not ((_ is mk-none) (select Log_old (mk-tuple2 n h))))
                                                            )
                                                            ;(= (select Log_old (mk-tuple2 n (el3-1 (maybe-get log_old_entry)))) (select Log_new (mk-tuple2 n (el3-1 (maybe-get log_new_entry)))))
                                                        )
                                                        
                                                    )
                                                )
                                            )
                                        
                                            (invariant-2a-iii n hp Log_old)
                                            (invariant-2a-iii n hp Log_new)
                                        )
                                        ;(invariant-2a-iii n h Log_right)
                                    )
                                )
                            )
                        )
                    )
                    (=> 
                        (not (= n KEY_psk))
                        (assert-invariant-2a-iii new-state-Gks0 new-state-Gks0Map)
                    )
                    (=>
                        (= n KEY_psk)
                        (assert-invariant-2a-iii new-state-Gks0 new-state-Gks0Map)
                        ;(=>
                        ;    (invariant-2a-iii (<<func-proof-name>> h) h Log_new)
                        ;    (assert-invariant-2a-iii new-state-Gks0 new-state-Gks0Map)
                        ;)
                    )
                )
            )


        )

    )
)
(define-fun invariants-2a-i-and-2a-ii
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
                    (n (<<func-proof-name>> h))
                )
                (let 
                    (
                        (l (none-aware-level h))
                    )
                    (and
                        (invariant-2a-i n l h Log_left K_left)
                        (invariant-2a-i n l h Log_right K_right)
                        (invariant-2a-ii n l h Log_left K_left)
                        (invariant-2a-ii n l h Log_right K_right)
                    )
                )
            )
        )
    )
)
(define-fun <relation-assume-invariants-2a-i-and-2a-ii-game_Gks0-game_Gks0Map-SET> 
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-SET-Gks0 <OracleReturn-Gks0-<$$>-Key-<$$>-SET>)
        (return-SET-Gks0Map <OracleReturn-Gks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (invariants-2a-i-and-2a-ii old-state-Gks0 old-state-Gks0Map)
)
(define-fun <relation-assert-invariants-2a-i-and-2a-ii-game_Gks0-game_Gks0Map-SET> 
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-SET-Gks0 <OracleReturn-Gks0-<$$>-Key-<$$>-SET>)
        (return-SET-Gks0Map <OracleReturn-Gks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (let 
        (
            (new-state-Gks0 (<oracle-return-Gks0-<$$>-Key-<$$>-SET-game-state> return-SET-Gks0))
            (new-state-Gks0Map (<oracle-return-Gks0Map-<$$>-Key-<$$>-SET-game-state> return-SET-Gks0Map))
        )
        (invariants-2a-i-and-2a-ii new-state-Gks0 new-state-Gks0Map)
    )
)
(define-fun <relation-assume-invariants-2a-v-and-2a-vi-game_Gks0-game_Gks0Map-SET> 
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-SET-Gks0 <OracleReturn-Gks0-<$$>-Key-<$$>-SET>)
        (return-SET-Gks0Map <OracleReturn-Gks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (and
        (invariant-2a-v old-state-Gks0 old-state-Gks0Map)
        (invariant-2a-vi old-state-Gks0 old-state-Gks0Map)
    )
)
(define-fun <relation-assert-invariants-2a-v-and-2a-vi-game_Gks0-game_Gks0Map-SET> 
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-SET-Gks0 <OracleReturn-Gks0-<$$>-Key-<$$>-SET>)
        (return-SET-Gks0Map <OracleReturn-Gks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (let 
        (
            (new-state-Gks0 (<oracle-return-Gks0-<$$>-Key-<$$>-SET-game-state> return-SET-Gks0))
            (new-state-Gks0Map (<oracle-return-Gks0Map-<$$>-Key-<$$>-SET-game-state> return-SET-Gks0Map))
        )
        (and
            (invariant-2a-v new-state-Gks0 new-state-Gks0Map)
            (invariant-2a-vi new-state-Gks0 new-state-Gks0Map)
        )
    )
)
