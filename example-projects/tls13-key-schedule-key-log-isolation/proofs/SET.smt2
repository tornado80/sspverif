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
(define-fun <relation-assume-updated-invariant-log-inverse-game_Gks0-game_Gks0Map-SET> 
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
    )
)
(define-fun <relation-assert-updated-invariant-log-inverse-game_Gks0-game_Gks0Map-SET> 
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
        )
    )
)
(define-fun <relation-assume-J-invariants-game_Gks0-game_Gks0Map-SET> 
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
        (J-invariants old-state-Gks0Map)
    )
)
(define-fun <relation-assert-J-invariants-game_Gks0-game_Gks0Map-SET> 
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
(define-fun <relation-assume-invariant-2a-iv-game_Gks0-game_Gks0Map-SET> 
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
        (assert-invariant-2a-iv old-state-Gks0 old-state-Gks0Map)
    )
)
(define-fun <relation-assert-invariant-2a-iv-game_Gks0-game_Gks0Map-SET> 
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
            (assert-invariant-2a-iv new-state-Gks0 new-state-Gks0Map)
        )
    )
)
(define-fun <relation-assume-invariant-2a-vii-game_Gks0-game_Gks0Map-SET> 
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
        (assert-invariant-2a-vii old-state-Gks0 old-state-Gks0Map)
    )
)
(define-fun <relation-assert-invariant-2a-vii-game_Gks0-game_Gks0Map-SET> 
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
            (assert-invariant-2a-vii new-state-Gks0 new-state-Gks0Map)
        )
    )
)
(define-fun <relation-lemma-SAMPLE-output-length-game_Gks0-game_Gks0Map-SET> 
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
                (input_left (<pkg-state-Sample-<$$>-input> (<game-Gks0-<$$>-pkgstate-pkg_Sample> new-state-Gks0)))
                (input_right (<pkg-state-Sample-<$$>-input> (<game-Gks0-<$$>-pkgstate-pkg_Sample> new-state-Gks0)))
                (output_left (<pkg-state-Sample-<$$>-output> (<game-Gks0Map-<$$>-pkgstate-pkg_Sample> new-state-Gks0Map)))
                (output_right (<pkg-state-Sample-<$$>-output> (<game-Gks0Map-<$$>-pkgstate-pkg_Sample> new-state-Gks0Map)))
                
                (k256_left (<pkg-state-Sample-<$$>-k256> (<game-Gks0-<$$>-pkgstate-pkg_Sample> new-state-Gks0)))
                (k384_left (<pkg-state-Sample-<$$>-k384> (<game-Gks0-<$$>-pkgstate-pkg_Sample> new-state-Gks0)))
                (k512_left (<pkg-state-Sample-<$$>-k512> (<game-Gks0-<$$>-pkgstate-pkg_Sample> new-state-Gks0)))
                (k256_right (<pkg-state-Sample-<$$>-k256> (<game-Gks0Map-<$$>-pkgstate-pkg_Sample> new-state-Gks0Map)))
                (k384_right (<pkg-state-Sample-<$$>-k384> (<game-Gks0Map-<$$>-pkgstate-pkg_Sample> new-state-Gks0Map)))
                (k512_right (<pkg-state-Sample-<$$>-k512> (<game-Gks0Map-<$$>-pkgstate-pkg_Sample> new-state-Gks0Map)))
            )
            (and
                (= (<<func-proof-len_key>> output_left) input_left)
                (= (<<func-proof-len_key>> output_right) input_right)
                (= (<<func-proof-len_key>> (<<func-proof-cast256>> k256_left)) 256)
                (= (<<func-proof-len_key>> (<<func-proof-cast384>> k384_left)) 384)
                (= (<<func-proof-len_key>> (<<func-proof-cast512>> k512_left)) 512)
                (= (<<func-proof-len_key>> (<<func-proof-cast256>> k256_right)) 256)
                (= (<<func-proof-len_key>> (<<func-proof-cast384>> k384_right)) 384)
                (= (<<func-proof-len_key>> (<<func-proof-cast512>> k512_right)) 512)
            )
        )
    )
)
(define-fun <relation-assume-invariant-2a-viii-game_Gks0-game_Gks0Map-SET> 
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
        (assert-invariant-2a-viii old-state-Gks0 old-state-Gks0Map)
        ;(assert-invariant-2a-iii old-state-Gks0 old-state-Gks0Map)
    )
)
(define-fun <relation-assert-invariant-2a-viii-game_Gks0-game_Gks0Map-SET> 
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
                (Log_left (<pkg-state-Log-<$$>-Log> (<game-Gks0-<$$>-pkgstate-pkg_Log> new-state-Gks0)))
                (checkpoint_left (<pkg-state-Key-<$$>-checkpoint> (<game-Gks0-<$$>-pkgstate-pkg_Key> new-state-Gks0)))
                (len_handle_left (<pkg-state-Key-<$$>-len_handle> (<game-Gks0-<$$>-pkgstate-pkg_Key> new-state-Gks0)))
                (input_left (<pkg-state-Sample-<$$>-input> (<game-Gks0-<$$>-pkgstate-pkg_Sample> new-state-Gks0)))
                (input_right (<pkg-state-Sample-<$$>-input> (<game-Gks0-<$$>-pkgstate-pkg_Sample> new-state-Gks0)))
                (raw_key_left (<pkg-state-Key-<$$>-raw_key> (<game-Gks0-<$$>-pkgstate-pkg_Key> new-state-Gks0)))
                (Log_right (<pkg-state-Log-<$$>-Log> (<game-Gks0Map-<$$>-pkgstate-pkg_Log> new-state-Gks0Map)))
                (Log_right_old (<pkg-state-Log-<$$>-Log> (<game-Gks0Map-<$$>-pkgstate-pkg_Log> old-state-Gks0Map)))
                (len_handle_right (<pkg-state-Key-<$$>-len_handle> (<game-Gks0Map-<$$>-pkgstate-pkg_Key> new-state-Gks0Map)))
                (checkpoint_right (<pkg-state-Key-<$$>-checkpoint> (<game-Gks0Map-<$$>-pkgstate-pkg_Key> new-state-Gks0Map)))
            )
            (and
                (let
                    (
                        (log_entry (select Log_right (mk-tuple2 n h)))
                    )
                    (=>
                        (and (not ((_ is mk-none) log_entry)) (not (= n KEY_dh)))
                        (let 
                            (
                                (ks (el3-3 (maybe-get log_entry)))
                                (mapped_h (el3-1 (maybe-get log_entry)))
                            )
                            (and
                                (=>
                                    (= h mapped_h)
                                    (invariant-2a-viii n h Log_right)
                                )
                                (=>
                                    (not (= h mapped_h))
                                    (and 
                                        (invariant-2a-viii n h Log_right)
                                        (= ks (el3-3 (maybe-get (select Log_right_old (mk-tuple2 n mapped_h)))))
                                        (invariant-2a-iii n h Log_right_old)
                                        (= n (<<func-proof-name>> mapped_h))
                                        (invariant-2a-viii (<<func-proof-name>> mapped_h) mapped_h Log_right_old)
                                        (=>
                                            (= n (<<func-proof-name>> mapped_h))
                                            (= (<<func-proof-len_key>> ks) (<<func-proof-len_alg>> (<<func-proof-handle_alg>> mapped_h)))
                                        )
                                    )
                                )
                                (= (<<func-proof-len_key>> ks) len_handle_right)
                                (= len_handle_right (<<func-proof-len_alg>> (<<func-proof-handle_alg>> h)))
                                (= (<<func-proof-handle_alg>> h) (<<func-proof-handle_alg>> mapped_h))
                                (= (<<func-proof-len_key>> ks) (<<func-proof-len_alg>> (<<func-proof-handle_alg>> h)) (<<func-proof-len_alg>> (<<func-proof-handle_alg>> mapped_h)))
                            )
                        )
                    )
                )
                (invariant-2a-viii n h Log_left)
                (invariant-2a-viii n h Log_right)
                (assert-invariant-2a-viii new-state-Gks0 new-state-Gks0Map)
            )
        )
    )
)
(define-fun <relation-assume-invariant-log-preserves-name-game_Gks0-game_Gks0Map-SET> 
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
    (invariant-log-preserves-name old-state-Gks0 old-state-Gks0Map)
)
(define-fun <relation-assert-invariant-log-preserves-name-game_Gks0-game_Gks0Map-SET> 
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
        (invariant-log-preserves-name new-state-Gks0 new-state-Gks0Map)
    )
)
(define-fun <relation-lemma-injectivity-of-len_alg-game_Gks0-game_Gks0Map-SET>
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
    (forall
        (
            (alg1 Int)
            (alg2 Int)
        )
        (=>
            (= (<<func-proof-len_alg>> alg1) (<<func-proof-len_alg>> alg2))
            (= alg1 alg2)
        )
    )
)
(define-fun <relation-assume-invariant-log-inverse-name-game_Gks0-game_Gks0Map-SET> 
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
    (invariant-log-inverse-name old-state-Gks0 old-state-Gks0Map)
)
(define-fun <relation-assert-invariant-log-inverse-name-game_Gks0-game_Gks0Map-SET> 
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
        (invariant-log-inverse-name new-state-Gks0 new-state-Gks0Map)
    )
)
(define-fun <relation-assume-invariant-2e-game_Gks0-game_Gks0Map-SET> 
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
    (invariant-2e old-state-Gks0 old-state-Gks0Map)
)
(define-fun <relation-assert-invariant-2e-game_Gks0-game_Gks0Map-SET> 
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
        (invariant-2e new-state-Gks0 new-state-Gks0Map)
    )
)
(define-fun <relation-assume-invariant-2a-ix-and-2a-x-game_Gks0-game_Gks0Map-SET> 
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
    (assert-invariant-2a-ix-and-2a-x old-state-Gks0 old-state-Gks0Map)
)
(define-fun <relation-assert-invariant-2a-ix-and-2a-x-game_Gks0-game_Gks0Map-SET> 
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
        (assert-invariant-2a-ix-and-2a-x new-state-Gks0 new-state-Gks0Map)
    )
)
(define-fun <relation-assume-invariant-consistent-log-inverse-level-zero-psk-game_Gks0-game_Gks0Map-SET> 
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
    (invariant-consistent-log-inverse-level-zero-psk old-state-Gks0 old-state-Gks0Map)
)
(define-fun <relation-assert-invariant-consistent-log-inverse-level-zero-psk-game_Gks0-game_Gks0Map-SET> 
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
        (invariant-consistent-log-inverse-level-zero-psk new-state-Gks0 new-state-Gks0Map)
    )
)
(define-fun <relation-assume-invariant-consistent-log-for-dh-and-psk-game_Gks0-game_Gks0Map-SET> 
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
    (invariant-consistent-log-for-dh-and-psk old-state-Gks0 old-state-Gks0Map)
)
(define-fun <relation-assert-invariant-consistent-log-for-dh-and-psk-game_Gks0-game_Gks0Map-SET> 
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
        (invariant-consistent-log-for-dh-and-psk new-state-Gks0 new-state-Gks0Map)
    )
)

(define-fun <relation-assume-invariant-2a-v-game_Gks0-game_Gks0Map-SET> 
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
    (invariant-2a-v old-state-Gks0 old-state-Gks0Map)
)
(define-fun <relation-lemma-rand-is-eq-game_Gks0-game_Gks0Map-SET> 
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
        (rand-is-eq 0 0 (<game-Gks0-<$$>-rand-0> old-state-Gks0) (<game-Gks0Map-<$$>-rand-0> old-state-Gks0Map))
        (rand-is-eq 1 1 (<game-Gks0-<$$>-rand-1> old-state-Gks0) (<game-Gks0Map-<$$>-rand-1> old-state-Gks0Map))
        (rand-is-eq 2 2 (<game-Gks0-<$$>-rand-2> old-state-Gks0) (<game-Gks0Map-<$$>-rand-2> old-state-Gks0Map))
    )
)
(define-fun <relation-lemma-randomness-mapping-game_Gks0-game_Gks0Map-SET> 
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
        (randomness-mapping-SET (<game-Gks0-<$$>-rand-0> old-state-Gks0) (<game-Gks0Map-<$$>-rand-0> old-state-Gks0Map) 0 0 (<game-Gks0-<$$>-rand-0> old-state-Gks0) (<game-Gks0Map-<$$>-rand-0> old-state-Gks0Map))
        (randomness-mapping-SET (<game-Gks0-<$$>-rand-1> old-state-Gks0) (<game-Gks0Map-<$$>-rand-1> old-state-Gks0Map) 1 1 (<game-Gks0-<$$>-rand-1> old-state-Gks0) (<game-Gks0Map-<$$>-rand-1> old-state-Gks0Map))
        (randomness-mapping-SET (<game-Gks0-<$$>-rand-2> old-state-Gks0) (<game-Gks0Map-<$$>-rand-2> old-state-Gks0Map) 2 2 (<game-Gks0-<$$>-rand-2> old-state-Gks0) (<game-Gks0Map-<$$>-rand-2> old-state-Gks0Map))
    )
)