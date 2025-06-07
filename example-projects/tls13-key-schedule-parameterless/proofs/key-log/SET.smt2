(define-fun <relation-lemma-SET-returns-same-handle-for-non-dh-and-psk-game_KeyLogGks0-game_KeyLogGks0Map-SET> 
    (
        (old-state-KeyLogGks0 <GameState_KeyLogGks0_<$$>>)
        (old-state-KeyLogGks0Map <GameState_KeyLogGks0Map_<$$>>)
        (return-SET-KeyLogGks0 <OracleReturn-KeyLogGks0-<$$>-Key-<$$>-SET>)
        (return-SET-KeyLogGks0Map <OracleReturn-KeyLogGks0Map-<$$>-Key-<$$>-SET>)
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
            (return-value (<oracle-return-KeyLogGks0Map-<$$>-Key-<$$>-SET-return-value-or-abort> return-SET-KeyLogGks0Map))
            (return-value (<oracle-return-KeyLogGks0-<$$>-Key-<$$>-SET-return-value-or-abort> return-SET-KeyLogGks0))
            h
        )
    )
)
(define-fun <relation-lemma-UNQ-preserves-invariant-2a-iii-game_KeyLogGks0-game_KeyLogGks0Map-SET> 
    (
        (old-state-KeyLogGks0 <GameState_KeyLogGks0_<$$>>)
        (old-state-KeyLogGks0Map <GameState_KeyLogGks0Map_<$$>>)
        (return-SET-KeyLogGks0 <OracleReturn-KeyLogGks0-<$$>-Key-<$$>-SET>)
        (return-SET-KeyLogGks0Map <OracleReturn-KeyLogGks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    true
)
(define-fun <relation-assume-updated-invariant-log-inverse-game_KeyLogGks0-game_KeyLogGks0Map-SET> 
    (
        (old-state-KeyLogGks0 <GameState_KeyLogGks0_<$$>>)
        (old-state-KeyLogGks0Map <GameState_KeyLogGks0Map_<$$>>)
        (return-SET-KeyLogGks0 <OracleReturn-KeyLogGks0-<$$>-Key-<$$>-SET>)
        (return-SET-KeyLogGks0Map <OracleReturn-KeyLogGks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (and
        (updated-invariant-log-inverse old-state-KeyLogGks0 old-state-KeyLogGks0Map)
    )
)
(define-fun <relation-assert-updated-invariant-log-inverse-game_KeyLogGks0-game_KeyLogGks0Map-SET> 
    (
        (old-state-KeyLogGks0 <GameState_KeyLogGks0_<$$>>)
        (old-state-KeyLogGks0Map <GameState_KeyLogGks0Map_<$$>>)
        (return-SET-KeyLogGks0 <OracleReturn-KeyLogGks0-<$$>-Key-<$$>-SET>)
        (return-SET-KeyLogGks0Map <OracleReturn-KeyLogGks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (let 
        (
            (new-state-KeyLogGks0 (<oracle-return-KeyLogGks0-<$$>-Key-<$$>-SET-game-state> return-SET-KeyLogGks0))
            (new-state-KeyLogGks0Map (<oracle-return-KeyLogGks0Map-<$$>-Key-<$$>-SET-game-state> return-SET-KeyLogGks0Map))
        )
        (and
            (updated-invariant-log-inverse new-state-KeyLogGks0 new-state-KeyLogGks0Map)
        )
    )
)
(define-fun <relation-assume-J-invariants-game_KeyLogGks0-game_KeyLogGks0Map-SET> 
    (
        (old-state-KeyLogGks0 <GameState_KeyLogGks0_<$$>>)
        (old-state-KeyLogGks0Map <GameState_KeyLogGks0Map_<$$>>)
        (return-SET-KeyLogGks0 <OracleReturn-KeyLogGks0-<$$>-Key-<$$>-SET>)
        (return-SET-KeyLogGks0Map <OracleReturn-KeyLogGks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (and
        (J-invariants old-state-KeyLogGks0Map)
    )
)
(define-fun <relation-assert-J-invariants-game_KeyLogGks0-game_KeyLogGks0Map-SET> 
    (
        (old-state-KeyLogGks0 <GameState_KeyLogGks0_<$$>>)
        (old-state-KeyLogGks0Map <GameState_KeyLogGks0Map_<$$>>)
        (return-SET-KeyLogGks0 <OracleReturn-KeyLogGks0-<$$>-Key-<$$>-SET>)
        (return-SET-KeyLogGks0Map <OracleReturn-KeyLogGks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (let 
        (
            (new-state-KeyLogGks0 (<oracle-return-KeyLogGks0-<$$>-Key-<$$>-SET-game-state> return-SET-KeyLogGks0))
            (new-state-KeyLogGks0Map (<oracle-return-KeyLogGks0Map-<$$>-Key-<$$>-SET-game-state> return-SET-KeyLogGks0Map))
        )
        (and
            (J-invariants new-state-KeyLogGks0Map)
        )
    )
)
(define-fun <relation-assume-invariant-2a-iii-game_KeyLogGks0-game_KeyLogGks0Map-SET> 
    (
        (old-state-KeyLogGks0 <GameState_KeyLogGks0_<$$>>)
        (old-state-KeyLogGks0Map <GameState_KeyLogGks0Map_<$$>>)
        (return-SET-KeyLogGks0 <OracleReturn-KeyLogGks0-<$$>-Key-<$$>-SET>)
        (return-SET-KeyLogGks0Map <OracleReturn-KeyLogGks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (assert-invariant-2a-iii old-state-KeyLogGks0 old-state-KeyLogGks0Map)
)
(define-fun <relation-assert-invariant-2a-iii-game_KeyLogGks0-game_KeyLogGks0Map-SET> 
    (
        (old-state-KeyLogGks0 <GameState_KeyLogGks0_<$$>>)
        (old-state-KeyLogGks0Map <GameState_KeyLogGks0Map_<$$>>)
        (return-SET-KeyLogGks0 <OracleReturn-KeyLogGks0-<$$>-Key-<$$>-SET>)
        (return-SET-KeyLogGks0Map <OracleReturn-KeyLogGks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (let 
        (
            (new-state-KeyLogGks0 (<oracle-return-KeyLogGks0-<$$>-Key-<$$>-SET-game-state> return-SET-KeyLogGks0))
            (new-state-KeyLogGks0Map (<oracle-return-KeyLogGks0Map-<$$>-Key-<$$>-SET-game-state> return-SET-KeyLogGks0Map))
        )
        (let 
            (
                (Log_old (<pkg-state-Log-<$$>-Log> (<game-KeyLogGks0-<$$>-pkgstate-pkg_Log> old-state-KeyLogGks0)))
                (Log_new (<pkg-state-Log-<$$>-Log> (<game-KeyLogGks0-<$$>-pkgstate-pkg_Log> new-state-KeyLogGks0)))
                (returnPoint (<pkg-state-Log-<$$>-ReturnPoint> (<game-KeyLogGks0-<$$>-pkgstate-pkg_Log> new-state-KeyLogGks0)))
                (checkpoint (<pkg-state-Key-<$$>-checkpoint> (<game-KeyLogGks0-<$$>-pkgstate-pkg_Key> new-state-KeyLogGks0)))
            )
            (and 
                (assert-invariant-2a-iii new-state-KeyLogGks0 new-state-KeyLogGks0Map)
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
                            (invariant-2a-iii (<<func-name>> h) h Log_new)
                            (assert-invariant-2a-iii new-state-KeyLogGks0 new-state-KeyLogGks0Map)
                            (forall
                                (
                                    (hp Bits_*)
                                )
                                (let
                                    (
                                        (n (<<func-name>> hp))
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
                        (assert-invariant-2a-iii new-state-KeyLogGks0 new-state-KeyLogGks0Map)
                    )
                    (=>
                        (= n KEY_psk)
                        (assert-invariant-2a-iii new-state-KeyLogGks0 new-state-KeyLogGks0Map)
                        ;(=>
                        ;    (invariant-2a-iii (<<func-name>> h) h Log_new)
                        ;    (assert-invariant-2a-iii new-state-KeyLogGks0 new-state-KeyLogGks0Map)
                        ;)
                    )
                )
            )


        )

    )
)
(define-fun invariants-2a-i-and-2a-ii
    (
        (state-KeyLogGks0 <GameState_KeyLogGks0_<$$>>)
        (state-KeyLogGks0Map <GameState_KeyLogGks0Map_<$$>>)
    )
    Bool
    (let 
        (
            (Log_left (<pkg-state-Log-<$$>-Log> (<game-KeyLogGks0-<$$>-pkgstate-pkg_Log> state-KeyLogGks0)))
            (Log_right (<pkg-state-Log-<$$>-Log> (<game-KeyLogGks0Map-<$$>-pkgstate-pkg_Log> state-KeyLogGks0Map)))
            (K_left (<pkg-state-Key-<$$>-K> (<game-KeyLogGks0-<$$>-pkgstate-pkg_Key> state-KeyLogGks0)))
            (K_right (<pkg-state-Key-<$$>-K> (<game-KeyLogGks0Map-<$$>-pkgstate-pkg_Key> state-KeyLogGks0Map)))
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
(define-fun <relation-assume-invariants-2a-i-and-2a-ii-game_KeyLogGks0-game_KeyLogGks0Map-SET> 
    (
        (old-state-KeyLogGks0 <GameState_KeyLogGks0_<$$>>)
        (old-state-KeyLogGks0Map <GameState_KeyLogGks0Map_<$$>>)
        (return-SET-KeyLogGks0 <OracleReturn-KeyLogGks0-<$$>-Key-<$$>-SET>)
        (return-SET-KeyLogGks0Map <OracleReturn-KeyLogGks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (invariants-2a-i-and-2a-ii old-state-KeyLogGks0 old-state-KeyLogGks0Map)
)
(define-fun <relation-assert-invariants-2a-i-and-2a-ii-game_KeyLogGks0-game_KeyLogGks0Map-SET> 
    (
        (old-state-KeyLogGks0 <GameState_KeyLogGks0_<$$>>)
        (old-state-KeyLogGks0Map <GameState_KeyLogGks0Map_<$$>>)
        (return-SET-KeyLogGks0 <OracleReturn-KeyLogGks0-<$$>-Key-<$$>-SET>)
        (return-SET-KeyLogGks0Map <OracleReturn-KeyLogGks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (let 
        (
            (new-state-KeyLogGks0 (<oracle-return-KeyLogGks0-<$$>-Key-<$$>-SET-game-state> return-SET-KeyLogGks0))
            (new-state-KeyLogGks0Map (<oracle-return-KeyLogGks0Map-<$$>-Key-<$$>-SET-game-state> return-SET-KeyLogGks0Map))
        )
        (invariants-2a-i-and-2a-ii new-state-KeyLogGks0 new-state-KeyLogGks0Map)
    )
)
(define-fun <relation-assume-invariants-2a-v-and-2a-vi-game_KeyLogGks0-game_KeyLogGks0Map-SET> 
    (
        (old-state-KeyLogGks0 <GameState_KeyLogGks0_<$$>>)
        (old-state-KeyLogGks0Map <GameState_KeyLogGks0Map_<$$>>)
        (return-SET-KeyLogGks0 <OracleReturn-KeyLogGks0-<$$>-Key-<$$>-SET>)
        (return-SET-KeyLogGks0Map <OracleReturn-KeyLogGks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (and
        (invariant-2a-v old-state-KeyLogGks0 old-state-KeyLogGks0Map)
        (invariant-2a-vi old-state-KeyLogGks0 old-state-KeyLogGks0Map)
    )
)
(define-fun <relation-assert-invariants-2a-v-and-2a-vi-game_KeyLogGks0-game_KeyLogGks0Map-SET> 
    (
        (old-state-KeyLogGks0 <GameState_KeyLogGks0_<$$>>)
        (old-state-KeyLogGks0Map <GameState_KeyLogGks0Map_<$$>>)
        (return-SET-KeyLogGks0 <OracleReturn-KeyLogGks0-<$$>-Key-<$$>-SET>)
        (return-SET-KeyLogGks0Map <OracleReturn-KeyLogGks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (let 
        (
            (new-state-KeyLogGks0 (<oracle-return-KeyLogGks0-<$$>-Key-<$$>-SET-game-state> return-SET-KeyLogGks0))
            (new-state-KeyLogGks0Map (<oracle-return-KeyLogGks0Map-<$$>-Key-<$$>-SET-game-state> return-SET-KeyLogGks0Map))
        )
        (and
            (invariant-2a-v new-state-KeyLogGks0 new-state-KeyLogGks0Map)
            (invariant-2a-vi new-state-KeyLogGks0 new-state-KeyLogGks0Map)
        )
    )
)
(define-fun <relation-assume-invariant-2a-iv-game_KeyLogGks0-game_KeyLogGks0Map-SET> 
    (
        (old-state-KeyLogGks0 <GameState_KeyLogGks0_<$$>>)
        (old-state-KeyLogGks0Map <GameState_KeyLogGks0Map_<$$>>)
        (return-SET-KeyLogGks0 <OracleReturn-KeyLogGks0-<$$>-Key-<$$>-SET>)
        (return-SET-KeyLogGks0Map <OracleReturn-KeyLogGks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (and
        (assert-invariant-2a-iv old-state-KeyLogGks0 old-state-KeyLogGks0Map)
    )
)
(define-fun <relation-assert-invariant-2a-iv-game_KeyLogGks0-game_KeyLogGks0Map-SET> 
    (
        (old-state-KeyLogGks0 <GameState_KeyLogGks0_<$$>>)
        (old-state-KeyLogGks0Map <GameState_KeyLogGks0Map_<$$>>)
        (return-SET-KeyLogGks0 <OracleReturn-KeyLogGks0-<$$>-Key-<$$>-SET>)
        (return-SET-KeyLogGks0Map <OracleReturn-KeyLogGks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (let 
        (
            (new-state-KeyLogGks0 (<oracle-return-KeyLogGks0-<$$>-Key-<$$>-SET-game-state> return-SET-KeyLogGks0))
            (new-state-KeyLogGks0Map (<oracle-return-KeyLogGks0Map-<$$>-Key-<$$>-SET-game-state> return-SET-KeyLogGks0Map))
        )
        (and
            (assert-invariant-2a-iv new-state-KeyLogGks0 new-state-KeyLogGks0Map)
        )
    )
)
(define-fun <relation-assume-invariant-2a-vii-game_KeyLogGks0-game_KeyLogGks0Map-SET> 
    (
        (old-state-KeyLogGks0 <GameState_KeyLogGks0_<$$>>)
        (old-state-KeyLogGks0Map <GameState_KeyLogGks0Map_<$$>>)
        (return-SET-KeyLogGks0 <OracleReturn-KeyLogGks0-<$$>-Key-<$$>-SET>)
        (return-SET-KeyLogGks0Map <OracleReturn-KeyLogGks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (and
        (assert-invariant-2a-vii old-state-KeyLogGks0 old-state-KeyLogGks0Map)
    )
)
(define-fun <relation-assert-invariant-2a-vii-game_KeyLogGks0-game_KeyLogGks0Map-SET> 
    (
        (old-state-KeyLogGks0 <GameState_KeyLogGks0_<$$>>)
        (old-state-KeyLogGks0Map <GameState_KeyLogGks0Map_<$$>>)
        (return-SET-KeyLogGks0 <OracleReturn-KeyLogGks0-<$$>-Key-<$$>-SET>)
        (return-SET-KeyLogGks0Map <OracleReturn-KeyLogGks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (let 
        (
            (new-state-KeyLogGks0 (<oracle-return-KeyLogGks0-<$$>-Key-<$$>-SET-game-state> return-SET-KeyLogGks0))
            (new-state-KeyLogGks0Map (<oracle-return-KeyLogGks0Map-<$$>-Key-<$$>-SET-game-state> return-SET-KeyLogGks0Map))
        )
        (and
            (assert-invariant-2a-vii new-state-KeyLogGks0 new-state-KeyLogGks0Map)
        )
    )
)
(define-fun <relation-lemma-SAMPLE-output-length-game_KeyLogGks0-game_KeyLogGks0Map-SET> 
    (
        (old-state-KeyLogGks0 <GameState_KeyLogGks0_<$$>>)
        (old-state-KeyLogGks0Map <GameState_KeyLogGks0Map_<$$>>)
        (return-SET-KeyLogGks0 <OracleReturn-KeyLogGks0-<$$>-Key-<$$>-SET>)
        (return-SET-KeyLogGks0Map <OracleReturn-KeyLogGks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (let 
        (
            (new-state-KeyLogGks0 (<oracle-return-KeyLogGks0-<$$>-Key-<$$>-SET-game-state> return-SET-KeyLogGks0))
            (new-state-KeyLogGks0Map (<oracle-return-KeyLogGks0Map-<$$>-Key-<$$>-SET-game-state> return-SET-KeyLogGks0Map))
        )
        (let
            (
                (input_left (<pkg-state-Sample-<$$>-input> (<game-KeyLogGks0-<$$>-pkgstate-pkg_Sample> new-state-KeyLogGks0)))
                (input_right (<pkg-state-Sample-<$$>-input> (<game-KeyLogGks0-<$$>-pkgstate-pkg_Sample> new-state-KeyLogGks0)))
                (output_left (<pkg-state-Sample-<$$>-output> (<game-KeyLogGks0Map-<$$>-pkgstate-pkg_Sample> new-state-KeyLogGks0Map)))
                (output_right (<pkg-state-Sample-<$$>-output> (<game-KeyLogGks0Map-<$$>-pkgstate-pkg_Sample> new-state-KeyLogGks0Map)))
                
                (k256_left (<pkg-state-Sample-<$$>-k256> (<game-KeyLogGks0-<$$>-pkgstate-pkg_Sample> new-state-KeyLogGks0)))
                (k384_left (<pkg-state-Sample-<$$>-k384> (<game-KeyLogGks0-<$$>-pkgstate-pkg_Sample> new-state-KeyLogGks0)))
                (k512_left (<pkg-state-Sample-<$$>-k512> (<game-KeyLogGks0-<$$>-pkgstate-pkg_Sample> new-state-KeyLogGks0)))
                (k256_right (<pkg-state-Sample-<$$>-k256> (<game-KeyLogGks0Map-<$$>-pkgstate-pkg_Sample> new-state-KeyLogGks0Map)))
                (k384_right (<pkg-state-Sample-<$$>-k384> (<game-KeyLogGks0Map-<$$>-pkgstate-pkg_Sample> new-state-KeyLogGks0Map)))
                (k512_right (<pkg-state-Sample-<$$>-k512> (<game-KeyLogGks0Map-<$$>-pkgstate-pkg_Sample> new-state-KeyLogGks0Map)))
            )
            (and
                (= (<<func-len_key>> output_left) input_left)
                (= (<<func-len_key>> output_right) input_right)
                (= (<<func-len_key>> (<<func-cast256>> k256_left)) 256)
                (= (<<func-len_key>> (<<func-cast384>> k384_left)) 384)
                (= (<<func-len_key>> (<<func-cast512>> k512_left)) 512)
                (= (<<func-len_key>> (<<func-cast256>> k256_right)) 256)
                (= (<<func-len_key>> (<<func-cast384>> k384_right)) 384)
                (= (<<func-len_key>> (<<func-cast512>> k512_right)) 512)
            )
        )
    )
)
(define-fun <relation-assume-invariant-2a-viii-game_KeyLogGks0-game_KeyLogGks0Map-SET> 
    (
        (old-state-KeyLogGks0 <GameState_KeyLogGks0_<$$>>)
        (old-state-KeyLogGks0Map <GameState_KeyLogGks0Map_<$$>>)
        (return-SET-KeyLogGks0 <OracleReturn-KeyLogGks0-<$$>-Key-<$$>-SET>)
        (return-SET-KeyLogGks0Map <OracleReturn-KeyLogGks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (and
        (assert-invariant-2a-viii old-state-KeyLogGks0 old-state-KeyLogGks0Map)
        ;(assert-invariant-2a-iii old-state-KeyLogGks0 old-state-KeyLogGks0Map)
    )
)
(define-fun <relation-assert-invariant-2a-viii-game_KeyLogGks0-game_KeyLogGks0Map-SET> 
    (
        (old-state-KeyLogGks0 <GameState_KeyLogGks0_<$$>>)
        (old-state-KeyLogGks0Map <GameState_KeyLogGks0Map_<$$>>)
        (return-SET-KeyLogGks0 <OracleReturn-KeyLogGks0-<$$>-Key-<$$>-SET>)
        (return-SET-KeyLogGks0Map <OracleReturn-KeyLogGks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (let 
        (
            (new-state-KeyLogGks0 (<oracle-return-KeyLogGks0-<$$>-Key-<$$>-SET-game-state> return-SET-KeyLogGks0))
            (new-state-KeyLogGks0Map (<oracle-return-KeyLogGks0Map-<$$>-Key-<$$>-SET-game-state> return-SET-KeyLogGks0Map))
        )
        (let 
            (
                (Log_left (<pkg-state-Log-<$$>-Log> (<game-KeyLogGks0-<$$>-pkgstate-pkg_Log> new-state-KeyLogGks0)))
                (checkpoint_left (<pkg-state-Key-<$$>-checkpoint> (<game-KeyLogGks0-<$$>-pkgstate-pkg_Key> new-state-KeyLogGks0)))
                (len_handle_left (<pkg-state-Key-<$$>-len_handle> (<game-KeyLogGks0-<$$>-pkgstate-pkg_Key> new-state-KeyLogGks0)))
                (input_left (<pkg-state-Sample-<$$>-input> (<game-KeyLogGks0-<$$>-pkgstate-pkg_Sample> new-state-KeyLogGks0)))
                (input_right (<pkg-state-Sample-<$$>-input> (<game-KeyLogGks0-<$$>-pkgstate-pkg_Sample> new-state-KeyLogGks0)))
                (raw_key_left (<pkg-state-Key-<$$>-raw_key> (<game-KeyLogGks0-<$$>-pkgstate-pkg_Key> new-state-KeyLogGks0)))
                (Log_right (<pkg-state-Log-<$$>-Log> (<game-KeyLogGks0Map-<$$>-pkgstate-pkg_Log> new-state-KeyLogGks0Map)))
                (Log_right_old (<pkg-state-Log-<$$>-Log> (<game-KeyLogGks0Map-<$$>-pkgstate-pkg_Log> old-state-KeyLogGks0Map)))
                (len_handle_right (<pkg-state-Key-<$$>-len_handle> (<game-KeyLogGks0Map-<$$>-pkgstate-pkg_Key> new-state-KeyLogGks0Map)))
                (checkpoint_right (<pkg-state-Key-<$$>-checkpoint> (<game-KeyLogGks0Map-<$$>-pkgstate-pkg_Key> new-state-KeyLogGks0Map)))
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
                                        (= n (<<func-name>> mapped_h))
                                        (invariant-2a-viii (<<func-name>> mapped_h) mapped_h Log_right_old)
                                        (=>
                                            (= n (<<func-name>> mapped_h))
                                            (= (<<func-len_key>> ks) (<<func-len_alg>> (<<func-handle_alg>> mapped_h)))
                                        )
                                    )
                                )
                                (= (<<func-len_key>> ks) len_handle_right)
                                (= len_handle_right (<<func-len_alg>> (<<func-handle_alg>> h)))
                                (= (<<func-handle_alg>> h) (<<func-handle_alg>> mapped_h))
                                (= (<<func-len_key>> ks) (<<func-len_alg>> (<<func-handle_alg>> h)) (<<func-len_alg>> (<<func-handle_alg>> mapped_h)))
                            )
                        )
                    )
                )
                (invariant-2a-viii n h Log_left)
                (invariant-2a-viii n h Log_right)
                (assert-invariant-2a-viii new-state-KeyLogGks0 new-state-KeyLogGks0Map)
            )
        )
    )
)
(define-fun <relation-assume-invariant-log-preserves-name-game_KeyLogGks0-game_KeyLogGks0Map-SET> 
    (
        (old-state-KeyLogGks0 <GameState_KeyLogGks0_<$$>>)
        (old-state-KeyLogGks0Map <GameState_KeyLogGks0Map_<$$>>)
        (return-SET-KeyLogGks0 <OracleReturn-KeyLogGks0-<$$>-Key-<$$>-SET>)
        (return-SET-KeyLogGks0Map <OracleReturn-KeyLogGks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (invariant-log-preserves-name old-state-KeyLogGks0 old-state-KeyLogGks0Map)
)
(define-fun <relation-assert-invariant-log-preserves-name-game_KeyLogGks0-game_KeyLogGks0Map-SET> 
    (
        (old-state-KeyLogGks0 <GameState_KeyLogGks0_<$$>>)
        (old-state-KeyLogGks0Map <GameState_KeyLogGks0Map_<$$>>)
        (return-SET-KeyLogGks0 <OracleReturn-KeyLogGks0-<$$>-Key-<$$>-SET>)
        (return-SET-KeyLogGks0Map <OracleReturn-KeyLogGks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (let 
        (
            (new-state-KeyLogGks0 (<oracle-return-KeyLogGks0-<$$>-Key-<$$>-SET-game-state> return-SET-KeyLogGks0))
            (new-state-KeyLogGks0Map (<oracle-return-KeyLogGks0Map-<$$>-Key-<$$>-SET-game-state> return-SET-KeyLogGks0Map))
        )
        (invariant-log-preserves-name new-state-KeyLogGks0 new-state-KeyLogGks0Map)
    )
)
(define-fun <relation-lemma-injectivity-of-len_alg-game_KeyLogGks0-game_KeyLogGks0Map-SET>
    (
        (old-state-KeyLogGks0 <GameState_KeyLogGks0_<$$>>)
        (old-state-KeyLogGks0Map <GameState_KeyLogGks0Map_<$$>>)
        (return-SET-KeyLogGks0 <OracleReturn-KeyLogGks0-<$$>-Key-<$$>-SET>)
        (return-SET-KeyLogGks0Map <OracleReturn-KeyLogGks0Map-<$$>-Key-<$$>-SET>)
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
            (= (<<func-len_alg>> alg1) (<<func-len_alg>> alg2))
            (= alg1 alg2)
        )
    )
)
(define-fun <relation-assume-invariant-log-inverse-name-game_KeyLogGks0-game_KeyLogGks0Map-SET> 
    (
        (old-state-KeyLogGks0 <GameState_KeyLogGks0_<$$>>)
        (old-state-KeyLogGks0Map <GameState_KeyLogGks0Map_<$$>>)
        (return-SET-KeyLogGks0 <OracleReturn-KeyLogGks0-<$$>-Key-<$$>-SET>)
        (return-SET-KeyLogGks0Map <OracleReturn-KeyLogGks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (invariant-log-inverse-name old-state-KeyLogGks0 old-state-KeyLogGks0Map)
)
(define-fun <relation-assert-invariant-log-inverse-name-game_KeyLogGks0-game_KeyLogGks0Map-SET> 
    (
        (old-state-KeyLogGks0 <GameState_KeyLogGks0_<$$>>)
        (old-state-KeyLogGks0Map <GameState_KeyLogGks0Map_<$$>>)
        (return-SET-KeyLogGks0 <OracleReturn-KeyLogGks0-<$$>-Key-<$$>-SET>)
        (return-SET-KeyLogGks0Map <OracleReturn-KeyLogGks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (let 
        (
            (new-state-KeyLogGks0 (<oracle-return-KeyLogGks0-<$$>-Key-<$$>-SET-game-state> return-SET-KeyLogGks0))
            (new-state-KeyLogGks0Map (<oracle-return-KeyLogGks0Map-<$$>-Key-<$$>-SET-game-state> return-SET-KeyLogGks0Map))
        )
        (invariant-log-inverse-name new-state-KeyLogGks0 new-state-KeyLogGks0Map)
    )
)
(define-fun <relation-assume-invariant-2e-game_KeyLogGks0-game_KeyLogGks0Map-SET> 
    (
        (old-state-KeyLogGks0 <GameState_KeyLogGks0_<$$>>)
        (old-state-KeyLogGks0Map <GameState_KeyLogGks0Map_<$$>>)
        (return-SET-KeyLogGks0 <OracleReturn-KeyLogGks0-<$$>-Key-<$$>-SET>)
        (return-SET-KeyLogGks0Map <OracleReturn-KeyLogGks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (invariant-2e old-state-KeyLogGks0 old-state-KeyLogGks0Map)
)
(define-fun <relation-assert-invariant-2e-game_KeyLogGks0-game_KeyLogGks0Map-SET> 
    (
        (old-state-KeyLogGks0 <GameState_KeyLogGks0_<$$>>)
        (old-state-KeyLogGks0Map <GameState_KeyLogGks0Map_<$$>>)
        (return-SET-KeyLogGks0 <OracleReturn-KeyLogGks0-<$$>-Key-<$$>-SET>)
        (return-SET-KeyLogGks0Map <OracleReturn-KeyLogGks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (let 
        (
            (new-state-KeyLogGks0 (<oracle-return-KeyLogGks0-<$$>-Key-<$$>-SET-game-state> return-SET-KeyLogGks0))
            (new-state-KeyLogGks0Map (<oracle-return-KeyLogGks0Map-<$$>-Key-<$$>-SET-game-state> return-SET-KeyLogGks0Map))
        )
        (invariant-2e new-state-KeyLogGks0 new-state-KeyLogGks0Map)
    )
)
(define-fun <relation-assume-invariant-2a-ix-and-2a-x-game_KeyLogGks0-game_KeyLogGks0Map-SET> 
    (
        (old-state-KeyLogGks0 <GameState_KeyLogGks0_<$$>>)
        (old-state-KeyLogGks0Map <GameState_KeyLogGks0Map_<$$>>)
        (return-SET-KeyLogGks0 <OracleReturn-KeyLogGks0-<$$>-Key-<$$>-SET>)
        (return-SET-KeyLogGks0Map <OracleReturn-KeyLogGks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (assert-invariant-2a-ix-and-2a-x old-state-KeyLogGks0 old-state-KeyLogGks0Map)
)
(define-fun <relation-assert-invariant-2a-ix-and-2a-x-game_KeyLogGks0-game_KeyLogGks0Map-SET> 
    (
        (old-state-KeyLogGks0 <GameState_KeyLogGks0_<$$>>)
        (old-state-KeyLogGks0Map <GameState_KeyLogGks0Map_<$$>>)
        (return-SET-KeyLogGks0 <OracleReturn-KeyLogGks0-<$$>-Key-<$$>-SET>)
        (return-SET-KeyLogGks0Map <OracleReturn-KeyLogGks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (let 
        (
            (new-state-KeyLogGks0 (<oracle-return-KeyLogGks0-<$$>-Key-<$$>-SET-game-state> return-SET-KeyLogGks0))
            (new-state-KeyLogGks0Map (<oracle-return-KeyLogGks0Map-<$$>-Key-<$$>-SET-game-state> return-SET-KeyLogGks0Map))
        )
        (assert-invariant-2a-ix-and-2a-x new-state-KeyLogGks0 new-state-KeyLogGks0Map)
    )
)
(define-fun <relation-assume-invariant-consistent-log-inverse-level-zero-psk-game_KeyLogGks0-game_KeyLogGks0Map-SET> 
    (
        (old-state-KeyLogGks0 <GameState_KeyLogGks0_<$$>>)
        (old-state-KeyLogGks0Map <GameState_KeyLogGks0Map_<$$>>)
        (return-SET-KeyLogGks0 <OracleReturn-KeyLogGks0-<$$>-Key-<$$>-SET>)
        (return-SET-KeyLogGks0Map <OracleReturn-KeyLogGks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (invariant-consistent-log-inverse-level-zero-psk old-state-KeyLogGks0 old-state-KeyLogGks0Map)
)
(define-fun <relation-assert-invariant-consistent-log-inverse-level-zero-psk-game_KeyLogGks0-game_KeyLogGks0Map-SET> 
    (
        (old-state-KeyLogGks0 <GameState_KeyLogGks0_<$$>>)
        (old-state-KeyLogGks0Map <GameState_KeyLogGks0Map_<$$>>)
        (return-SET-KeyLogGks0 <OracleReturn-KeyLogGks0-<$$>-Key-<$$>-SET>)
        (return-SET-KeyLogGks0Map <OracleReturn-KeyLogGks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (let 
        (
            (new-state-KeyLogGks0 (<oracle-return-KeyLogGks0-<$$>-Key-<$$>-SET-game-state> return-SET-KeyLogGks0))
            (new-state-KeyLogGks0Map (<oracle-return-KeyLogGks0Map-<$$>-Key-<$$>-SET-game-state> return-SET-KeyLogGks0Map))
        )
        (invariant-consistent-log-inverse-level-zero-psk new-state-KeyLogGks0 new-state-KeyLogGks0Map)
    )
)
(define-fun <relation-assume-invariant-consistent-log-for-dh-and-psk-game_KeyLogGks0-game_KeyLogGks0Map-SET> 
    (
        (old-state-KeyLogGks0 <GameState_KeyLogGks0_<$$>>)
        (old-state-KeyLogGks0Map <GameState_KeyLogGks0Map_<$$>>)
        (return-SET-KeyLogGks0 <OracleReturn-KeyLogGks0-<$$>-Key-<$$>-SET>)
        (return-SET-KeyLogGks0Map <OracleReturn-KeyLogGks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (invariant-consistent-log-for-dh-and-psk old-state-KeyLogGks0 old-state-KeyLogGks0Map)
)
(define-fun <relation-assert-invariant-consistent-log-for-dh-and-psk-game_KeyLogGks0-game_KeyLogGks0Map-SET> 
    (
        (old-state-KeyLogGks0 <GameState_KeyLogGks0_<$$>>)
        (old-state-KeyLogGks0Map <GameState_KeyLogGks0Map_<$$>>)
        (return-SET-KeyLogGks0 <OracleReturn-KeyLogGks0-<$$>-Key-<$$>-SET>)
        (return-SET-KeyLogGks0Map <OracleReturn-KeyLogGks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (let 
        (
            (new-state-KeyLogGks0 (<oracle-return-KeyLogGks0-<$$>-Key-<$$>-SET-game-state> return-SET-KeyLogGks0))
            (new-state-KeyLogGks0Map (<oracle-return-KeyLogGks0Map-<$$>-Key-<$$>-SET-game-state> return-SET-KeyLogGks0Map))
        )
        (invariant-consistent-log-for-dh-and-psk new-state-KeyLogGks0 new-state-KeyLogGks0Map)
    )
)

(define-fun <relation-assume-invariant-2a-v-game_KeyLogGks0-game_KeyLogGks0Map-SET> 
    (
        (old-state-KeyLogGks0 <GameState_KeyLogGks0_<$$>>)
        (old-state-KeyLogGks0Map <GameState_KeyLogGks0Map_<$$>>)
        (return-SET-KeyLogGks0 <OracleReturn-KeyLogGks0-<$$>-Key-<$$>-SET>)
        (return-SET-KeyLogGks0Map <OracleReturn-KeyLogGks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (invariant-2a-v old-state-KeyLogGks0 old-state-KeyLogGks0Map)
)
(define-fun <relation-lemma-rand-is-eq-game_KeyLogGks0-game_KeyLogGks0Map-SET> 
    (
        (old-state-KeyLogGks0 <GameState_KeyLogGks0_<$$>>)
        (old-state-KeyLogGks0Map <GameState_KeyLogGks0Map_<$$>>)
        (return-SET-KeyLogGks0 <OracleReturn-KeyLogGks0-<$$>-Key-<$$>-SET>)
        (return-SET-KeyLogGks0Map <OracleReturn-KeyLogGks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (and
        (rand-is-eq 0 0 (<game-KeyLogGks0-<$$>-rand-0> old-state-KeyLogGks0) (<game-KeyLogGks0Map-<$$>-rand-0> old-state-KeyLogGks0Map))
        (rand-is-eq 1 1 (<game-KeyLogGks0-<$$>-rand-1> old-state-KeyLogGks0) (<game-KeyLogGks0Map-<$$>-rand-1> old-state-KeyLogGks0Map))
        (rand-is-eq 2 2 (<game-KeyLogGks0-<$$>-rand-2> old-state-KeyLogGks0) (<game-KeyLogGks0Map-<$$>-rand-2> old-state-KeyLogGks0Map))
    )
)
(define-fun <relation-lemma-randomness-mapping-game_KeyLogGks0-game_KeyLogGks0Map-SET> 
    (
        (old-state-KeyLogGks0 <GameState_KeyLogGks0_<$$>>)
        (old-state-KeyLogGks0Map <GameState_KeyLogGks0Map_<$$>>)
        (return-SET-KeyLogGks0 <OracleReturn-KeyLogGks0-<$$>-Key-<$$>-SET>)
        (return-SET-KeyLogGks0Map <OracleReturn-KeyLogGks0Map-<$$>-Key-<$$>-SET>)
        (n Int)
        (l Int)
        (h Bits_*)
        (hon Bool)
        (k Bits_*)
    )
    Bool
    (and
        (randomness-mapping-SET (<game-KeyLogGks0-<$$>-rand-0> old-state-KeyLogGks0) (<game-KeyLogGks0Map-<$$>-rand-0> old-state-KeyLogGks0Map) 0 0 (<game-KeyLogGks0-<$$>-rand-0> old-state-KeyLogGks0) (<game-KeyLogGks0Map-<$$>-rand-0> old-state-KeyLogGks0Map))
        (randomness-mapping-SET (<game-KeyLogGks0-<$$>-rand-1> old-state-KeyLogGks0) (<game-KeyLogGks0Map-<$$>-rand-1> old-state-KeyLogGks0Map) 1 1 (<game-KeyLogGks0-<$$>-rand-1> old-state-KeyLogGks0) (<game-KeyLogGks0Map-<$$>-rand-1> old-state-KeyLogGks0Map))
        (randomness-mapping-SET (<game-KeyLogGks0-<$$>-rand-2> old-state-KeyLogGks0) (<game-KeyLogGks0Map-<$$>-rand-2> old-state-KeyLogGks0Map) 2 2 (<game-KeyLogGks0-<$$>-rand-2> old-state-KeyLogGks0) (<game-KeyLogGks0Map-<$$>-rand-2> old-state-KeyLogGks0Map))
    )
)