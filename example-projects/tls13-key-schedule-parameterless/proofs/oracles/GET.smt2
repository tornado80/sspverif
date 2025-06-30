(define-fun randomness-mapping-GET
    ( 
        (sample-ctr-old-Gks0 Int)
        (sample-ctr-old-Gks0Map Int)
        (sample-id-Gks0 Int)
        (sample-id-Gks0Map Int)
        (sample-ctr-Gks0 Int)
        (sample-ctr-Gks0Map Int)
    )
    Bool
    (randomness-mapping 
        sample-ctr-old-Gks0 
        sample-ctr-old-Gks0Map
        sample-id-Gks0
        sample-id-Gks0Map
        sample-ctr-Gks0
        sample-ctr-Gks0Map
    )
)

(define-fun <relation-all-invariants-before-game_Gks0-game_Gks0Map-GET> 
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-GET-Gks0 <OracleReturn-Gks0-<$$>-OutputKeyGetter-<$$>-GET>)
        (return-GET-Gks0Map <OracleReturn-Gks0Map-<$$>-Map-<$$>-GET>)
        (n Int)
        (l Int)
        (h Bits_*)
    )
    Bool
    (all-invariants old-state-Gks0 old-state-Gks0Map)
)

(define-fun <relation-all-invariants-after-game_Gks0-game_Gks0Map-GET> 
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-GET-Gks0 <OracleReturn-Gks0-<$$>-OutputKeyGetter-<$$>-GET>)
        (return-GET-Gks0Map <OracleReturn-Gks0Map-<$$>-Map-<$$>-GET>)
        (n Int)
        (l Int)
        (h Bits_*)
    )
    Bool
    (all-invariants <<game-state-game_Gks0-new-GET>> <<game-state-game_Gks0Map-new-GET>>)
)

(define-fun <relation-lemma-alg-is-preserved-game_Gks0-game_Gks0Map-GET> 
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-GET-Gks0 <OracleReturn-Gks0-<$$>-OutputKeyGetter-<$$>-GET>)
        (return-GET-Gks0Map <OracleReturn-Gks0Map-<$$>-Map-<$$>-GET>)
        (n Int)
        (l Int)
        (h Bits_*)
    )
    Bool
    (let 
        (
            (M (<pkg-state-MapTable-<$$>-M> (<game-Gks0Map-<$$>-pkgstate-pkg_MapTable> old-state-Gks0Map)))
        )
        (let 
            (
                (m (maybe-get (select M (mk-tuple3 n (none-aware-level h) h))))
            )
            (= (<<func-handle_alg>> h) (<<func-handle_alg>> m))
        )
    )
)

(define-fun <relation-lemma-left-output-game_Gks0-game_Gks0Map-GET> 
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-GET-Gks0 <OracleReturn-Gks0-<$$>-OutputKeyGetter-<$$>-GET>)
        (return-GET-Gks0Map <OracleReturn-Gks0Map-<$$>-Map-<$$>-GET>)
        (n Int)
        (l Int)
        (h Bits_*)
    )
    Bool
    (let 
        (
            (left-output (return-value (<oracle-return-Gks0-<$$>-OutputKeyGetter-<$$>-GET-return-value-or-abort> return-GET-Gks0)))
            (K (<pkg-state-Key-<$$>-K> (<game-Gks0-<$$>-pkgstate-pkg_Key> old-state-Gks0)))
        )
        (and 
            (= (el2-2 left-output) (el2-2 (maybe-get (select K (mk-tuple3 n l h)))))
            (= (el2-1 left-output) (<<func-tag>> (<<func-handle_alg>> h) (el2-1 (maybe-get (select K (mk-tuple3 n l h))))))
            (= (el2-2 left-output) (el2-2 (maybe-get (select K (mk-tuple3 n (none-aware-level h) h))))) ; needs lemma-name-and-level-of-handle
            (= (el2-1 left-output) (<<func-tag>> (<<func-handle_alg>> h) (el2-1 (maybe-get (select K (mk-tuple3 n (none-aware-level h) h)))))) ; needs lemma-name-and-level-of-handle
        )
    )
)

(define-fun <relation-lemma-name-and-level-of-handle-game_Gks0-game_Gks0Map-GET> 
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-GET-Gks0 <OracleReturn-Gks0-<$$>-OutputKeyGetter-<$$>-GET>)
        (return-GET-Gks0Map <OracleReturn-Gks0Map-<$$>-Map-<$$>-GET>)
        (nn Int)
        (ll Int)
        (hh Bits_*)
    )
    Bool
    ; when a mapping entry is not none then the index (name, level) matches the handle
    ; we have just assumed it to make sure the proof goes through with it
    (let 
        (
            (M (<pkg-state-MapTable-<$$>-M> (<game-Gks0Map-<$$>-pkgstate-pkg_MapTable> old-state-Gks0Map)))
        )
        (forall 
            (
                (n Int)
                (l Int)
                (h Bits_*)
            )
            (=>
                (not ((_ is mk-none) (select M (mk-tuple3 n l h))))
                (and 
                    (= n (<<func-name>> h))
                    (= l (none-aware-level h))
                )
            )
        )
    )

)

(define-fun <relation-lemma-invariant-6-game_Gks0-game_Gks0Map-GET> 
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-GET-Gks0 <OracleReturn-Gks0-<$$>-OutputKeyGetter-<$$>-GET>)
        (return-GET-Gks0Map <OracleReturn-Gks0Map-<$$>-Map-<$$>-GET>)
        (nn Int)
        (ll Int)
        (h Bits_*)
    )
    Bool
    (let 
        (
            (M_right (<pkg-state-MapTable-<$$>-M> (<game-Gks0Map-<$$>-pkgstate-pkg_MapTable> old-state-Gks0Map)))
            (K_left (<pkg-state-Key-<$$>-K> (<game-Gks0-<$$>-pkgstate-pkg_Key> old-state-Gks0)))
            (K_right (<pkg-state-Key-<$$>-K> (<game-Gks0Map-<$$>-pkgstate-pkg_Key> old-state-Gks0Map)))
        )

            (let 
                (
                    (n (<<func-name>> h))
                )
                (let
                    (
                        (l (none-aware-level h))
                    )
                    (let 
                        (
                            (m (maybe-get (select M_right (mk-tuple3 n l h))))
                        )
                        (=
                            (select K_left (mk-tuple3 n l h))
                            (select K_right (mk-tuple3 n (none-aware-level m) m))
                        )
                    )
                )
            )
    )
)

(define-fun <relation-lemma-right-output-game_Gks0-game_Gks0Map-GET> 
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
        (return-GET-Gks0 <OracleReturn-Gks0-<$$>-OutputKeyGetter-<$$>-GET>)
        (return-GET-Gks0Map <OracleReturn-Gks0Map-<$$>-Map-<$$>-GET>)
        (n Int)
        (l Int)
        (h Bits_*)
    )
    Bool
    (let 
        (
            (right-output (return-value (<oracle-return-Gks0Map-<$$>-Map-<$$>-GET-return-value-or-abort> return-GET-Gks0Map)))
            (K (<pkg-state-Key-<$$>-K> (<game-Gks0Map-<$$>-pkgstate-pkg_Key> old-state-Gks0Map)))
            (M (<pkg-state-MapTable-<$$>-M> (<game-Gks0Map-<$$>-pkgstate-pkg_MapTable> old-state-Gks0Map)))
        )
        (let 
            (
                (m (maybe-get (select M (mk-tuple3 n (none-aware-level h) h)))) ; needs lemma-name-and-level-of-handle
            )
            (and 
                (= 
                    (el2-2 right-output) 
                    (el2-2 (maybe-get (select K (mk-tuple3 n (maybe-get (<<func-level>> m)) m))))
                )
                (= 
                    (el2-1 right-output) 
                    (<<func-tag>> (<<func-handle_alg>> m) (el2-1 (maybe-get (select K (mk-tuple3 n (maybe-get (<<func-level>> m)) m)))))
                )
                (= 
                    (el2-2 right-output) 
                    (el2-2 (maybe-get (select K (mk-tuple3 n (none-aware-level m) m))))
                )
                (= 
                    (el2-1 right-output) 
                    (<<func-tag>> (<<func-handle_alg>> m) (el2-1 (maybe-get (select K (mk-tuple3 n (none-aware-level m) m)))))
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
    (invariant-6 state-Gks0 state-Gks0Map)

    
    
    ;true
    ;(all-invariants state-Gks0 state-Gks0Map)
)