(define-fun invariant
    (
        (old-state-Gks0 <GameState_Gks0_<$$>>)
        (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
    )
    Bool
    (and 
        ; Invariant (1) : E_left = E_right
        (let
            (
                (E_left  (<pkg-state-DH-<$$>-E> (<game-Gks0-<$$>-pkgstate-pkg_DH> old-state-Gks0)))
                (E_right (<pkg-state-DH-<$$>-E> (<game-Gks0Map-<$$>-pkgstate-pkg_DH> old-state-Gks0Map)))
            )
            (= E_left E_right)
        )
        ; Invariant (2v) : Log_gks0[(n, h)] = some(h, hon, k) or none
        (let
            (
                (Log (<pkg-state-Log-<$$>-Log> (<game-Gks0-<$$>-pkgstate-pkg_Log> old-state-Gks0)))
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
    )
)