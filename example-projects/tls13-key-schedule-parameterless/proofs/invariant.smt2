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