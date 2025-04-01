(define-fun randomness-mapping-DHGEN
  ( 
    (sample-ctr-old-Gks0 Int)
    (sample-ctr-old-Gks0Map Int)
    (sample-id-Gks0 Int)
    (sample-id-Gks0Map Int)
    (sample-ctr-Gks0 Int)
    (sample-ctr-Gks0Map Int)
  ) 
  Bool
  (and
    (= sample-ctr-Gks0 sample-ctr-old-Gks0)
    (= sample-ctr-Gks0Map sample-ctr-old-Gks0Map)
    (= sample-id-Gks0 3)
    (= sample-id-Gks0Map 3)
  )
)

(define-fun invariant
  (
    (old-state-Gks0 <GameState_Gks0_<$$>>)
    (old-state-Gks0Map <GameState_Gks0Map_<$$>>)
  )
  Bool
  (let
    (
      (E_left  (<pkg-state-DH-<$$>-E> (<game-Gks0-<$$>-pkgstate-pkg_DH> old-state-Gks0)))
      (E_right (<pkg-state-DH-<$$>-E> (<game-Gks0Map-<$$>-pkgstate-pkg_DH> old-state-Gks0Map)))
    ) 
    (= E_left E_right)
  )
)