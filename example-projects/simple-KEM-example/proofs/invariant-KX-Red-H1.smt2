invariant(define-fun invariant
  ( (state-prot     <GameState_todo>>)
    (state-red      <GameState_todo>>))
  Bool
; getting package-state out of game-state and demanding equality, they should be exactly the same in this case.
(=
(<game-KX-<$<!n!><!b!><!zeron!>$>-pkgstate-Game>     state-kx)         ;some params are still missing.
(<game-H1-<$<!n!><!b!><!false!><!zeron!>$>-pkgstate-Game> state-kxred) ;some params are still missing.
)

;  (let
;    ; getting ctr out of state
;    ( (ctr-kxred (<pkg-state-Rand-<$<!n!>$>-ctr> (<game-SmallComposition-<$<!n!>$>-pkgstate-rand> state-0)))
;      (ctr-kx (<pkg-state-Rand-<$<!n!>$>-ctr> (<game-MediumComposition-<$<!n!>$>-pkgstate-rand> state-1))))
;
;    ; ctr are equal
;    (= ctr-kxred ctr-kx))

)
