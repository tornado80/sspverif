; Main idea of this invariant proof
; If ctr are equal in both games and they use the same randomness, then both games 
;    - produce the same output
;    - abort iff the other aborts
;    - have same ctr afterwards

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Randomness mapping --- there is only 1 randomness counter
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun randomness-mapping-UsefulOracle
  ( (ctr-0 Int)
    (ctr-1 Int)
    (id-0  Int)
    (id-1  Int)
    (icr-0 Int)
    (icr-1 Int))
  Bool
  (and
    (= ctr-0 ctr-1)
    (= ctr-0 icr-1)
    (= ctr-0 icr-1)
    (= id-0      0)
    (= id-1      0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Invariant --- note that the invariant needs to be game-global 
;               Having different variants for Oracle & UselessOracle would allow to prove wrong things.
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun invariant
  ( (state-0  <GameState_SmallComposition_<$<!n!>$>>)
    (state-1  <GameState_MediumComposition_<$<!n!>$>>))
  Bool
  (let
    ; getting ctr out of state
    ( (ctr-0 (<state-Rand-<$<!n!>$>-ctr> (<game-SmallComposition-<$<!n!>$>-pkgstate-rand> state-0)))
      (ctr-1 (<state-Rand-<$<!n!>$>-ctr> (<game-MediumComposition-<$<!n!>$>-pkgstate-rand> state-1))))

    ; ctr are equal
    (= ctr-0 ctr-1)))

;;;; Chris: This function should not exist?
;
;(define-fun invariant-Oracle
;  ( (state-0  <GameState_SmallComposition_<$<!n!>$>>)
;    (state-1  <GameState_MediumComposition_<$<!n!>$>>))
;  Bool
;  (invariant state-0 state-1))
