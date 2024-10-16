; Main idea of this invariant proof
; If ltk (or K) are equal (or use the same randomness), then both games 
;    - produce the same output
;    - abort iff the other aborts
;    - have same ltk and same table K afterwards

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Randomness mapping --- there is only randomness for ltk
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun
    randomness-mapping-PRF
    (
        (ctr-left      Int)
        (ctr-right     Int) 
        (id-left       Int)
        (id-right      Int) 
        (new-left      Int)
        (new-right     Int)
    )
    Bool
(and
(= ctr-left  new-left )
(= ctr-right new-right)
(= id-left  1)
(= id-right 1)
))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Invariant --- note that the invariant needs to be game-global 
;               Having different variants for EVAL & GET allows to prove wrong things.
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun invariant-PRF      (
        (state-mod  <GameState_Modprfreal_<$<!n!>$>> )
        (state-mon  <GameState_Monprfreal_<$<!n!>$>>)
)
    Bool
    (let

; getting ltk and table K out of state
(
(ltk-mod (<state-modPRF-<$<!n!>$>-ltk>     (<game-Modprfreal-<$<!n!>$>-pkgstate-mod_prf> state-mod)))
(  K-mod (<state-KeyReal-<$<!n!>$>-K>      (<game-Modprfreal-<$<!n!>$>-pkgstate-key> state-mod)))
(ltk-mon (<state-PRFReal-<$<!n!>$>-ltk>    (<game-Monprfreal-<$<!n!>$>-pkgstate-prf> state-mon)))
(  K-mon (<state-ReductionPRF-<$<!n!>$>-K> (<game-Monprfreal-<$<!n!>$>-pkgstate-red> state-mon)))
)

(and
; ltk are equal
; T   are equal
(= ltk-mod ltk-mon)
(= K-mod   K-mon)
)

))
