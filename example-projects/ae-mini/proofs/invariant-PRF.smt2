; Main idea of this invariant proof
; If ltk (or K) are equal (or use the same randomness), then both games 
;    - produce the same output
;    - abort iff the other aborts
;    - have same ltk and same K afterwards

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Randomness mapping --- there is only randomness for ltk
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun
    randomness-mapping-Eval
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

(define-fun invariant-EVAL      (
        (state-mod  CompositionState-modprfreal )
        (state-mon  CompositionState-monprfreal)
)
    Bool
    (let

; getting ltk and table K out
(
(ltk-mod (state-modprfreal-modprf-ltk     (composition-pkgstate-modprfreal-modprf state-mod)))
(  K-mod (state-modprfreal-key-K          (composition-pkgstate-modprfreal-modprf state-mod)))
(ltk-mon (state-monprfreal-monprfreal-ltk (composition-pkgstate-modprfreal-modprf state-mon)))
(  K-mon (state-monprfreal-red-K          (composition-pkgstate-modprfreal-modprf state-mon)))


(and
; ltk are equal
; T   are equal
(= ltk-mod ltk-mon)
(= K-mod   K-mon)
)

)))
