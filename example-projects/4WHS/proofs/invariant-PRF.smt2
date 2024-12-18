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

(define-fun Send1
  ( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
    (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
    (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
    (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
  (and
    (= scr-1 base-ctr-1)
    (= scr-0 base-ctr-0)
    (= id-0      id-1)))

(define-fun Send2
  ( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
    (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
    (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
    (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
  (and
    (= scr-1 base-ctr-1)
    (= scr-0 base-ctr-0)
    (= id-0      id-1)))

(define-fun Send3
  ( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
    (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
    (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
    (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
  (and
    (= scr-1 base-ctr-1)
    (= scr-0 base-ctr-0)
    (= id-0      id-1)))

(define-fun Send4
  ( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
    (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
    (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
    (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
  (and
    (= scr-1 base-ctr-1)
    (= scr-0 base-ctr-0)
    (= id-0      id-1)))

(define-fun Send5
  ( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
    (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
    (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
    (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
  (and
    (= scr-1 base-ctr-1)
    (= scr-0 base-ctr-0)
    (= id-0      id-1)))

(define-fun Reveal
  ( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
    (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
    (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
    (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
  (and
    (= scr-1 base-ctr-1)
    (= scr-0 base-ctr-0)
    (= id-0      id-1)))

(define-fun Test
  ( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
    (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
    (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
    (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
  (and
    (= scr-1 base-ctr-1)
    (= scr-0 base-ctr-0)
    (= id-0      id-1)))

(define-fun NewKey
  ( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
    (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
    (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
    (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
  (and
    (= scr-1 base-ctr-1)
    (= scr-0 base-ctr-0)
    (= id-0      id-1)))

(define-fun NewSession
  ( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
    (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
    (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
    (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
  (and
    (= scr-1 base-ctr-1)
    (= scr-0 base-ctr-0)
    (= id-0      id-1)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Invariant --- note that the invariant needs to be game-global 
;               Having different variants for Oracle & UselessOracle would allow to prove wrong things.
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun invariant
  ( (state-kx  <GameState_KX_<$<!n!>$>>)
    (state-kxred  <GameState_KX_Red_<$<!n!>$>>))
  Bool
;  (let
;    ; getting ctr out of state
;    ( (ctr-kxred (<pkg-state-Rand-<$<!n!>$>-ctr> (<game-SmallComposition-<$<!n!>$>-pkgstate-rand> state-0)))
;      (ctr-kx (<pkg-state-Rand-<$<!n!>$>-ctr> (<game-MediumComposition-<$<!n!>$>-pkgstate-rand> state-1))))
;
;    ; ctr are equal
;    (= ctr-kxred ctr-kx))
(state-kx state-kxred)   

)
