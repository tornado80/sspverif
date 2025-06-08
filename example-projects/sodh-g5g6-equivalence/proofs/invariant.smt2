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

(define-fun randomness-mapping-TH
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
    (= id-0      1)
    (= id-1      1)))

(define-fun randomness-mapping-TXTR
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
    (= id-0      0)
    (= id-1      0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Invariant --- note that the invariant needs to be game-global 
;               Having different variants for Oracle & UselessOracle would allow to prove wrong things.
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun invariant-TH-implies-T
    (
        (E (Array Bits_* (Maybe Int)))
        (T (Array (Tuple2 Bits_* Bits_*) (Maybe Bits_*)))
        (TH (Array (Tuple2 Bits_* Bits_*) (Maybe Bits_*)))
        (TXTR (Array (Tuple3 Bits_* Bits_* Bits_*) (Maybe Bits_*)))
    )
    Bool
    ; TH[Z, s] = h != None => T[Z, s] = h
    (forall 
        (
            (Z Bits_*)
            (s Bits_*)
        )
        (let 
            (
                (h (select TH (mk-tuple2 Z s)))
            )
            (=>
                (not ((_ is mk-none) h))
                (= h (select T (mk-tuple2 Z s)))
            )
        )
    )
)

(define-fun invariant-T-NotNone-implies-TH-and-TXTR
    (
        (E (Array Bits_* (Maybe Int)))
        (T (Array (Tuple2 Bits_* Bits_*) (Maybe Bits_*)))
        (TH (Array (Tuple2 Bits_* Bits_*) (Maybe Bits_*)))
        (TXTR (Array (Tuple3 Bits_* Bits_* Bits_*) (Maybe Bits_*)))
    )
    Bool
    ; T[Z, s] = h != None => TH[Z, s] = h or 
    ; there exists X, Y such that Y^E[X] = Z and TXTR[X, Y, s] = h
    (forall 
        (
            (Z Bits_*)
            (s Bits_*)
        )
        (let 
            (
                (h (select T (mk-tuple2 Z s)))
            )
            (=>
                (not ((_ is mk-none) h))
                (or
                    (= h (select TH (mk-tuple2 Z s)))
                    (let 
                        (
                            (XY (<<func-find_collision_in_TXTR>> TXTR Z s))
                        )
                        (and 
                            (not ((_ is mk-none) XY))
                            (let 
                                (
                                    (X (el2-1 (maybe-get XY)))
                                    (Y (el2-2 (maybe-get XY)))
                                )
                                (and 
                                    (= h (select TXTR (mk-tuple3 X Y s)))
                                    (= Z (<<func-exp>> Y (maybe-get (select E X))))
                                )
                            )
                        )
                    )
                )
            )
        )
    )
)

(define-fun invariant-T-None-implies-TH-and-TXTR
    (
        (E (Array Bits_* (Maybe Int)))
        (T (Array (Tuple2 Bits_* Bits_*) (Maybe Bits_*)))
        (TH (Array (Tuple2 Bits_* Bits_*) (Maybe Bits_*)))
        (TXTR (Array (Tuple3 Bits_* Bits_* Bits_*) (Maybe Bits_*)))
    )
    Bool
    ; T[Z, s] = None if and only if
    ; TH[Z, s] = None and
    ; forall X, Y such that Y^E[X] = Z and TXTR[X, Y, s] = None
    (forall 
        (
            (Z Bits_*)
            (s Bits_*)
        )
        (let 
            (
                (h (select T (mk-tuple2 Z s)))
            )
            (=
                ((_ is mk-none) h)
                (and
                    ((_ is mk-none) (select TH (mk-tuple2 Z s)))
                    ((_ is mk-none) (<<func-find_collision_in_TXTR>> TXTR Z s))
                )
            )
        )
    )
)

(define-fun invariant-TXTR-implies-T
    (
        (E (Array Bits_* (Maybe Int)))
        (T (Array (Tuple2 Bits_* Bits_*) (Maybe Bits_*)))
        (TH (Array (Tuple2 Bits_* Bits_*) (Maybe Bits_*)))
        (TXTR (Array (Tuple3 Bits_* Bits_* Bits_*) (Maybe Bits_*)))
    )
    Bool
    ; TXTR[X, Y, s] = h != None => T[Y^E[X], s] = h
    (forall 
        (
            (X Bits_*)
            (Y Bits_*)
            (s Bits_*)
        )
        (let 
            (
                (h (select TXTR (mk-tuple3 X Y s)))
            )
            (=>
                (not ((_ is mk-none) h))
                (= h (select T (mk-tuple2 (<<func-exp>> Y (maybe-get (select E X))) s)))
            )
        )
    )
)

(define-fun invariant
    (
        (state-g5  <GameState_G5_<$$>>)
        (state-g6  <GameState_G6_<$$>>)
    )
    Bool
    (let 
        (
            (E_left (<pkg-state-g5P-<$$>-E> (<game-G5-<$$>-pkgstate-g5> state-g5)))
            (E_right (<pkg-state-g6P-<$$>-E> (<game-G6-<$$>-pkgstate-g6> state-g6)))
            (T (<pkg-state-g5P-<$$>-T> (<game-G5-<$$>-pkgstate-g5> state-g5)))
            (TH (<pkg-state-g6P-<$$>-TH> (<game-G6-<$$>-pkgstate-g6> state-g6)))
            (TXTR (<pkg-state-g6P-<$$>-TXTR> (<game-G6-<$$>-pkgstate-g6> state-g6)))
        )
        (and 
            (= E_left E_right)
            ; TH[Z, s] = h != None => T[Z, s] = h
            (invariant-TH-implies-T E_left T TH TXTR)
            ; T[Z, s] = h != None => TH[Z, s] = h or 
            ; there exists X, Y such that Y^E[X] = Z and TXTR[X, Y, s] = h
            (invariant-T-NotNone-implies-TH-and-TXTR E_left T TH TXTR)
            ; T[Z, s] = None if and only if
            ; TH[Z, s] = None and
            ; forall X, Y such that Y^E[X] = Z and TXTR[X, Y, s] = None
            (invariant-T-None-implies-TH-and-TXTR E_left T TH TXTR)
            ; TXTR[X, Y, s] = h != None => T[Y^E[X], s] = h
            (invariant-TXTR-implies-T E_left T TH TXTR)
        )
    )
)

(define-fun <relation-lemma-find-collision-g5-g6-TXTR>
    (
        (old-state-g5  <GameState_G5_<$$>>)
        (old-state-g6  <GameState_G6_<$$>>)
        (return-g5 <OracleReturn-G5-<$$>-g5P-<$$>-TXTR>)
        (return-g6 <OracleReturn-G6-<$$>-g6P-<$$>-TXTR>)
        (X Bits_*)
        (Y Bits_*)
        (s Bits_*)
    )
    Bool
    (let
        (
            (state-g5 (<oracle-return-G5-<$$>-g5P-<$$>-TXTR-game-state> return-g5))
            (state-g6 (<oracle-return-G6-<$$>-g6P-<$$>-TXTR-game-state> return-g6))
        )
        (let 
            (
                (E (<pkg-state-g6P-<$$>-E> (<game-G6-<$$>-pkgstate-g6> state-g6)))
                (T (<pkg-state-g5P-<$$>-T> (<game-G5-<$$>-pkgstate-g5> state-g5)))
                (TH (<pkg-state-g6P-<$$>-TH> (<game-G6-<$$>-pkgstate-g6> state-g6)))
                (oldTXTR (<pkg-state-g6P-<$$>-TXTR> (<game-G6-<$$>-pkgstate-g6> old-state-g6)))
                (TXTR (<pkg-state-g6P-<$$>-TXTR> (<game-G6-<$$>-pkgstate-g6> state-g6)))
            )
            (and 
                (=>
                    (not ((_ is mk-none) (select TXTR (mk-tuple3 X Y s))))
                    (= (mk-tuple2 X Y) (maybe-get (<<func-find_collision_in_TXTR>> TXTR (<<func-exp>> Y (maybe-get (select E X))) s)))
                )
                (=>
                    ((_ is mk-none) (<<func-find_collision_in_TXTR>> oldTXTR (<<func-exp>> Y (maybe-get (select E X))) s))
                    (forall 
                        (
                            (Xp Bits_*)
                            (Yp Bits_*)
                        )
                        (=>
                            (not ((_ is mk-none) (select TXTR (mk-tuple3 Xp Yp s))))
                            (not (= (<<func-exp>> Y (maybe-get (select E X))) (<<func-exp>> Yp (maybe-get (select E Xp)))))
                        )
                    )
                )
            )

        )
    )

)

; only for debugging; not used for proving

(define-fun <relation-assert-invariants-g5-g6-TXTR>
    (
        (old-state-g5  <GameState_G5_<$$>>)
        (old-state-g6  <GameState_G6_<$$>>)
        (return-g5 <OracleReturn-G5-<$$>-g5P-<$$>-TXTR>)
        (return-g6 <OracleReturn-G6-<$$>-g6P-<$$>-TXTR>)
        (X Bits_*)
        (Y Bits_*)
        (s Bits_*)
    )
    Bool
    (let
        (
            (state-g5 (<oracle-return-G5-<$$>-g5P-<$$>-TXTR-game-state> return-g5))
            (state-g6 (<oracle-return-G6-<$$>-g6P-<$$>-TXTR-game-state> return-g6))
        )
        (let 
            (
                (E_left (<pkg-state-g5P-<$$>-E> (<game-G5-<$$>-pkgstate-g5> state-g5)))
                (E_right (<pkg-state-g6P-<$$>-E> (<game-G6-<$$>-pkgstate-g6> state-g6)))
                (oldT (<pkg-state-g5P-<$$>-T> (<game-G5-<$$>-pkgstate-g5> old-state-g5)))
                (T (<pkg-state-g5P-<$$>-T> (<game-G5-<$$>-pkgstate-g5> state-g5)))
                (oldTH (<pkg-state-g6P-<$$>-TH> (<game-G6-<$$>-pkgstate-g6> old-state-g6)))
                (TH (<pkg-state-g6P-<$$>-TH> (<game-G6-<$$>-pkgstate-g6> state-g6)))
                (oldTXTR (<pkg-state-g6P-<$$>-TXTR> (<game-G6-<$$>-pkgstate-g6> old-state-g6)))
                (TXTR (<pkg-state-g6P-<$$>-TXTR> (<game-G6-<$$>-pkgstate-g6> state-g6)))
                (returnpoint (<pkg-state-g6P-<$$>-returnpoint> (<game-G6-<$$>-pkgstate-g6> state-g6)) )
            )
            (and 
                ; TH[Z, s] = h != None => T[Z, s] = h
                (invariant-TH-implies-T E_left T TH TXTR)
                ; T[Z, s] = h != None => TH[Z, s] = h or 
                ; there exists X, Y such that Y^E[X] = Z and TXTR[X, Y, s] = h
                (invariant-T-NotNone-implies-TH-and-TXTR E_left T TH TXTR)
    
    (forall 
        (
            (Z Bits_*)
            (s Bits_*)
        )
        (
            =>
            (not (= Z (<<func-exp>> Y (maybe-get (select E_left X)))))
            (= (select T (mk-tuple2 Z s)) (select oldT (mk-tuple2 Z s)))
        )
    ); proved
                
(=>
    (not (= returnpoint 10))
    (forall 
        (
            (Z Bits_*)
            (s Bits_*)
        )
        (=> 
        ;true
            (not (= Z (<<func-exp>> Y (maybe-get (select E_left X)))))
            ; this means setting TXTR in G6 might break some thing from previous ones
            ; 
            ; we need the none property of find_collision

            (let 
                (
                    (h (select T (mk-tuple2 Z s)))
                )
                (=>
                    (not ((_ is mk-none) h))
                    (or
                        (= h (select TH (mk-tuple2 Z s)))
                        (let 
                            (
                                (XY (<<func-find_collision_in_TXTR>> TXTR Z s))
                            )
                            (and 
                                (not ((_ is mk-none) XY))
                                (let 
                                    (
                                        (X (el2-1 (maybe-get XY)))
                                        (Y (el2-2 (maybe-get XY)))
                                    )
                                    (and 
                                        (= h (select TXTR (mk-tuple3 X Y s)))
                                        (= Z (<<func-exp>> Y (maybe-get (select E_left X))))
                                    )
                                )
                            )
                        )
                    )
                )
            )
        )
    )
)

                ; T[Z, s] = None if and only if
                ; TH[Z, s] = None and
                ; forall X, Y such that Y^E[X] = Z and TXTR[X, Y, s] = None
                (invariant-T-None-implies-TH-and-TXTR E_left T TH TXTR)
                ; TXTR[X, Y, s] = h != None => T[Y^E[X], s] = h
                (invariant-TXTR-implies-T E_left T TH TXTR)
            )
            
        )
    )

)

(define-fun <relation-lemma-find-collision-g5-g6-TH>
    (
        (old-state-g5  <GameState_G5_<$$>>)
        (old-state-g6  <GameState_G6_<$$>>)
        (return-g5 <OracleReturn-G5-<$$>-g5P-<$$>-TH>)
        (return-g6 <OracleReturn-G6-<$$>-g6P-<$$>-TH>)
        (Z Bits_*)
        (s Bits_*)
    )
    Bool
    (let 
        (
            (E (<pkg-state-g6P-<$$>-E> (<game-G6-<$$>-pkgstate-g6> old-state-g6)))
            ; should be new state of G6 not old state
            (XY (<pkg-state-g6P-<$$>-XY> (<game-G6-<$$>-pkgstate-g6> old-state-g6)))
            (TXTR (<pkg-state-g6P-<$$>-TXTR> (<game-G6-<$$>-pkgstate-g6> old-state-g6)))
        )
        (and 
            (=>
                (not ((_ is mk-none) XY))
                (let 
                    (
                        (X (el2-1 (maybe-get XY)))
                        (Y (el2-2 (maybe-get XY)))
                    )
                    (and 
                        (= Z (<<func-exp>> Y (maybe-get (select E X))))
                        (not ((_ is mk-none) (select TXTR (mk-tuple3 X Y s))))
                    )
                )
            )
        )
    )
)