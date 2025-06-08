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
                    (exists 
                        (
                            (X Bits_*)
                            (Y Bits_*)
                        )
                        (and 
                            (= h (select TXTR (mk-tuple3 X Y s)))
                            (= Z (<<func-exp>> Y (maybe-get (select E X))))
                        )
                    )
                    ;(let 
                    ;    (
                    ;        (XY (<<func-find_collision_in_TXTR>> TXTR Z s))
                    ;    )
                    ;    (and 
                    ;        (not ((_ is mk-none) XY))
                    ;        (let 
                    ;            (
                    ;                (X (el2-1 (maybe-get XY)))
                    ;                (Y (el2-2 (maybe-get XY)))
                    ;            )
                    ;            (and 
                    ;                (= h (select TXTR (mk-tuple3 X Y s)))
                    ;                (= Z (<<func-exp>> Y (maybe-get (select E X))))
                    ;            )
                    ;        )
                    ;    )
                    ;)
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
    ; forall X, Y such that Y^E[X] = Z then TXTR[X, Y, s] = None
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
                    ;((_ is mk-none) (<<func-find_collision_in_TXTR>> TXTR Z s))
                    (forall 
                        (
                            (X Bits_*)
                            (Y Bits_*)
                        )
                        (=>
                            (= Z (<<func-exp>> Y (maybe-get (select E X))))
                            ((_ is mk-none) (select TXTR (mk-tuple3 X Y s)))
                        )
                    )
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
            ; forall X, Y such that Y^E[X] = Z then TXTR[X, Y, s] = None
            ;(invariant-T-None-implies-TH-and-TXTR E_left T TH TXTR)
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
        (XXXX Bits_*)
        (YYYY Bits_*)
        (ssss Bits_*)
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
            )
            (and
                ; find(table, Z, s) = None if and only if forall X,Y. table[X, Y, s] != None => Z = Y^E[X]
                (forall 
                    (
                        (Zp Bits_*)
                        (sp Bits_*)
                        (table (Array (Tuple3 Bits_* Bits_* Bits_*) (Maybe Bits_*)))
                    )
                    (=
                        ((_ is mk-none) (<<func-find_collision_in_TXTR>> table Zp sp)) 
                        (forall 
                            (
                                (Xp Bits_*)
                                (Yp Bits_*)
                            )
                            (=>
                                (not ((_ is mk-none) (select table (mk-tuple3 Xp Yp sp))))
                                (not (= Zp (<<func-exp>> Yp (maybe-get (select E Xp)))))
                            )
                        )
                    )
                )
                (forall 
                    (
                        (Zp Bits_*)
                        (Xp Bits_*)
                        (Yp Bits_*)
                        (sp Bits_*)
                        (table (Array (Tuple3 Bits_* Bits_* Bits_*) (Maybe Bits_*)))
                    )
                    (and 
                        ; if e = find(table, Z, s) then e_Y ^E[e_X] = Z and table[e_x, e_y, s] != None
                        (let 
                            (
                                (e (<<func-find_collision_in_TXTR>> table Zp sp))
                            )
                            (=>
                                (not ((_ is mk-none) e))
                                (let 
                                    (
                                        (eX (el2-1 (maybe-get e)))
                                        (eY (el2-2 (maybe-get e)))
                                    )
                                    (and
                                        (not ((_ is mk-none) (select table (mk-tuple3 eX eY sp))))
                                        (= Zp (<<func-exp>> eY (maybe-get (select E eX))))
                                    )
                                )
                            )
                        )
                        ; if table[X, Y, s] != None then find(table, y^E[X], s) = (X, Y)
                        (=>
                            (not ((_ is mk-none) (select table (mk-tuple3 Xp Yp sp))))
                            ;(= (mk-tuple2 Xp Yp) (maybe-get (<<func-find_collision_in_TXTR>> table (<<func-exp>> Yp (maybe-get (select E_left Xp))) sp)))
                            (= (mk-some (mk-tuple2 Xp Yp))  (<<func-find_collision_in_TXTR>> table (<<func-exp>> Yp (maybe-get (select E Xp))) sp))
                        )
                    )
                )

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
        (ZZZZ Bits_*)
        (ssss Bits_*)
    )
    Bool
    (let
        (
            (state-g5 (<oracle-return-G5-<$$>-g5P-<$$>-TH-game-state> return-g5))
            (state-g6 (<oracle-return-G6-<$$>-g6P-<$$>-TH-game-state> return-g6))
        )
        (let 
            (
                (E (<pkg-state-g6P-<$$>-E> (<game-G6-<$$>-pkgstate-g6> state-g6)))
            )
            (and
                ; find(table, Z, s) = None if and only if forall X,Y. table[X, Y, s] != None => Z = Y^E[X]
                (forall 
                    (
                        (Zp Bits_*)
                        (sp Bits_*)
                        (table (Array (Tuple3 Bits_* Bits_* Bits_*) (Maybe Bits_*)))
                    )
                    (=
                        ((_ is mk-none) (<<func-find_collision_in_TXTR>> table Zp sp)) 
                        (forall 
                            (
                                (Xp Bits_*)
                                (Yp Bits_*)
                            )
                            (=>
                                (not ((_ is mk-none) (select table (mk-tuple3 Xp Yp sp))))
                                (not (= Zp (<<func-exp>> Yp (maybe-get (select E Xp)))))
                            )
                        )
                    )
                )
                (forall 
                    (
                        (Zp Bits_*)
                        (Xp Bits_*)
                        (Yp Bits_*)
                        (sp Bits_*)
                        (table (Array (Tuple3 Bits_* Bits_* Bits_*) (Maybe Bits_*)))
                    )
                    (and 
                        ; if e = find(table, Z, s) then e_Y ^E[e_X] = Z and table[e_x, e_y, s] != None
                        (let 
                            (
                                (e (<<func-find_collision_in_TXTR>> table Zp sp))
                            )
                            (=>
                                (not ((_ is mk-none) e))
                                (let 
                                    (
                                        (eX (el2-1 (maybe-get e)))
                                        (eY (el2-2 (maybe-get e)))
                                    )
                                    (and
                                        (not ((_ is mk-none) (select table (mk-tuple3 eX eY sp))))
                                        (= Zp (<<func-exp>> eY (maybe-get (select E eX))))
                                    )
                                )
                            )
                        )
                        ; if table[X, Y, s] != None then find(table, y^E[X], s) = (X, Y)
                        (=>
                            (not ((_ is mk-none) (select table (mk-tuple3 Xp Yp sp))))
                            ;(= (mk-tuple2 Xp Yp) (maybe-get (<<func-find_collision_in_TXTR>> table (<<func-exp>> Yp (maybe-get (select E_left Xp))) sp)))
                            (= (mk-some (mk-tuple2 Xp Yp))  (<<func-find_collision_in_TXTR>> table (<<func-exp>> Yp (maybe-get (select E Xp))) sp))
                        )
                    )
                )

            )

        )
    )

)

; only for debugging; not used for proving

(define-fun <relation-assume-uniqueness-and-none-collision-g5-g6-TH>
    (
        (old-state-g5  <GameState_G5_<$$>>)
        (old-state-g6  <GameState_G6_<$$>>)
        (return-g5 <OracleReturn-G5-<$$>-g5P-<$$>-TH>)
        (return-g6 <OracleReturn-G6-<$$>-g6P-<$$>-TH>)
        (ZZZZ Bits_*)
        (ssss Bits_*)
    )
    Bool
    (let
        (
            (state-g5 (<oracle-return-G5-<$$>-g5P-<$$>-TH-game-state> return-g5))
            (state-g6 (<oracle-return-G6-<$$>-g6P-<$$>-TH-game-state> return-g6))
        )
        (let 
            (
                (E_left (<pkg-state-g5P-<$$>-E> (<game-G5-<$$>-pkgstate-g5> state-g5)))
                (oldTXTR (<pkg-state-g6P-<$$>-TXTR> (<game-G6-<$$>-pkgstate-g6> old-state-g6)))
            )
            (and
                ; not necessary for verification but important for well-definedness 
                ; of find_collision_in_TXTR
                ; for each Z, there is exactly one X, Y pair in TXTR such that 
                ; Y^E[X] = Z:
                ; i.e.
                ; TXTR[X, Y, s] != None => 
                ; forall X', Y' if TXTR[X', Y', s] != None and Y^E[X] = Y'^E[X'] =>
                ; X = S' and Y = Y'
                (forall 
                    (
                        (X Bits_*)
                        (Y Bits_*)
                        (s Bits_*)
                    )
                    (=>
                        (not ((_ is mk-none) (select oldTXTR (mk-tuple3 X Y s))))
                        (forall
                            (
                                (Xp Bits_*)
                                (Yp Bits_*)
                            )
                            (=>
                                (and 
                                    (not ((_ is mk-none) (select oldTXTR (mk-tuple3 Xp Yp s))))
                                    (= (<<func-exp>> Y (maybe-get (select E_left X))) (<<func-exp>> Yp (maybe-get (select E_left Xp))))
                                )
                                (and 
                                    (= X Xp)
                                    (= Y Yp)
                                )
                            )
                        )
                    )
                )
            )
        
        )
    )
)

(define-fun <relation-assert-uniqueness-g5-g6-TH>
    (
        (old-state-g5  <GameState_G5_<$$>>)
        (old-state-g6  <GameState_G6_<$$>>)
        (return-g5 <OracleReturn-G5-<$$>-g5P-<$$>-TH>)
        (return-g6 <OracleReturn-G6-<$$>-g6P-<$$>-TH>)
        (ZZZZ Bits_*)
        (ssss Bits_*)
    )
    Bool
    (let
        (
            (state-g5 (<oracle-return-G5-<$$>-g5P-<$$>-TH-game-state> return-g5))
            (state-g6 (<oracle-return-G6-<$$>-g6P-<$$>-TH-game-state> return-g6))
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
            )
            (and
                ; not necessary for verification but important for well-definedness 
                ; of find_collision_in_TXTR
                ; for each Z, there is exactly one X, Y pair in TXTR such that 
                ; Y^E[X] = Z:
                ; i.e.
                ; TXTR[X, Y, s] != None => 
                ; forall X', Y' if TXTR[X', Y', s] != None and Y^E[X] = Y'^E[X'] =>
                ; X = S' and Y = Y'
                (forall 
                    (
                        (X Bits_*)
                        (Y Bits_*)
                        (s Bits_*)
                    )
                    (=>
                        (not ((_ is mk-none) (select TXTR (mk-tuple3 X Y s))))
                        (forall
                            (
                                (Xp Bits_*)
                                (Yp Bits_*)
                            )
                            (=>
                                (and 
                                    (not ((_ is mk-none) (select TXTR (mk-tuple3 Xp Yp s))))
                                    (= (<<func-exp>> Y (maybe-get (select E_left X))) (<<func-exp>> Yp (maybe-get (select E_left Xp))))
                                )
                                (and 
                                    (= X Xp)
                                    (= Y Yp)
                                )
                            )
                        )
                    )
                )
            )
        )
    )
)

(define-fun <relation-assume-uniqueness-and-none-collision-g5-g6-TXTR>
    (
        (old-state-g5  <GameState_G5_<$$>>)
        (old-state-g6  <GameState_G6_<$$>>)
        (return-g5 <OracleReturn-G5-<$$>-g5P-<$$>-TXTR>)
        (return-g6 <OracleReturn-G6-<$$>-g6P-<$$>-TXTR>)
        (X Bits_*)
        (Y Bits_*)
        (ssss Bits_*)
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
                (oldTXTR (<pkg-state-g6P-<$$>-TXTR> (<game-G6-<$$>-pkgstate-g6> old-state-g6)))
            )
            (and
                ; find(table, Z, s) = None => forall X,Y. table[X, Y, s] != None => Z = Y^E[X]
                (forall 
                    (
                        (Zp Bits_*)
                        (sp Bits_*)
                        (table (Array (Tuple3 Bits_* Bits_* Bits_*) (Maybe Bits_*)))
                    )
                    (=>
                        ((_ is mk-none) (<<func-find_collision_in_TXTR>> table Zp sp)) 
                        (forall 
                            (
                                (Xp Bits_*)
                                (Yp Bits_*)
                            )
                            (=>
                                (not ((_ is mk-none) (select table (mk-tuple3 Xp Yp sp))))
                                (not (= Zp (<<func-exp>> Yp (maybe-get (select E_left Xp)))))
                            )
                        )
                    )
                )            
                ; not necessary for verification but important for well-definedness 
                ; of find_collision_in_TXTR
                ; for each Z, there is exactly one X, Y pair in TXTR such that 
                ; Y^E[X] = Z:
                ; i.e.
                ; TXTR[X, Y, s] != None => 
                ; forall X', Y' if TXTR[X', Y', s] != None and Y^E[X] = Y'^E[X'] =>
                ; X = S' and Y = Y'
                (forall 
                    (
                        (X Bits_*)
                        (Y Bits_*)
                        (s Bits_*)
                    )
                    (=>
                        (not ((_ is mk-none) (select oldTXTR (mk-tuple3 X Y s))))
                        (forall
                            (
                                (Xp Bits_*)
                                (Yp Bits_*)
                            )
                            (=>
                                (and 
                                    (not ((_ is mk-none) (select oldTXTR (mk-tuple3 Xp Yp s))))
                                    (= (<<func-exp>> Y (maybe-get (select E_left X))) (<<func-exp>> Yp (maybe-get (select E_left Xp))))
                                )
                                (and 
                                    (= X Xp)
                                    (= Y Yp)
                                )
                            )
                        )
                    )
                )
            )
        
        )
    )
)

(define-fun <relation-assert-uniqueness-g5-g6-TXTR>
    (
        (old-state-g5  <GameState_G5_<$$>>)
        (old-state-g6  <GameState_G6_<$$>>)
        (return-g5 <OracleReturn-G5-<$$>-g5P-<$$>-TXTR>)
        (return-g6 <OracleReturn-G6-<$$>-g6P-<$$>-TXTR>)
        (X Bits_*)
        (Y Bits_*)
        (ssss Bits_*)
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
                (TXTR (<pkg-state-g6P-<$$>-TXTR> (<game-G6-<$$>-pkgstate-g6> state-g6)))
            )
                ; not necessary for verification but important for well-definedness 
                ; of find_collision_in_TXTR
                ; for each Z, there is exactly one X, Y pair in TXTR such that 
                ; Y^E[X] = Z:
                ; i.e.
                ; TXTR[X, Y, s] != None => 
                ; forall X', Y' if TXTR[X', Y', s] != None and Y^E[X] = Y'^E[X'] =>
                ; X = S' and Y = Y'
                (forall 
                    (
                        (X Bits_*)
                        (Y Bits_*)
                        (s Bits_*)
                    )
                    (=>
                        (not ((_ is mk-none) (select TXTR (mk-tuple3 X Y s))))
                        (forall
                            (
                                (Xp Bits_*)
                                (Yp Bits_*)
                            )
                            (=>
                                (and 
                                    (not ((_ is mk-none) (select TXTR (mk-tuple3 Xp Yp s))))
                                    (= (<<func-exp>> Y (maybe-get (select E_left X))) (<<func-exp>> Yp (maybe-get (select E_left Xp))))
                                )
                                (and 
                                    (= X Xp)
                                    (= Y Yp)
                                )
                            )
                        )
                    )
                )
        )
    )
)

(define-fun <relation-assert-invariants-g5-g6-TXTR>
    (
        (old-state-g5  <GameState_G5_<$$>>)
        (old-state-g6  <GameState_G6_<$$>>)
        (return-g5 <OracleReturn-G5-<$$>-g5P-<$$>-TXTR>)
        (return-g6 <OracleReturn-G6-<$$>-g6P-<$$>-TXTR>)
        (X Bits_*)
        (Y Bits_*)
        (ssss Bits_*)
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
        (and 
            ((_ is mk-none) (select oldTH (mk-tuple2 (<<func-exp>> Y (maybe-get (select E_left X))) ssss)))
            ((_ is mk-none) (<<func-find_collision_in_TXTR>> oldTXTR (<<func-exp>> Y (maybe-get (select E_left X))) ssss))
        )
        (and
            (not ((_ is mk-none) (select TXTR (mk-tuple3 X Y ssss))))
            (= (select TXTR (mk-tuple3 X Y ssss)) (select T (mk-tuple2 (<<func-exp>> Y (maybe-get (select E_left X))) ssss)))
            (= (maybe-get (<<func-find_collision_in_TXTR>> TXTR (<<func-exp>> Y (maybe-get (select E_left X))) ssss)) (mk-tuple2 X Y))
            (forall 
                (
                    (Z Bits_*)
                    (s Bits_*)
                )
                (=> 
                    
                    (not (= Z (<<func-exp>> Y (maybe-get (select E_left X)))))
                    ; this means setting TXTR in G6 might break some thing from previous ones
                    ; we need the none property of find_collision
                    (and
                        (=>
                            ; checking whether the axiom suffices to prove first step
                            ; we can remove quantification over table and state it twice for TXTR and TH but we need for all Z, s
                            (forall 
                                (
                                    (Zp Bits_*)
                                    (sp Bits_*)
                                    (table (Array (Tuple3 Bits_* Bits_* Bits_*) (Maybe Bits_*)))
                                )
                                (=
                                    ((_ is mk-none) (<<func-find_collision_in_TXTR>> table Zp sp)) 
                                    (forall 
                                        (
                                            (Xp Bits_*)
                                            (Yp Bits_*)
                                        )
                                        (=>
                                            (not ((_ is mk-none) (select table (mk-tuple3 Xp Yp sp))))
                                            (not (= Zp (<<func-exp>> Yp (maybe-get (select E_left Xp)))))
                                        )
                                    )
                                )
                            )
                            ; first step to prove (= (<<func-find_collision_in_TXTR>> TXTR Z s) (<<func-find_collision_in_TXTR>> oldTXTR Z s))
                            (=> 
                                ((_ is mk-none) (<<func-find_collision_in_TXTR>> TXTR Z s)) 
                                ((_ is mk-none) (<<func-find_collision_in_TXTR>> oldTXTR Z s))
                            )

                        )

                        (=>
                            ; we can remove quantification over table and state it twice for TXTR and TH but we need for all Z, s
                            (forall 
                                (
                                    (Zp Bits_*)
                                    (Xp Bits_*)
                                    (Yp Bits_*)
                                    (sp Bits_*)
                                    (table (Array (Tuple3 Bits_* Bits_* Bits_*) (Maybe Bits_*)))
                                )
                                (and 
                                    ; if e = find(table, Z, s) then e_Y ^E[e_X] = Z and table[e_x, e_y, s] != None
                                    (let 
                                        (
                                            (e (<<func-find_collision_in_TXTR>> table Zp sp))
                                        )
                                        (=>
                                            (not ((_ is mk-none) e))
                                            (let 
                                                (
                                                    (eX (el2-1 (maybe-get e)))
                                                    (eY (el2-2 (maybe-get e)))
                                                )
                                                (and
                                                    (not ((_ is mk-none) (select table (mk-tuple3 eX eY sp))))
                                                    (= Zp (<<func-exp>> eY (maybe-get (select E_left eX))))
                                                )
                                            )
                                        )
                                    )
                                    ; if table[X, Y, s] != None then find(table, y^E[X], s) = (X, Y)
                                    (=>
                                        (not ((_ is mk-none) (select table (mk-tuple3 Xp Yp sp))))
                                        ;(= (mk-tuple2 Xp Yp) (maybe-get (<<func-find_collision_in_TXTR>> table (<<func-exp>> Yp (maybe-get (select E_left Xp))) sp)))
                                        (= (mk-some (mk-tuple2 Xp Yp))  (<<func-find_collision_in_TXTR>> table (<<func-exp>> Yp (maybe-get (select E_left Xp))) sp))
                                    )
                                )
                            )
                            ; second step to prove (= (<<func-find_collision_in_TXTR>> TXTR Z s) (<<func-find_collision_in_TXTR>> oldTXTR Z s))
                            (let 
                                (
                                    (e (<<func-find_collision_in_TXTR>> TXTR Z s))
                                )
                                (=>
                                    (not ((_ is mk-none) e))
                                    (and 
                                            (let 
                                                (
                                                    (eX (el2-1 (maybe-get e)))
                                                    (eY (el2-2 (maybe-get e)))
                                                )
                                                (and
                                                    (not ((_ is mk-none) (select TXTR (mk-tuple3 eX eY s))))
                                                    (= Z (<<func-exp>> eY (maybe-get (select E_left eX))))
                                                    (not (and (= Y eY) (= X eX)))
                                                    (not ((_ is mk-none) (select oldTXTR (mk-tuple3 eX eY s))))
                                                    (= (mk-tuple2 eX eY) (maybe-get (<<func-find_collision_in_TXTR>> oldTXTR (<<func-exp>> eY (maybe-get (select E_left eX))) s)))
                                                    (= (maybe-get e) (mk-tuple2 eX eY) )
                                                    (= e (<<func-find_collision_in_TXTR>> oldTXTR Z s))
                                                )
                                            )
                                            (= e (<<func-find_collision_in_TXTR>> oldTXTR Z s))
                                    )
                                )
                            )
                        )

                        (=>
                            false
                            ; second step to prove (= (<<func-find_collision_in_TXTR>> TXTR Z s) (<<func-find_collision_in_TXTR>> oldTXTR Z s))
                            (let 
                                (
                                    (e (<<func-find_collision_in_TXTR>> TXTR Z s))
                                )
                                (=>
                                    (not ((_ is mk-none) e))
                                    (= e (<<func-find_collision_in_TXTR>> oldTXTR Z s))
                                )
                            )
                        )

                        (=>
                            (and 
                                (let 
                                    (
                                        (e (<<func-find_collision_in_TXTR>> TXTR Z s))
                                    )
                                    (=>
                                        (not ((_ is mk-none) e))
                                        (= e (<<func-find_collision_in_TXTR>> oldTXTR Z s))
                                    )
                                )
                                (=> 
                                    ((_ is mk-none) (<<func-find_collision_in_TXTR>> TXTR Z s)) 
                                    ((_ is mk-none) (<<func-find_collision_in_TXTR>> oldTXTR Z s))
                                )
                            )
                            (= (<<func-find_collision_in_TXTR>> TXTR Z s) (<<func-find_collision_in_TXTR>> oldTXTR Z s))
                        )

                        ; but proving (= (<<func-find_collision_in_TXTR>> TXTR Z s) (<<func-find_collision_in_TXTR>> oldTXTR Z s))
                        ; seems to be enough
                        (=>
                            (= (<<func-find_collision_in_TXTR>> TXTR Z s) (<<func-find_collision_in_TXTR>> oldTXTR Z s))
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
            )
        )
    )

                ; T[Z, s] = None if and only if
                ; TH[Z, s] = None and
                ; forall X, Y such that Y^E[X] = Z then TXTR[X, Y, s] = None
                (invariant-T-None-implies-TH-and-TXTR E_left T TH TXTR)
                ; TXTR[X, Y, s] = h != None => T[Y^E[X], s] = h
                (invariant-TXTR-implies-T E_left T TH TXTR)
            )
            
        )
    )

)