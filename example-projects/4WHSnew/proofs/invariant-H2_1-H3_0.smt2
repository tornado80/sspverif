                                        ; Main idea of this invariant proof
                                        ; If ctr are equal in both games and they use the same randomness, then both games
                                        ;    - produce the same output
                                        ;    - abort iff the other aborts
                                        ;    - have same ctr afterwards

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
                                        ;
                                        ; Randomness mapping
                                        ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun randomness-mapping-Send1
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
   (= id-0      0)  ; This is the 2nd sampling in KX and samples ni.
   (= id-1      0)  ; This sampling happens in the Nonces package and is the 2nd sampling (in fact the last sampling, because Nonces is defined last).
   ))

(define-fun randomness-mapping-Send2
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
   (= id-0     0)   ; This is the 3rd sampling in KX and samples nr.
   (= id-1     0)   ; This sampling happens in the Nonces package and is the 2nd sampling (in fact the last sampling, because Nonces is defined last).
   ))

(define-fun randomness-mapping-Send3
    ( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
      (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
      (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
      (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
      (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
      (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
                                        ; There is no randomness used in this oracle.
  false
  )

(define-fun randomness-mapping-Send4
    ( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
      (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
      (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
      (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
      (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
      (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
                                        ; There is no randomness used in this oracle.
  false
  )

(define-fun randomness-mapping-Send5
    ( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
      (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
      (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
      (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
      (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
      (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
                                        ; There is no randomness used in this oracle.
  false
  )

(define-fun randomness-mapping-Reveal
    ( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
      (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
      (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
      (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
      (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
      (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
                                        ; There is no randomness used in this oracle.
  false
  )

(define-fun randomness-mapping-Test
    ( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
      (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
      (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
      (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
      (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
      (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
  (and
   (= scr-1 base-ctr-1)
   (= id-0     2)   ; This is the 1st sampling in KX   and samples the random key in Test.
   (= id-1     2)   ; This is the 1st sampling in H1_0 and samples the random key in Test.
   ))

(define-fun randomness-mapping-NewKey
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
   (= id-0     1)   ; This is the 0th sampling in KX   and samples the random key in NewKey.
   (= id-1     1)   ; This is the 0th sampling in H1_0 and samples the random key in NewKey.
   ))

(define-fun randomness-mapping-NewSession
    ( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
      (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
      (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
      (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
      (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
      (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
                                        ; There is no randomness used in this oracle.
  false
  )

(define-fun randomness-mapping-SameKey
    ( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
      (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
      (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
      (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
      (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
      (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
                                        ; There is no randomness used in this oracle.
  false
  )
(define-fun randomness-mapping-AtMost
    ( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
      (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
      (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
      (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
      (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
      (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
                                        ; There is no randomness used in this oracle.
  false
  )
(define-fun randomness-mapping-AtLeast
    ( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
      (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
      (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
      (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
      (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
      (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
                                        ; There is no randomness used in this oracle.
  false
  )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
                                        ;                                                                                                      ;
                                        ; Invariant --- note that the invariant needs to be game-global and not per oracle,                    ;
                                        ;               so that induction over the oracle calls remains meaningful.                            ;
                                        ;                                                                                                      ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun <relation-mess-is-two-H2_1-H3_0-Send4>
    ((H2-old <GameState_H2_<$<!n!><!b!><!true!><!zeron!>$>>)
     (H3-old <GameState_H3_<$<!n!><!b!><!true!><!zeron!>$>>)
     (H2-return <OracleReturn-H2-<$<!n!><!b!><!true!><!zeron!>$>-Game-<$<!b!><!n!><!zeron!>$>-Send4>)
     (H3-return <OracleReturn-H3-<$<!n!><!b!><!true!><!zeron!>$>-Game_nochecks-<$<!b!><!n!><!zeron!>$>-Send4>)
     (ctr Int)
     (msg (Tuple2 Bits_256 Bits_256)))
  Bool
  (let ((gamestate-H2 (<game-H2-<$<!n!><!b!><!true!><!zeron!>$>-pkgstate-Game>     H2-old))
        (gamestate-H3 (<game-H3-<$<!n!><!b!><!true!><!zeron!>$>-pkgstate-Game_nochecks> H3-old))
        (newstate-H2  (<game-H2-<$<!n!><!b!><!true!><!zeron!>$>-pkgstate-Game>
                       (<oracle-return-H2-<$<!n!><!b!><!true!><!zeron!>$>-Game-<$<!b!><!n!><!zeron!>$>-Send4-game-state> H2-return)))
        (newstate-H3  (<game-H3-<$<!n!><!b!><!true!><!zeron!>$>-pkgstate-Game_nochecks>
                       (<oracle-return-H3-<$<!n!><!b!><!true!><!zeron!>$>-Game_nochecks-<$<!b!><!n!><!zeron!>$>-Send4-game-state> H3-return))))
    (let ((H2-state-old (<pkg-state-Game-<$<!b!><!n!><!zeron!>$>-State> gamestate-H2))
          (H3-state-old (<pkg-state-Game_nochecks-<$<!b!><!n!><!zeron!>$>-State> gamestate-H3))
          (H2-state-new (<pkg-state-Game-<$<!b!><!n!><!zeron!>$>-State> newstate-H2))
          (H3-state-new (<pkg-state-Game_nochecks-<$<!b!><!n!><!zeron!>$>-State> newstate-H3)))
      (and (= (select H2-state-new ctr)
              (select H3-state-new ctr))
           (=> (not (= (select H2-state-new ctr)
                       (as mk-none (Maybe (Tuple11 Int Bool Int Bits_256 (Maybe Bool)
                                                   (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                                   (Maybe (Tuple5 Int Int (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)))
                                                   Int)))))
               (= (el11-11 (maybe-get (select H2-state-new ctr))) 2))))))


                           ;(= key1 key2))))))))))



         ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Maybe the desired version
         ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; (forall ((ctr Int))
;;  (and
;;     (or (= (select H2-state ctr)
;;            (as mk-none (Maybe (Tuple12 Int Bool Int Bool Bits_256 (Maybe Bool)
;;                                        (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
;;                                        (Maybe (Tuple5 Int Int (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)))
;;                                        Int))))
;;      (exists ((U Int) (u Bool) (V Int) (v Bool) (ltk Bits_256) (acc (Maybe Bool))
;;               (k (Maybe Bits_256)) (ni (Maybe Bits_256)) (nr (Maybe Bits_256)) (kmac (Maybe Bits_256))
;;               (sid (Maybe (Tuple5 Int Int (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256))))
;;               (mess Int))
;;         (and (= (select H2-state ctr) (mk-some (mk-tuple12 U u V v ltk acc k ni nr kmac sid mess)))
;;             (=> (and (not (= 0 mess)) (not (= 1 mess)))
;;                 (or (= acc (mk-some false))
;;                     (not (= sid (as mk-none
;;                                     (Maybe (Tuple5 Int Int (Maybe Bits_256) (Maybe Bits_256)
;;                                                    (Maybe Bits_256)))))))))))
;;     (or (= (select H3-state ctr)
;;            (as mk-none (Maybe (Tuple12 Int Bool Int Bool Bits_256 (Maybe Bool)
;;                                        (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
;;                                        (Maybe (Tuple5 Int Int (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)))
;;                                        Int))))
;;      (exists ((U Int) (u Bool) (V Int) (v Bool) (ltk Bits_256) (acc (Maybe Bool))
;;               (k (Maybe Bits_256)) (ni (Maybe Bits_256)) (nr (Maybe Bits_256)) (kmac (Maybe Bits_256))
;;               (sid (Maybe (Tuple5 Int Int (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256))))
;;               (mess Int))
;;         (and (= (select H3-state ctr) (mk-some (mk-tuple12 U u V v ltk acc k ni nr kmac sid mess)))
;;             (and (=> (and (not (= 0 mess)) (not (= 1 mess)))
;;                      (or (= acc (mk-some false))
;;                          (not (= sid (as mk-none
;;                                          (Maybe (Tuple5 Int Int (Maybe Bits_256) (Maybe Bits_256)
;;                                                         (Maybe Bits_256))))))))))))))))))


(define-fun <relation-debug-H2_1-H3_0-Send4>
    ((H2-old <GameState_H2_<$<!n!><!b!><!true!><!zeron!>$>>)
     (H3-old <GameState_H3_<$<!n!><!b!><!true!><!zeron!>$>>)
     (H2-return <OracleReturn-H2-<$<!n!><!b!><!true!><!zeron!>$>-Game-<$<!b!><!n!><!zeron!>$>-Send4>)
     (H3-return <OracleReturn-H3-<$<!n!><!b!><!true!><!zeron!>$>-Game_nochecks-<$<!b!><!n!><!zeron!>$>-Send4>)
     (ctr Int)
     (msg (Tuple2 Bits_256 Bits_256)))
  Bool
  (let (
        (gamestate-H2  (<game-H2-<$<!n!><!b!><!true!><!zeron!>$>-pkgstate-Game>
                       (<oracle-return-H2-<$<!n!><!b!><!true!><!zeron!>$>-Game-<$<!b!><!n!><!zeron!>$>-Send4-game-state> H2-return)))
        (gamestate-H3  (<game-H3-<$<!n!><!b!><!true!><!zeron!>$>-pkgstate-Game_nochecks>
                       (<oracle-return-H3-<$<!n!><!b!><!true!><!zeron!>$>-Game_nochecks-<$<!b!><!n!><!zeron!>$>-Send4-game-state> H3-return)))
        (crstate-H2  (<game-H2-<$<!n!><!b!><!true!><!zeron!>$>-pkgstate-CR>
                       (<oracle-return-H2-<$<!n!><!b!><!true!><!zeron!>$>-Game-<$<!b!><!n!><!zeron!>$>-Send4-game-state> H2-return)))
        (crstate-H3  (<game-H3-<$<!n!><!b!><!true!><!zeron!>$>-pkgstate-CR>
                       (<oracle-return-H3-<$<!n!><!b!><!true!><!zeron!>$>-Game_nochecks-<$<!b!><!n!><!zeron!>$>-Send4-game-state> H3-return)))
        (noncesstate-H2  (<game-H2-<$<!n!><!b!><!true!><!zeron!>$>-pkgstate-Nonces>
                       (<oracle-return-H2-<$<!n!><!b!><!true!><!zeron!>$>-Game-<$<!b!><!n!><!zeron!>$>-Send4-game-state> H2-return)))
        (noncesstate-H3  (<game-H3-<$<!n!><!b!><!true!><!zeron!>$>-pkgstate-Nonces>
                       (<oracle-return-H3-<$<!n!><!b!><!true!><!zeron!>$>-Game_nochecks-<$<!b!><!n!><!zeron!>$>-Send4-game-state> H3-return))))
;(define-fun invariant-helper-Send4
;    ((state-kx     <GameState_H2_<$<!n!><!b!><!true!><!zeron!>$>>)
;     (state-kxred  <GameState_H3_<$<!n!><!b!><!true!><!zeron!>$>>))
;  Bool ; I am using gamestate-H2 and gamestate-H3 here although these point to the new state! 
;  (let ((gamestate-H2 (<game-H2-<$<!n!><!b!><!true!><!zeron!>$>-pkgstate-Game>     state-kx))
;        (gamestate-H3 (<game-H3-<$<!n!><!b!><!true!><!zeron!>$>-pkgstate-Game_nochecks> state-kxred))
;        (crstate-H2 (<game-H2-<$<!n!><!b!><!true!><!zeron!>$>-pkgstate-CR>     state-kx))
;        (crstate-H3 (<game-H3-<$<!n!><!b!><!true!><!zeron!>$>-pkgstate-CR> state-kxred)))
    (let ((h2-prf (<pkg-state-CR-<$<!bcr!><!n!>$>-PRFinverse> crstate-H2))
          (h3-prf (<pkg-state-CR-<$<!bcr!><!n!>$>-PRFinverse> crstate-H3))
          (h2-mac (<pkg-state-CR-<$<!bcr!><!n!>$>-MACinverse> crstate-H2))
          (h3-mac (<pkg-state-CR-<$<!bcr!><!n!>$>-MACinverse> crstate-H3))
          (H2-state (<pkg-state-Game-<$<!b!><!n!><!zeron!>$>-State> gamestate-H2))
          (H3-state (<pkg-state-Game_nochecks-<$<!b!><!n!><!zeron!>$>-State> gamestate-H3)))
      (and
       (forall ((k Bits_256))
               (and
                (let ((entry (select h2-mac k)))
                  (=> (not (= entry (as mk-none (Maybe (Tuple3 Bits_256 Bits_256 Int)))))
                      (let ((kmac  (el3-1 (maybe-get entry)))
                            (nonce (el3-2 (maybe-get entry)))
                            (label (el3-3 (maybe-get entry))))
                        (= k (<<func-mac>> kmac nonce label)))))
                (let ((entry (select h3-mac k)))
                  (=> (not (= entry (as mk-none (Maybe (Tuple3 Bits_256 Bits_256 Int)))))
                      (let ((kmac  (el3-1 (maybe-get entry)))
                            (nonce (el3-2 (maybe-get entry)))
                            (label (el3-3 (maybe-get entry))))
                        (= k (<<func-mac>> kmac nonce label)))))
                (let ((entry (select h2-prf k)))
                  (=> (not (= entry (as mk-none (Maybe (Tuple6 Bits_256 Int Int Bits_256 Bits_256 Bool)))))
                      (let ((ltk (el6-1 (maybe-get entry)))
                            (U    (el6-2 (maybe-get entry)))
                            (V    (el6-3 (maybe-get entry)))
                            (ni   (el6-4 (maybe-get entry)))
                            (nr   (el6-5 (maybe-get entry)))
                            (flag (el6-6 (maybe-get entry))))
                        (= k (<<func-prf>> ltk U V ni nr flag)))))
                (let ((entry (select h3-prf k)))
                  (=> (not (= entry (as mk-none (Maybe (Tuple6 Bits_256 Int Int Bits_256 Bits_256 Bool)))))
                      (let ((ltk (el6-1 (maybe-get entry)))
                            (U    (el6-2 (maybe-get entry)))
                            (V    (el6-3 (maybe-get entry)))
                            (ni   (el6-4 (maybe-get entry)))
                            (nr   (el6-5 (maybe-get entry)))
                            (flag (el6-6 (maybe-get entry))))
                        (= k (<<func-prf>> ltk U V ni nr flag)))))))

       (= (<pkg-state-Game-<$<!b!><!n!><!zeron!>$>-LTK> gamestate-H2)
          (<pkg-state-Game_nochecks-<$<!b!><!n!><!zeron!>$>-LTK> gamestate-H3))
       (= (<pkg-state-Game-<$<!b!><!n!><!zeron!>$>-H> gamestate-H2)
          (<pkg-state-Game_nochecks-<$<!b!><!n!><!zeron!>$>-H> gamestate-H3))
       (= (<pkg-state-Game-<$<!b!><!n!><!zeron!>$>-ctr_> gamestate-H2)
          (<pkg-state-Game_nochecks-<$<!b!><!n!><!zeron!>$>-ctr_> gamestate-H3))
       (= (<pkg-state-Game-<$<!b!><!n!><!zeron!>$>-kid_> gamestate-H2)
          (<pkg-state-Game_nochecks-<$<!b!><!n!><!zeron!>$>-kid_> gamestate-H3))
       (= (<pkg-state-Game-<$<!b!><!n!><!zeron!>$>-RevTested> gamestate-H2)
          (<pkg-state-Game_nochecks-<$<!b!><!n!><!zeron!>$>-RevTested> gamestate-H3))
       (= (<pkg-state-Game-<$<!b!><!n!><!zeron!>$>-Fresh> gamestate-H2)
          (<pkg-state-Game_nochecks-<$<!b!><!n!><!zeron!>$>-Fresh> gamestate-H3))
       (= (<pkg-state-Game-<$<!b!><!n!><!zeron!>$>-First> gamestate-H2)
          (<pkg-state-Game_nochecks-<$<!b!><!n!><!zeron!>$>-First> gamestate-H3))
       (= (<pkg-state-Game-<$<!b!><!n!><!zeron!>$>-Second> gamestate-H2)
          (<pkg-state-Game_nochecks-<$<!b!><!n!><!zeron!>$>-Second> gamestate-H3))
       (= (<pkg-state-Game-<$<!b!><!n!><!zeron!>$>-State> gamestate-H2)
          (<pkg-state-Game_nochecks-<$<!b!><!n!><!zeron!>$>-State> gamestate-H3))

       (= crstate-H2 crstate-H3)

;       (= (<game-H2-<$<!n!><!b!><!true!><!zeron!>$>-pkgstate-CR>     state-kx)
;          (<game-H3-<$<!n!><!b!><!true!><!zeron!>$>-pkgstate-CR> state-kxred))

       (= noncesstate-H2 noncesstate-H3)

;       (= (<game-H2-<$<!n!><!b!><!true!><!zeron!>$>-pkgstate-Nonces>     state-kx)
;          (<game-H3-<$<!n!><!b!><!true!><!zeron!>$>-pkgstate-Nonces> state-kxred))



       (forall ((ctr Int))
               (let ((state (select H2-state ctr)))
                 (=> (not (= state
                             (as mk-none (Maybe (Tuple11 Int Bool Int Bits_256 (Maybe Bool)
                                                         (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                                         (Maybe (Tuple5 Int Int (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)))
                                                         Int)))))
                     (let ((U    (el11-1  (maybe-get state)))
                           (u    (el11-2  (maybe-get state)))
                           (V    (el11-3  (maybe-get state)))
                           (ltk  (el11-4  (maybe-get state)))
                           (acc  (el11-5  (maybe-get state)))
                           (k    (el11-6  (maybe-get state)))
                           (ni   (el11-7  (maybe-get state)))
                           (nr   (el11-8  (maybe-get state)))
                           (kmac (el11-9  (maybe-get state)))
                           (sid  (el11-10 (maybe-get state)))
                           (mess (el11-11 (maybe-get state))))
                       (and
                        (=> (> 2 mess) (= acc (as mk-none (Maybe Bool))))
                        (=> (> mess 0) ; message larger than 0
                            (and (not (= ni (as mk-none (Maybe Bits_256))))
                                 (=> u
                                     (and (not (= nr (as mk-none (Maybe Bits_256))))
                                          (= sid (mk-some (mk-tuple5 V U ni nr
                                                                     (mk-some (<<func-mac>> (maybe-get kmac)
                                                                                            (maybe-get nr)
                                                                                            2)))))
                                          (= k (mk-some (<<func-prf>> ltk V U
                                                                      (maybe-get ni)
                                                                      (maybe-get nr)
                                                                      true)))
                                          (= (select h2-prf (maybe-get k))
                                             (mk-some (mk-tuple6 ltk V U (maybe-get ni) (maybe-get nr) true)))
                                          (= kmac (mk-some (<<func-prf>> ltk V U
                                                                         (maybe-get ni)
                                                                         (maybe-get nr)
                                                                         false)))
                                          (= (select h2-prf (maybe-get kmac))
                                             (mk-some (mk-tuple6 ltk V U (maybe-get ni) (maybe-get nr) false)))))))
                        (=> (and (> mess 1) ; message large than 1
                                 (= acc (mk-some true))) ; accept = true
                            (and ; (not (= ni (as mk-none (Maybe Bits_256))))
                             (not (= nr (as mk-none (Maybe Bits_256))))
                             (not (= kmac (as mk-none (Maybe Bits_256))))
                             (=> (not u)
                                 (and (= sid (mk-some (mk-tuple5 U V ni nr
                                                                 (mk-some (<<func-mac>> (maybe-get kmac)
                                                                                        (maybe-get nr)
                                                                                        2)))))
                                      (= k (mk-some (<<func-prf>> ltk U V
                                                                  (maybe-get ni)
                                                                  (maybe-get nr)
                                                                  true)))
                                      (= (select h2-prf (maybe-get k))
                                         (mk-some (mk-tuple6 ltk U V (maybe-get ni) (maybe-get nr) true)))
                                      (= kmac (mk-some (<<func-prf>> ltk U V
                                                                     (maybe-get ni)
                                                                     (maybe-get nr)
                                                                     false)))
                                      (= (select h2-prf (maybe-get kmac))
                                         (mk-some (mk-tuple6 ltk U V (maybe-get ni) (maybe-get nr) false))))))))))))
       (forall ((ctr1 Int) (ctr2 Int))
               (let ((state1 (select H2-state ctr1))
                     (state2 (select H2-state ctr2)))
                 (=> (and (not (= state1
                                  (as mk-none (Maybe (Tuple11 Int Bool Int Bits_256 (Maybe Bool)
                                                              (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                                              (Maybe (Tuple5 Int Int (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)))
                                                              Int)))))
                          (not (= state2
                                  (as mk-none (Maybe (Tuple11 Int Bool Int Bits_256 (Maybe Bool)
                                                              (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                                              (Maybe (Tuple5 Int Int (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)))
                                                              Int))))))
                     (let ((acc1 (el11-5  (maybe-get (select H2-state ctr1))))
                           (acc2 (el11-5  (maybe-get (select H2-state ctr2))))
                           (key1 (el11-6  (maybe-get (select H2-state ctr1))))
                           (key2 (el11-6  (maybe-get (select H2-state ctr2))))
                           (sid1 (el11-10 (maybe-get (select H2-state ctr1))))
                           (sid2 (el11-10 (maybe-get (select H2-state ctr2)))))
                       (=> (and (= (mk-some true) acc1 acc2)
                                (= sid1 sid2))
                           (= key1 key2))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Helper Functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun 

                     (let ((U    (el11-1  (maybe-get state)))
                           (u    (el11-2  (maybe-get state)))
                           (V    (el11-3  (maybe-get state)))
                           (ltk  (el11-4  (maybe-get state)))
                           (acc  (el11-5  (maybe-get state)))
                           (k    (el11-6  (maybe-get state)))
                           (ni   (el11-7  (maybe-get state)))
                           (nr   (el11-8  (maybe-get state)))
                           (kmac (el11-9  (maybe-get state)))
                           (sid  (el11-10 (maybe-get state)))
                           (mess (el11-11 (maybe-get state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; INVARIANT STARTS HERE
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun invariant
    ((state-kx     <GameState_H2_<$<!n!><!b!><!true!><!zeron!>$>>)
     (state-kxred  <GameState_H3_<$<!n!><!b!><!true!><!zeron!>$>>))
  Bool
  (let ((gamestate-H2 (<game-H2-<$<!n!><!b!><!true!><!zeron!>$>-pkgstate-Game>     state-kx))
        (gamestate-H3 (<game-H3-<$<!n!><!b!><!true!><!zeron!>$>-pkgstate-Game_nochecks> state-kxred))
        (crstate-H2 (<game-H2-<$<!n!><!b!><!true!><!zeron!>$>-pkgstate-CR>     state-kx))
        (crstate-H3 (<game-H3-<$<!n!><!b!><!true!><!zeron!>$>-pkgstate-CR> state-kxred))
        (noncestate-H2 (<game-H2-<$<!n!><!b!><!true!><!zeron!>$>-pkgstate-Nonces> state-kx))
        (noncestate-H3 (<game-H3-<$<!n!><!b!><!true!><!zeron!>$>-pkgstate-Nonces> state-kxred)))
    (let ((h2-prf (<pkg-state-CR-<$<!bcr!><!n!>$>-PRFinverse> crstate-H2))
          (h3-prf (<pkg-state-CR-<$<!bcr!><!n!>$>-PRFinverse> crstate-H3))
          (h2-mac (<pkg-state-CR-<$<!bcr!><!n!>$>-MACinverse> crstate-H2))
          (h3-mac (<pkg-state-CR-<$<!bcr!><!n!>$>-MACinverse> crstate-H3))
          (h2-nonces (<pkg-state-Nonces-<$<!true!><!n!>$>-Nonces> noncestate-H2))
          (h3-nonces (<pkg-state-Nonces-<$<!true!><!n!>$>-Nonces> noncestate-H3))
          (H2-state (<pkg-state-Game-<$<!b!><!n!><!zeron!>$>-State> gamestate-H2))
          (H3-state (<pkg-state-Game_nochecks-<$<!b!><!n!><!zeron!>$>-State> gamestate-H3)))
      (and
	   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	   ;; Package states are, in general, equal
       (= (<pkg-state-Game-<$<!b!><!n!><!zeron!>$>-LTK> gamestate-H2)
          (<pkg-state-Game_nochecks-<$<!b!><!n!><!zeron!>$>-LTK> gamestate-H3))
       (= (<pkg-state-Game-<$<!b!><!n!><!zeron!>$>-H> gamestate-H2)
          (<pkg-state-Game_nochecks-<$<!b!><!n!><!zeron!>$>-H> gamestate-H3))
       (= (<pkg-state-Game-<$<!b!><!n!><!zeron!>$>-ctr_> gamestate-H2)
          (<pkg-state-Game_nochecks-<$<!b!><!n!><!zeron!>$>-ctr_> gamestate-H3))
       (= (<pkg-state-Game-<$<!b!><!n!><!zeron!>$>-kid_> gamestate-H2)
          (<pkg-state-Game_nochecks-<$<!b!><!n!><!zeron!>$>-kid_> gamestate-H3))
       (= (<pkg-state-Game-<$<!b!><!n!><!zeron!>$>-RevTested> gamestate-H2)
          (<pkg-state-Game_nochecks-<$<!b!><!n!><!zeron!>$>-RevTested> gamestate-H3))
       (= (<pkg-state-Game-<$<!b!><!n!><!zeron!>$>-Fresh> gamestate-H2)
          (<pkg-state-Game_nochecks-<$<!b!><!n!><!zeron!>$>-Fresh> gamestate-H3))
       (= (<pkg-state-Game-<$<!b!><!n!><!zeron!>$>-First> gamestate-H2)
          (<pkg-state-Game_nochecks-<$<!b!><!n!><!zeron!>$>-First> gamestate-H3))
       (= (<pkg-state-Game-<$<!b!><!n!><!zeron!>$>-Second> gamestate-H2)
          (<pkg-state-Game_nochecks-<$<!b!><!n!><!zeron!>$>-Second> gamestate-H3))
       (= (<pkg-state-Game-<$<!b!><!n!><!zeron!>$>-State> gamestate-H2)
          (<pkg-state-Game_nochecks-<$<!b!><!n!><!zeron!>$>-State> gamestate-H3))
       (= (<game-H2-<$<!n!><!b!><!true!><!zeron!>$>-pkgstate-Nonces>     state-kx)
          (<game-H3-<$<!n!><!b!><!true!><!zeron!>$>-pkgstate-Nonces> state-kxred))
       (= (<game-H2-<$<!n!><!b!><!true!><!zeron!>$>-pkgstate-CR>     state-kx)
          (<game-H3-<$<!n!><!b!><!true!><!zeron!>$>-pkgstate-CR> state-kxred))
	   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	   ;; Local Statement on MAC & PRF collision-freeness
	   (forall ((k1 Bits_256) (k2 Bits_256))
			   (let ((entry1 (select h2-prf k1))
					 (entry2 (select h2-prf k1)))
				 (=> (and (not (= entry1 (as mk-none (Maybe (Tuple6 Bits_256 Int Int Bits_256 Bits_256 Bool)))))
						  (not (= entry2 (as mk-none (Maybe (Tuple6 Bits_256 Int Int Bits_256 Bits_256 Bool))))))
					 (let ((ltk1  (el6-1 (maybe-get entry1)))
						   (ltk2  (el6-1 (maybe-get entry2)))
                           (U1    (el6-2 (maybe-get entry1)))
						   (U2    (el6-2 (maybe-get entry2)))
                           (V1    (el6-3 (maybe-get entry1)))
						   (V2    (el6-3 (maybe-get entry2)))
                           (ni1   (el6-4 (maybe-get entry1)))
						   (ni2   (el6-4 (maybe-get entry2)))
                           (nr1   (el6-5 (maybe-get entry1)))
						   (nr2   (el6-5 (maybe-get entry2)))
                           (flag1 (el6-6 (maybe-get entry1)))
						   (flag2 (el6-6 (maybe-get entry2))))
					   (=> (not (= k1 k2))
						   (not (= entry1 entry2)))))))
	   
       (forall ((k Bits_256))
               (and
                (let ((entry (select h2-mac k)))
                  (=> (not (= entry (as mk-none (Maybe (Tuple3 Bits_256 Bits_256 Int)))))
                      (let ((kmac  (el3-1 (maybe-get entry)))
                            (nonce (el3-2 (maybe-get entry)))
                            (label (el3-3 (maybe-get entry))))
                        (= k (<<func-mac>> kmac nonce label)))))
                (let ((entry (select h2-prf k)))
                  (=> (not (= entry (as mk-none (Maybe (Tuple6 Bits_256 Int Int Bits_256 Bits_256 Bool)))))
                      (let ((ltk (el6-1 (maybe-get entry)))
                            (U    (el6-2 (maybe-get entry)))
                            (V    (el6-3 (maybe-get entry)))
                            (ni   (el6-4 (maybe-get entry)))
                            (nr   (el6-5 (maybe-get entry)))
                            (flag (el6-6 (maybe-get entry))))
                        (= k (<<func-prf>> ltk U V ni nr flag)))))))

	   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	   ;; Local statement on single entries in the game state
       (forall ((ctr Int))
               (let ((state (select H2-state ctr)))
                 (=> (not (= state
                             (as mk-none (Maybe (Tuple11 Int Bool Int Bits_256 (Maybe Bool)
                                                         (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                                         (Maybe (Tuple5 Int Int (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)))
                                                         Int)))))
                     (let ((U    (el11-1  (maybe-get state)))
                           (u    (el11-2  (maybe-get state)))
                           (V    (el11-3  (maybe-get state)))
                           (ltk  (el11-4  (maybe-get state)))
                           (acc  (el11-5  (maybe-get state)))
                           (k    (el11-6  (maybe-get state)))
                           (ni   (el11-7  (maybe-get state)))
                           (nr   (el11-8  (maybe-get state)))
                           (kmac (el11-9  (maybe-get state)))
                           (sid  (el11-10 (maybe-get state)))
                           (mess (el11-11 (maybe-get state))))
                       (and
						;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
						;; For any side
                        (=> (not (= ni (as mk-none (Maybe Bits_256))))
                            (or u (= (select h2-nonces (maybe-get ni)) (mk-some true))))
                        (=> (not (= nr (as mk-none (Maybe Bits_256))))
                            (or (not u) (= (select h2-nonces (maybe-get nr)) (mk-some true))))
						(=> (not (= k (as mk-none (Maybe Bits_256))))
							(and (= k (mk-some (<<func-prf>> ltk V U        ; then k    has the right value.
                                                             (maybe-get ni)
                                                             (maybe-get nr)
                                                             true)))
                                 (= (select h2-prf (maybe-get k))           ; then PRF value k is also in PRF table (at correct position).
                                    (mk-some (mk-tuple6 ltk V U 
                                                        (maybe-get ni) 
                                                        (maybe-get nr) 
                                                        true)))))
						(=> (not (= kmac (as mk-none (Maybe Bits_256))))
							(and (= kmac (mk-some (<<func-prf>> ltk V U     ; then kmac has the right value.
                                                                (maybe-get ni)
                                                                (maybe-get nr)
                                                                false)))
                                 (= (select h2-prf (maybe-get kmac))        ; then PRF value kmac is also in PRF table (at correct position).
                                    (mk-some (mk-tuple6 ltk V U 
                                                        (maybe-get ni) 
                                                        (maybe-get nr) 
                                                        false)))))
						(=> (and (> mess 1) ; message large than 1
                                 (= acc (mk-some true))) ; accept = true
							(and ; (not (= ni (as mk-none (Maybe Bits_256))))
                             (not (= nr (as mk-none (Maybe Bits_256))))
                             (not (= kmac (as mk-none (Maybe Bits_256))))))
						;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
						;; Responder
						(=> u 
							(=> (> mess 0)
								(and (not (= ni (as mk-none (Maybe Bits_256)))) ; then ni is not none.
									 (not (= nr (as mk-none (Maybe Bits_256)))) ; then nr   is not none.
                                     (= sid (mk-some (mk-tuple5 V U ni nr       ; then sid  has the right value.
                                                                (mk-some (<<func-mac>> (maybe-get kmac)
                                                                                       (maybe-get nr)
                                                                                       2))))))))
						;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
						;; Initiator
                        (=> (not u)
							(=> (and (> mess 1)
									 (= acc (mk-some true)))
								(and (= sid (mk-some (mk-tuple5 U V ni nr           ; then sid  has the right value.
																(mk-some (<<func-mac>> (maybe-get kmac)
																					   (maybe-get nr)
																					   2)))))))))))))
	   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	   ;; Pairwise properties of game states
       (forall ((ctr1 Int) (ctr2 Int))
               (let ((state1 (select H2-state ctr1))
                     (state2 (select H2-state ctr2)))
                 (=> (and (not (= state1
                                  (as mk-none (Maybe (Tuple11 Int Bool Int Bits_256 (Maybe Bool)
                                                              (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                                              (Maybe (Tuple5 Int Int (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)))
                                                              Int)))))
                          (not (= state2
                                  (as mk-none (Maybe (Tuple11 Int Bool Int Bits_256 (Maybe Bool)
                                                              (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                                              (Maybe (Tuple5 Int Int (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)))
                                                              Int))))))
                     (let ((U1   (el11-1  (maybe-get (select H2-state ctr1))))
						   (U2   (el11-1  (maybe-get (select H2-state ctr2))))
						   (u1   (el11-2  (maybe-get (select H2-state ctr1))))
						   (u2   (el11-2  (maybe-get (select H2-state ctr2))))
						   (V1   (el11-3  (maybe-get (select H2-state ctr1))))
						   (V2   (el11-3  (maybe-get (select H2-state ctr2))))
						   (ltk1 (el11-4  (maybe-get (select H2-state ctr1))))
						   (ltk2 (el11-4  (maybe-get (select H2-state ctr2))))
						   (acc1 (el11-5  (maybe-get (select H2-state ctr1))))
                           (acc2 (el11-5  (maybe-get (select H2-state ctr2))))
                           (key1 (el11-6  (maybe-get (select H2-state ctr1))))
                           (key2 (el11-6  (maybe-get (select H2-state ctr2))))
                           (ni1  (el11-7  (maybe-get (select H2-state ctr1))))
                           (ni2  (el11-7  (maybe-get (select H2-state ctr2))))
                           (nr1  (el11-8  (maybe-get (select H2-state ctr1))))
                           (nr2  (el11-8  (maybe-get (select H2-state ctr2))))
                           (sid1 (el11-10 (maybe-get (select H2-state ctr1))))
                           (sid2 (el11-10 (maybe-get (select H2-state ctr2)))))
                       (and
						(let ((nonce1 (ite u1 nr1 ni1))
							  (nonce2 (ite u2 nr2 ni2)))
						  (=> (and (not (= ctr1 ctr2))
								   (not (= nonce1 (as mk-none (Maybe Bits_256)))))
							  (not (= nonce1 nonce2))))
						(=> (and (not (= key1 (as mk-none (Maybe Bits_256))))
								 (= key1 key2)
								 false)
							(and (= ni1 ni2) (= nr1 nr2)))
						(=> (and (= (mk-some true) acc1 acc2)
                                 (= sid1 sid2))
							(and (= ltk1 ltk2))))))))))))
