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
                  (as mk-none (Maybe (Tuple12 Int Bool Int Bool Bits_256 (Maybe Bool)
                                              (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                              (Maybe (Tuple5 Int Int (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)))
                                              Int)))))
             (= (el12-12 (maybe-get (select H2-state-new ctr))) 2))))))


(define-fun invariant
  ( (state-kx     <GameState_H2_<$<!n!><!b!><!true!><!zeron!>$>>)
    (state-kxred  <GameState_H3_<$<!n!><!b!><!true!><!zeron!>$>>))
  Bool
(let ((gamestate-H2 (<game-H2-<$<!n!><!b!><!true!><!zeron!>$>-pkgstate-Game>     state-kx))
      (gamestate-H3 (<game-H3-<$<!n!><!b!><!true!><!zeron!>$>-pkgstate-Game_nochecks> state-kxred)))
  (let ((H2-state (<pkg-state-Game-<$<!b!><!n!><!zeron!>$>-State> gamestate-H2))
        (H3-state (<pkg-state-Game_nochecks-<$<!b!><!n!><!zeron!>$>-State> gamestate-H3)))
    (and (= (<pkg-state-Game-<$<!b!><!n!><!zeron!>$>-LTK> gamestate-H2)
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
         
        (forall ((ctr Int))
          (=> (not (= (select H2-state ctr)
                      (as mk-none (Maybe (Tuple12 Int Bool Int Bool Bits_256 (Maybe Bool)
                                                  (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                                  (Maybe (Tuple5 Int Int (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)))
                                                  Int)))))
              (and (not (= (el12-2 (maybe-get (select H2-state ctr))) ; sender
                           (el12-4 (maybe-get (select H2-state ctr))))) ; receiver (or the other way around)
				   (=> (> (el12-12 (maybe-get (select H2-state ctr))) 0) ; message larger than 0
				       (and (=> (el12-2 (maybe-get (select H2-state ctr))) ; u is true
					            (not (= (el12-8 (maybe-get (select H2-state ctr))) ; ni not none
						                (as mk-none (Maybe Bits_256)))))
							(=> (el12-4 (maybe-get (select H2-state ctr))) ; v is true
					            (not (= (el12-9 (maybe-get (select H2-state ctr))) ; nr not none
						                (as mk-none (Maybe Bits_256)))))))
				   (=> (> (el12-12 (maybe-get (select H2-state ctr))) 1) ; message large than 1
				       (and (not (= (el12-8 (maybe-get (select H2-state ctr))) ; ni set
					                (as mk-none (Maybe Bits_256))))
							(not (= (el12-9 (maybe-get (select H2-state ctr))) ; nr set
					                (as mk-none (Maybe Bits_256))))
					        (= (el12-7 (maybe-get (select H2-state ctr))) ; key is Some(prf(...)
					           (mk-some (<<func-prf>> (el12-5 (maybe-get (select H2-state ctr)))
						                              (el12-1 (maybe-get (select H2-state ctr)))
						                              (el12-3 (maybe-get (select H2-state ctr)))
													  (maybe-get (el12-8 (maybe-get (select H2-state ctr))))
													  (maybe-get (el12-8 (maybe-get (select H2-state ctr))))
													  false))))))))
        (forall ((ctr1 Int) (ctr2 Int))
           (=> (and (not (= (select H2-state ctr1)
                            (as mk-none (Maybe (Tuple12 Int Bool Int Bool Bits_256 (Maybe Bool)
                                                        (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                                        (Maybe (Tuple5 Int Int (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)))
                                                        Int)))))
                    (not (= (select H2-state ctr2)
                            (as mk-none (Maybe (Tuple12 Int Bool Int Bool Bits_256 (Maybe Bool)
                                                        (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                                        (Maybe (Tuple5 Int Int (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)))
                                                        Int))))))
				(=> (and (= (mk-some true)
							(el12-6 (maybe-get (select H2-state ctr1))) ; accepted
							(el12-6 (maybe-get (select H2-state ctr2))))
						 (= (el12-11 (maybe-get (select H2-state ctr1))) ; sid
						    (el12-11 (maybe-get (select H2-state ctr2)))))
					(= (el12-7 (maybe-get (select H2-state ctr1))) ; then key
					   (el12-7 (maybe-get (select H2-state ctr2)))))))))))



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

