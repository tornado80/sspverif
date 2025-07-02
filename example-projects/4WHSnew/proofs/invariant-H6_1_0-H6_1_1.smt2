;; Main idea of this invariant proof
;; If ctr are equal in both games and they use the same randomness, then both games
;;    - produce the same output
;;    - abort iff the other aborts
;;    - have same ctr afterwards
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Randomness mapping
;;
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
   (= id-0      2)  ; This is the 2nd sampling in KX and samples ni.
   (= id-1      2)  ; This sampling happens in the Nonces package and is the 2nd sampling (in fact the last sampling, because Nonces is defined last).
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
   (= id-0 id-1)))

(define-fun randomness-mapping-Send3
    ( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
      (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
      (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
      (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
      (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
      (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
  ;; There is no randomness used in this oracle.
  (and
   (= scr-1 base-ctr-1)
   (= scr-0 base-ctr-0)
   (= id-0 id-1)))

(define-fun randomness-mapping-Send4
    ( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
      (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
      (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
      (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
      (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
      (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
  ;; There is no randomness used in this oracle.
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
  ;; There is no randomness used in this oracle.
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
  (and
   (= scr-1 base-ctr-1)
   (= scr-0 base-ctr-0)
   (= id-0 id-1)))


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
   (= scr-0 base-ctr-0)
   (= id-0 1)
   (= id-1 3)))

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
   (= id-0     0)   ; This is the 0th sampling in KX   and samples the random key in NewKey.
   (= id-1     0)   ; This is the 0th sampling in H1_0 and samples the random key in NewKey.
   ))

(define-fun randomness-mapping-NewSession
    ( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
      (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
      (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
      (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
      (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
      (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
  ;; There is no randomness used in this oracle.
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
  ;; There is no randomness used in this oracle.
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
  ;; There is no randomness used in this oracle.
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
  ;; There is no randomness used in this oracle.
  false
  )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                                                                                      ;
;; Invariant --- note that the invariant needs to be game-global and not per oracle,                    ;
;;               so that induction over the oracle calls remains meaningful.                            ;
;;                                                                                                      ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; For honest keys, before reveal the output key was never computed
;;
;; ie revtested = None -> no entry in the table
;;
(define-fun <relation-lemma-key-not-yet-computed-H6_1_0-H6_1_1-Reveal>
    ((H610-old <GameState_H6_<$<!n!><!false!><!true!><!zeron!>$>>)
     (H611-old <GameState_H6_<$<!n!><!true!><!true!><!zeron!>$>>)
     (H610-return <OracleReturn-H6-<$<!n!><!false!><!true!><!zeron!>$>-Game_noprfkey-<$<!b!><!n!><!zeron!>$>-Reveal>)
     (H611-return <OracleReturn-H6-<$<!n!><!true!><!true!><!zeron!>$>-Game_noprfkey-<$<!b!><!n!><!zeron!>$>-Reveal>)
     (ctr Int))
  Bool
  (let ((retval0 (<oracle-return-H6-<$<!n!><!false!><!true!><!zeron!>$>-Game_noprfkey-<$<!b!><!n!><!zeron!>$>-Reveal-return-value-or-abort> H610-return))
        (H610-new (<oracle-return-H6-<$<!n!><!false!><!true!><!zeron!>$>-Game_noprfkey-<$<!b!><!n!><!zeron!>$>-Reveal-game-state> H610-return))
        (nonces-H610 (<game-H6-<$<!n!><!false!><!true!><!zeron!>$>-pkgstate-Nonces> H610-old))
        (game-H610 (<game-H6-<$<!n!><!false!><!true!><!zeron!>$>-pkgstate-Game_noprfkey> H610-old))
        (prf-H610 (<game-H6-<$<!n!><!false!><!true!><!zeron!>$>-pkgstate-PRF> H610-old))
        (none (as mk-none (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                          (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                          (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int)))))
    (let ((State0 (<pkg-state-Game_noprfkey-<$<!b!><!n!><!zeron!>$>-State> game-H610))
          (RevTested0 (<pkg-state-Game_noprfkey-<$<!b!><!n!><!zeron!>$>-RevTested> game-H610))
          (Prf0 (<pkg-state-PRF-<$<!bprf!><!n!>$>-PRF> prf-H610)))
      (and
       (=> (not (= retval0 (as mk-abort (ReturnValue Bits_256))))
           (let ((state (select State0 ctr)))
             (and (not (= state none))
                  (let  ((U    (el11-1  (maybe-get state)))
                         (u    (el11-2  (maybe-get state)))
                         (V    (el11-3  (maybe-get state)))
                         (kid  (el11-4  (maybe-get state)))
                         (acc  (el11-5  (maybe-get state)))
                         (k    (el11-6  (maybe-get state)))
                         (ni   (el11-7  (maybe-get state)))
                         (nr   (el11-8  (maybe-get state)))
                         (kmac (el11-9  (maybe-get state)))
                         (sid  (el11-10 (maybe-get state)))
                         (mess (el11-11 (maybe-get state))))
                    (and (not (= sid (as mk-none (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)))))
                         (= (select RevTested0 (maybe-get sid))
                            (as mk-none (Maybe Bool))))))))))))




(define-fun prfeval-has-matching-session
    ((prf (Array (Tuple6 Int Int Int Bits_256 Bits_256 Bool) (Maybe Bits_256)))
     (revtesteval (Array (Tuple5 Int Int Int Bits_256 Bits_256) (Maybe Int)))
     (revtesteval1 (Array (Tuple5 Int Int Int Bits_256 Bits_256) (Maybe Int)))
     (revtest (Array (Tuple5 Int Int Bits_256 Bits_256 Bits_256) (Maybe Bool)))
     (state (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                       (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                       (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int))))
     )
  Bool
  (let ((none (as mk-none (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                          (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                          (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int)))))
    (forall ((kid Int) (U Int) (V Int) (ni Bits_256) (nr Bits_256))
            (let ((pos-prf (mk-tuple6 kid U V ni nr true))
                  (pos-rev (mk-tuple5 kid U V ni nr)))
              (and (=> (not (= (select prf pos-prf)
                          (as mk-none (Maybe Bits_256))))
                       (not (= (select revtesteval pos-rev)
                               (as mk-none (Maybe Int)))))
                   (=> (not (= (select revtesteval pos-rev)
                               (as mk-none (Maybe Int))))
                       (let ((ctr (maybe-get (select revtesteval pos-rev)))
                             (st (select state (maybe-get (select revtesteval pos-rev)))))
                         (and
                          (not (= st none))
                          (let  ((Up   (el11-1  (maybe-get st)))
                                 (u    (el11-2  (maybe-get st)))
                                 (Vp   (el11-3  (maybe-get st)))
                                 (kidp (el11-4  (maybe-get st)))
                                 (acc  (el11-5  (maybe-get st)))
                                 (k    (el11-6  (maybe-get st)))
                                 (nip  (el11-7  (maybe-get st)))
                                 (nrp  (el11-8  (maybe-get st)))
                                 (kmac (el11-9  (maybe-get st)))
                                 (sid  (el11-10 (maybe-get st)))
                                 (mess (el11-11 (maybe-get st))))
                            (and
                             (= acc (mk-some true))
                             (not (= sid (as mk-none (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)))))
                             (= ni (maybe-get nip))
                             (= nr (maybe-get nrp))
                             (= U (ite u Vp Up))
                             (= V (ite u Up Vp))
                             (= kid kidp)
                             (let ((tau (<<func-mac>> (maybe-get kmac) nr 2)))
                               (= (mk-tuple5 U V ni nr tau)
                                  (maybe-get sid)))
                             (not (= (select revtest (maybe-get sid))
                                     (as mk-none (Maybe Bool))))))))))))))


(define-fun sid-matches
    ((state (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                       (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                       (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int))))
     (prf (Array (Tuple6 Int Int Int Bits_256 Bits_256 Bool) (Maybe Bits_256))))
  Bool
  (let ((none (as mk-none (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                          (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                          (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int)))))
    (forall ((ctr1 Int) (ctr2 Int))
            (let ((state1 (select state ctr1))
                  (state2 (select state ctr2)))
            (=> (and (not (= none state1))
                     (not (= none state2)))
                (let ((U1    (el11-1 (maybe-get state1)))
                      (U2    (el11-1 (maybe-get state2)))
                      (u1    (el11-2 (maybe-get state1)))
                      (u2    (el11-2 (maybe-get state2)))
                      (V1    (el11-3 (maybe-get state1)))
                      (V2    (el11-3 (maybe-get state2)))
                      (kid1  (el11-4 (maybe-get state1)))
                      (kid2  (el11-4 (maybe-get state2)))
                      (ni1   (el11-7 (maybe-get state1)))
                      (ni2   (el11-7 (maybe-get state2)))
                      (nr1   (el11-8 (maybe-get state1)))
                      (nr2   (el11-8 (maybe-get state2)))
                      (kmac1 (el11-9 (maybe-get state1)))
                      (kmac2 (el11-9 (maybe-get state2)))
                      (sid1  (el11-10 (maybe-get state1)))
                      (sid2  (el11-10 (maybe-get state2))))
                  (=> (and (not (= sid1 (as mk-none (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)))))
                           (not (= sid2 (as mk-none (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)))))
                           (= (mk-tuple5 kid1 (ite u1 V1 U1) (ite u1 U1 V1) ni1 nr1)
                              (mk-tuple5 kid2 (ite u2 V2 U2) (ite u2 U2 V2) ni2 nr2)))
                      (and (not (= kmac1 (as mk-none (Maybe Bits_256))))
                           (not (= kmac2 (as mk-none (Maybe Bits_256))))
                           (= kmac1 kmac2)
                           (= sid1 sid2)))))))))


(define-fun sid-is-wellformed
    ((state (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                       (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                       (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int))))
     (prf (Array (Tuple6 Int Int Int Bits_256 Bits_256 Bool) (Maybe Bits_256))))
  Bool
  (let ((none (as mk-none (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                          (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                          (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int)))))
    (forall ((ctr Int))
            (let ((state (select state ctr)))
              (=> (not (= state none))
                  (let  ((U    (el11-1  (maybe-get state)))
                         (u    (el11-2  (maybe-get state)))
                         (V    (el11-3  (maybe-get state)))
                         (kid  (el11-4  (maybe-get state)))
                         (acc  (el11-5  (maybe-get state)))
                         (k    (el11-6  (maybe-get state)))
                         (ni   (el11-7  (maybe-get state)))
                         (nr   (el11-8  (maybe-get state)))
                         (kmac (el11-9  (maybe-get state)))
                         (sid  (el11-10 (maybe-get state)))
                         (mess (el11-11 (maybe-get state))))
                    (=> (not (= sid (as mk-none (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)))))
                        (let ((tau (<<func-mac>> (maybe-get kmac) (maybe-get nr) 2)))
                          (= (mk-tuple5 (ite u V U) (ite u U V)
                                        (maybe-get ni) (maybe-get nr) tau)
                             (maybe-get sid))))))))))


(define-fun key-not-computed-unless-test-or-reveal
    ((state (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                       (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                       (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int))))
     (revtest (Array (Tuple5 Int Int Bits_256 Bits_256 Bits_256) (Maybe Bool)))
     (prf (Array (Tuple6 Int Int Int Bits_256 Bits_256 Bool) (Maybe Bits_256)))
     (H (Array Int (Maybe Bool))))
  Bool
  (and
   ;; mac keys are computed before output keys
   (forall ((kid Int)
            (U Int)
            (V Int)
            (ni Bits_256)
            (nr Bits_256))
           (=> (not (= (select prf (mk-tuple6 kid U V ni nr true))
                       (as mk-none (Maybe Bits_256))))
               (not (= (select prf (mk-tuple6 kid U V ni nr false))
                       (as mk-none (Maybe Bits_256))))))

   ;; output keys are only computed when revtesting
   (forall ((kid Int)
            (U Int)
            (V Int)
            (ni Bits_256)
            (nr Bits_256)
            (kmac-prime Bits_256))
           (and
            ;; entry in PRF table => entry in revtest
            (=> (not (= (select prf (mk-tuple6 kid U V ni nr true))
                        (as mk-none (Maybe Bits_256))))
                (let ((kmac (select prf (mk-tuple6 kid U V ni nr false))))
                  (let ((tau (<<func-mac>> (maybe-get kmac) nr 2)))
                    (not (= (select revtest (mk-tuple5 U V ni nr tau))
                            (as mk-none (Maybe Bool)))))))

            ;; revtest none => prf none
            (=> (let ((tau (<<func-mac>> kmac-prime nr 2)))
                  (= (select revtest (mk-tuple5 U V ni nr tau))
                     (as mk-none (Maybe Bool))))
                (=> (= (select prf (mk-tuple6 kid U V ni nr false))
                       (mk-some kmac-prime))
                    (= (select prf (mk-tuple6 kid U V ni nr true))
                       (as mk-none (Maybe Bits_256)))))))))



;; Some consistency checks on the PRF package
;;
;; (i) LTK and H are written at the same locations
;; (ii) neither is written on larger indices than kid
;;
(define-fun no-overwriting-prf ((prf <PackageState_PRF_<$<!bprf!><!n!>$>>))
  Bool
  (let ((kid (<pkg-state-PRF-<$<!bprf!><!n!>$>-kid_> prf))
        (LTK (<pkg-state-PRF-<$<!bprf!><!n!>$>-LTK> prf))
        (H (<pkg-state-PRF-<$<!bprf!><!n!>$>-H> prf)))
    (forall ((i Int))
            (and
             (=> (= (select H i) (as mk-none (Maybe Bool)))
                 (= (select LTK i) (as mk-none (Maybe Bits_256))))
             (=> (= (select LTK i) (as mk-none (Maybe Bits_256)))
                 (= (select H i) (as mk-none (Maybe Bool))))
             (=> (> i kid)
                 (and (= (select H i)
                         (as mk-none (Maybe Bool)))
                      (= (select LTK i)
                         (as mk-none (Maybe Bits_256)))))))))

(define-fun no-overwriting-game
    ((state (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                       (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                       (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int))))
     (ctr Int))
  Bool
  (forall ((i Int))
          (=> (> i ctr)
              (= (select state i)
                 (as mk-none (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                             (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                             (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int)))))))



(define-fun mac-keys-equal-in-prf
    ((prf0 (Array (Tuple6 Int Int Int Bits_256 Bits_256 Bool) (Maybe Bits_256)))
     (prf1 (Array (Tuple6 Int Int Int Bits_256 Bits_256 Bool) (Maybe Bits_256))))
  Bool
  (forall ((in (Tuple6 Int Int Int Bits_256 Bits_256 Bool)))
          (=> (= false (el6-6 in))
              (= (select prf0 in)
                 (select prf1 in)))))


(define-fun kmac-and-tau-are-computed-correctly
    ((state (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                       (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                       (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int))))
     (prf (Array (Tuple6 Int Int Int Bits_256 Bits_256 Bool) (Maybe Bits_256)))
     (honesty (Array Int (Maybe Bool)))
     (ltk (Array Int (Maybe Bits_256))))
  Bool
  (let ((none (as mk-none (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                          (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                          (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int)))))
    (forall ((ctr Int))
            (let ((state (select state ctr)))
              (=> (not (= state none))
                  (let  ((U    (el11-1  (maybe-get state)))
                         (u    (el11-2  (maybe-get state)))
                         (V    (el11-3  (maybe-get state)))
                         (kid  (el11-4  (maybe-get state)))
                         (acc  (el11-5  (maybe-get state)))
                         (k    (el11-6  (maybe-get state)))
                         (ni   (el11-7  (maybe-get state)))
                         (nr   (el11-8  (maybe-get state)))
                         (kmac (el11-9  (maybe-get state)))
                         (sid  (el11-10 (maybe-get state)))
                         (mess (el11-11 (maybe-get state))))
                    (and
                     (not (= (select ltk kid) (as mk-none (Maybe Bits_256))))
                     (not (= (select honesty kid) (as mk-none (Maybe Bool))))
                     (=> (and (not (= kmac (as mk-none (Maybe Bits_256))))
                              (= (select honesty kid) (mk-some false)))
                         (= kmac (mk-some (<<func-prf>> (maybe-get (select ltk kid)) (ite u V U) (ite u U V)
                                                        (maybe-get ni) (maybe-get nr) false))))
                     (=> (and (not (= kmac (as mk-none (Maybe Bits_256))))
                              (= (select honesty kid) (mk-some true)))
                         (= kmac (select prf (mk-tuple6 kid (ite u V U) (ite u U V)
                                                        (maybe-get ni) (maybe-get nr) false)))))))))))


(define-fun stuff-not-initialized-early
    ((state (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                       (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                       (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int)))))
  Bool
  (let ((none (as mk-none (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                          (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                          (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int)))))
    (forall ((ctr Int))
            (let ((state (select state ctr)))
              (=> (not (= state none))
                  (let  ((U    (el11-1  (maybe-get state)))
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
                    (and (ite u
                              (ite (> mess 0)
                                   (and (not (= sid (as mk-none (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)))))
                                        (not (= kmac (as mk-none (Maybe Bits_256))))
                                        (not (= ni (as mk-none (Maybe Bits_256))))
                                        (not (= nr (as mk-none (Maybe Bits_256)))))
                                   (and (= sid (as mk-none (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256))))
                                        (= ni nr kmac (as mk-none (Maybe Bits_256)))))
                              (ite (= mess 0)
                                   (and (= sid (as mk-none (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256))))
                                        (= ni nr kmac (as mk-none (Maybe Bits_256))))
                                   (ite (= mess 1)
                                        (and (not (= ni (as mk-none (Maybe Bits_256))))
                                             (= nr kmac (as mk-none (Maybe Bits_256)))
                                             (= sid (as mk-none (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)))))
                                        (and (not (= sid (as mk-none (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)))))
                                             (not (= kmac (as mk-none (Maybe Bits_256))))
                                             (not (= ni (as mk-none (Maybe Bits_256))))
                                             (not (= nr (as mk-none (Maybe Bits_256)))))))))))))))



(define-fun own-nonce-is-unique
    ((state (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                       (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                       (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int))))
     (nonces (Array Bits_256 (Maybe Bool))))
  Bool
  (let ((none (as mk-none (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                          (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                          (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int)))))
    (and
     (forall ((ctr Int))
             (let ((state (select state ctr)))
               (=> (not (= state none))
                   (let  ((U    (el11-1  (maybe-get state)))
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
                     (ite u
                          (=> (not (= nr (as mk-none (Maybe Bits_256))))
                              (= (select nonces (maybe-get nr)) (mk-some true)))
                          (=> (not (= ni (as mk-none (Maybe Bits_256))))
                              (= (select nonces (maybe-get ni)) (mk-some true))))))))

     (forall ((ctr1 Int)(ctr2 Int))
             (let ((state1 (select state ctr1))
                   (state2 (select state ctr2)))
               (=> (and (not (= none state1))
                        (not (= none state2)))
                   (let ((u1    (el11-2 (maybe-get state1)))
                         (u2    (el11-2 (maybe-get state2)))
                         (ni1   (el11-7 (maybe-get state1)))
                         (ni2   (el11-7 (maybe-get state2)))
                         (nr1   (el11-8 (maybe-get state1)))
                         (nr2   (el11-8 (maybe-get state2))))
                     (and
                      (let ((nonce1 (ite u1 nr1 ni1))
                            (nonce2 (ite u2 nr2 ni2)))
                        (=> (and (not (= ctr1 ctr2))
                                 (not (= nonce1 (as mk-none (Maybe Bits_256)))))
                            (not (= nonce1 nonce2))))))))))))


(define-fun revtesteval-populated
    ((revtesteval (Array (Tuple5 Int Int Int Bits_256 Bits_256) (Maybe Int)))
     (H (Array Int (Maybe Bool)))
     (prf (Array (Tuple6 Int Int Int Bits_256 Bits_256 Bool) (Maybe Bits_256))))
  Bool
  (forall ((kid Int) (U Int) (V Int) (ni Bits_256) (nr Bits_256))
          (let ((pos-prf (mk-tuple6 kid U V ni nr true))
                (pos-rev (mk-tuple5 kid U V ni nr)))
            (and
             (=> (= (select prf pos-prf)
                    (as mk-none (Maybe Bits_256)))
                 (or (= (select H kid) (mk-some false))
                     (= (select revtesteval pos-rev)
                        (as mk-none (Maybe Int)))))
             (=> (= (select revtesteval pos-rev)
                    (as mk-none (Maybe Int)))
                 (= (select prf pos-prf)
                    (as mk-none (Maybe Bits_256))))))))


(define-fun revtesteval-matches-sometimes
    ((state (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                       (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                       (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int))))
     (revtesteval0 (Array (Tuple5 Int Int Int Bits_256 Bits_256) (Maybe Int)))
     (revtesteval1 (Array (Tuple5 Int Int Int Bits_256 Bits_256) (Maybe Int)))
     (revtest (Array (Tuple5 Int Int Bits_256 Bits_256 Bits_256) (Maybe Bool))))
  Bool
   (let ((none (as mk-none (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                           (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                           (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int)))))
     (and
      (forall ((kid Int) (U Int) (V Int) (ni Bits_256) (nr Bits_256))
              (=> (not (= (select revtesteval1 (mk-tuple5 kid U V ni nr))
                          (as mk-none (Maybe Int))))
                  (= (select revtesteval1 (mk-tuple5 kid U V ni nr))
                     (select revtesteval0 (mk-tuple5 kid U V ni nr))))))))



(define-fun freshness-and-honesty-matches
    ((state (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                       (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                       (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int))))
     (fresh (Array Int (Maybe Bool)))
     (honest (Array Int (Maybe Bool))))
  Bool
  (let ((none (as mk-none (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                          (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                          (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int)))))
    (forall ((ctr Int))
            (let ((state (select state ctr)))
              (=> (not (= state none))
                  (let ((kid (el11-4  (maybe-get state))))
                    (= (select fresh ctr)
                       (select honest kid))))))))


(define-fun invariant
    ((state-H610  <GameState_H6_<$<!n!><!false!><!true!><!zeron!>$>>)
     (state-H611  <GameState_H6_<$<!n!><!true!><!true!><!zeron!>$>>))
  Bool
  (let ((nonces-H610 (<game-H6-<$<!n!><!false!><!true!><!zeron!>$>-pkgstate-Nonces> state-H610))
        (nonces-H611 (<game-H6-<$<!n!><!true!><!true!><!zeron!>$>-pkgstate-Nonces>  state-H611))
        (game-H610 (<game-H6-<$<!n!><!false!><!true!><!zeron!>$>-pkgstate-Game_noprfkey> state-H610))
        (game-H611 (<game-H6-<$<!n!><!true!><!true!><!zeron!>$>-pkgstate-Game_noprfkey>  state-H611))
        (prf-H610 (<game-H6-<$<!n!><!false!><!true!><!zeron!>$>-pkgstate-PRF> state-H610))
        (prf-H611 (<game-H6-<$<!n!><!true!><!true!><!zeron!>$>-pkgstate-PRF>  state-H611)))
    (let ((ctr0 (<pkg-state-Game_noprfkey-<$<!b!><!n!><!zeron!>$>-ctr_> game-H610))
          (ctr1 (<pkg-state-Game_noprfkey-<$<!b!><!n!><!zeron!>$>-ctr_> game-H611))
          (State0 (<pkg-state-Game_noprfkey-<$<!b!><!n!><!zeron!>$>-State> game-H610))
          (State1 (<pkg-state-Game_noprfkey-<$<!b!><!n!><!zeron!>$>-State> game-H611))
          (RevTested0 (<pkg-state-Game_noprfkey-<$<!b!><!n!><!zeron!>$>-RevTested> game-H610))
          (RevTested1 (<pkg-state-Game_noprfkey-<$<!b!><!n!><!zeron!>$>-RevTested> game-H611))
          (RevTestEval0 (<pkg-state-Game_noprfkey-<$<!b!><!n!><!zeron!>$>-RevTestEval> game-H610))
          (RevTestEval1 (<pkg-state-Game_noprfkey-<$<!b!><!n!><!zeron!>$>-RevTestEval> game-H611))
          (Fresh0 (<pkg-state-Game_noprfkey-<$<!b!><!n!><!zeron!>$>-Fresh> game-H610))
          (Fresh1 (<pkg-state-Game_noprfkey-<$<!b!><!n!><!zeron!>$>-Fresh> game-H611))
          (Nonces0 (<pkg-state-Nonces-<$<!true!><!n!>$>-Nonces> nonces-H610))
          (Nonces1 (<pkg-state-Nonces-<$<!true!><!n!>$>-Nonces> nonces-H611))
          (Ltk0 (<pkg-state-PRF-<$<!bprf!><!n!>$>-LTK> prf-H610))
          (Ltk1 (<pkg-state-PRF-<$<!bprf!><!n!>$>-LTK> prf-H611))
          (Prf0 (<pkg-state-PRF-<$<!bprf!><!n!>$>-PRF> prf-H610))
          (Prf1 (<pkg-state-PRF-<$<!bprf!><!n!>$>-PRF> prf-H611))
          (H0 (<pkg-state-PRF-<$<!bprf!><!n!>$>-H> prf-H610))
          (H1 (<pkg-state-PRF-<$<!bprf!><!n!>$>-H> prf-H611)))
      (and (= nonces-H610 nonces-H611)
           (= Ltk0 Ltk1)
           (= H0 H1)
           (= (<pkg-state-PRF-<$<!bprf!><!n!>$>-kid_> prf-H610)
              (<pkg-state-PRF-<$<!bprf!><!n!>$>-kid_> prf-H611))
           (= ctr0 ctr1)
           (= State0 State1)
           (= RevTested0 RevTested1)
           (= Fresh0 Fresh1)

           (freshness-and-honesty-matches State0 Fresh0 H0)
           (revtesteval-matches-sometimes State0 RevTestEval0 RevTestEval1 RevTested0)
           (no-overwriting-prf prf-H610)
           (no-overwriting-game State0 ctr0)
           (sid-is-wellformed State0 Prf0)
           (sid-matches State0 Prf0)
           (own-nonce-is-unique State0 Nonces0)
           (revtesteval-populated RevTestEval0 H0 Prf0)
           (revtesteval-populated RevTestEval1 H1 Prf1)
           (prfeval-has-matching-session Prf0 RevTestEval0 RevTestEval1 RevTested0 State0)
           (key-not-computed-unless-test-or-reveal State0 RevTested0 Prf0 H0)
           (mac-keys-equal-in-prf Prf0 Prf1)
           (kmac-and-tau-are-computed-correctly State0 Prf0 H0 Ltk0)
           (kmac-and-tau-are-computed-correctly State1 Prf1 H1 Ltk1)
           (stuff-not-initialized-early State0)
           ))))


(define-fun prf-table-empty
    ((state0 (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                       (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                       (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int))))
     (revtesteval0 (Array (Tuple5 Int Int Int Bits_256 Bits_256) (Maybe Int)))
     (revtested0 (Array (Tuple5 Int Int Bits_256 Bits_256 Bits_256) (Maybe Bool)))
     (prf0 (Array (Tuple6 Int Int Int Bits_256 Bits_256 Bool) (Maybe Bits_256)))
     (ctr Int))
  Bool
  (let ((none (as mk-none (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                          (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                          (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int)))))
    (let ((state (select state0 ctr)))
      (and (not (= state none))
           (let  ((U    (el11-1  (maybe-get state)))
                  (u    (el11-2  (maybe-get state)))
                  (V    (el11-3  (maybe-get state)))
                  (kid  (el11-4  (maybe-get state)))
                  (acc  (el11-5  (maybe-get state)))
                  (k    (el11-6  (maybe-get state)))
                  (ni   (el11-7  (maybe-get state)))
                  (nr   (el11-8  (maybe-get state)))
                  (kmac (el11-9  (maybe-get state)))
                  (sid  (el11-10 (maybe-get state)))
                  (mess (el11-11 (maybe-get state))))
             (and (not (= sid (as mk-none (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)))))
                  (= (select revtested0 (maybe-get sid)) (as mk-none (Maybe Bool)))
                  (= (select revtesteval0 (mk-tuple5 kid (ite u V U) (ite u U V)
                                                     (maybe-get ni) (maybe-get nr)))
                     (as mk-none (Maybe Int)))
                  (= (select prf0 (mk-tuple6 kid (ite u V U) (ite u U V)
                                             (maybe-get ni) (maybe-get nr) true))
                     (as mk-none (Maybe Bits_256)))
                  ))))))


(define-fun <relation-lemma-debug-H6_1_0-H6_1_1-Test>
    ((H610-old <GameState_H6_<$<!n!><!false!><!true!><!zeron!>$>>)
     (H611-old <GameState_H6_<$<!n!><!true!><!true!><!zeron!>$>>)
     (H610-return <OracleReturn-H6-<$<!n!><!false!><!true!><!zeron!>$>-Game_noprfkey-<$<!b!><!n!><!zeron!>$>-Test>)
     (H611-return <OracleReturn-H6-<$<!n!><!true!><!true!><!zeron!>$>-Game_noprfkey-<$<!b!><!n!><!zeron!>$>-Test>)
     (ctr Int))
  Bool
  (let ((state-H610 (<oracle-return-H6-<$<!n!><!false!><!true!><!zeron!>$>-Game_noprfkey-<$<!b!><!n!><!zeron!>$>-Test-game-state> H610-return))
        (state-H611 (<oracle-return-H6-<$<!n!><!true!><!true!><!zeron!>$>-Game_noprfkey-<$<!b!><!n!><!zeron!>$>-Test-game-state> H611-return))
        (retval0 (<oracle-return-H6-<$<!n!><!false!><!true!><!zeron!>$>-Game_noprfkey-<$<!b!><!n!><!zeron!>$>-Test-return-value-or-abort> H610-return))
        (retval1 (<oracle-return-H6-<$<!n!><!true!><!true!><!zeron!>$>-Game_noprfkey-<$<!b!><!n!><!zeron!>$>-Test-return-value-or-abort> H611-return)))
    (let ((nonces-H610 (<game-H6-<$<!n!><!false!><!true!><!zeron!>$>-pkgstate-Nonces> state-H610))
          (nonces-H611 (<game-H6-<$<!n!><!true!><!true!><!zeron!>$>-pkgstate-Nonces>  state-H611))
          (game-H610 (<game-H6-<$<!n!><!false!><!true!><!zeron!>$>-pkgstate-Game_noprfkey> state-H610))
          (game-H610-old (<game-H6-<$<!n!><!false!><!true!><!zeron!>$>-pkgstate-Game_noprfkey> H610-old))
          (game-H611 (<game-H6-<$<!n!><!true!><!true!><!zeron!>$>-pkgstate-Game_noprfkey>  state-H611))
          (game-H611-old (<game-H6-<$<!n!><!true!><!true!><!zeron!>$>-pkgstate-Game_noprfkey>  H611-old))
          (prf-H610 (<game-H6-<$<!n!><!false!><!true!><!zeron!>$>-pkgstate-PRF> state-H610))
          (prf-H610-old (<game-H6-<$<!n!><!false!><!true!><!zeron!>$>-pkgstate-PRF> H610-old))
          (prf-H611 (<game-H6-<$<!n!><!true!><!true!><!zeron!>$>-pkgstate-PRF>  state-H611)))
      (let ((ctr0 (<pkg-state-Game_noprfkey-<$<!b!><!n!><!zeron!>$>-ctr_> game-H610))
            (ctr1 (<pkg-state-Game_noprfkey-<$<!b!><!n!><!zeron!>$>-ctr_> game-H611))
            (State0 (<pkg-state-Game_noprfkey-<$<!b!><!n!><!zeron!>$>-State> game-H610))
            (State1 (<pkg-state-Game_noprfkey-<$<!b!><!n!><!zeron!>$>-State> game-H611))
            (RevTested0 (<pkg-state-Game_noprfkey-<$<!b!><!n!><!zeron!>$>-RevTested> game-H610))
            (RevTested0-old (<pkg-state-Game_noprfkey-<$<!b!><!n!><!zeron!>$>-RevTested> game-H610-old))
            (RevTested1 (<pkg-state-Game_noprfkey-<$<!b!><!n!><!zeron!>$>-RevTested> game-H611))
            (RevTestEval0 (<pkg-state-Game_noprfkey-<$<!b!><!n!><!zeron!>$>-RevTestEval> game-H610))
            (RevTestEval0-old (<pkg-state-Game_noprfkey-<$<!b!><!n!><!zeron!>$>-RevTestEval> game-H610-old))
            (RevTestEval1 (<pkg-state-Game_noprfkey-<$<!b!><!n!><!zeron!>$>-RevTestEval> game-H611))
            (RevTestEval1-old (<pkg-state-Game_noprfkey-<$<!b!><!n!><!zeron!>$>-RevTestEval> game-H611-old))
            (Fresh0 (<pkg-state-Game_noprfkey-<$<!b!><!n!><!zeron!>$>-Fresh> game-H610))
            (Fresh1 (<pkg-state-Game_noprfkey-<$<!b!><!n!><!zeron!>$>-Fresh> game-H611))
            (Nonces0 (<pkg-state-Nonces-<$<!true!><!n!>$>-Nonces> nonces-H610))
            (Nonces1 (<pkg-state-Nonces-<$<!true!><!n!>$>-Nonces> nonces-H611))
            (Ltk0 (<pkg-state-PRF-<$<!bprf!><!n!>$>-LTK> prf-H610))
            (Ltk1 (<pkg-state-PRF-<$<!bprf!><!n!>$>-LTK> prf-H611))
            (Prf0 (<pkg-state-PRF-<$<!bprf!><!n!>$>-PRF> prf-H610))
            (Prf0-old (<pkg-state-PRF-<$<!bprf!><!n!>$>-PRF> prf-H610-old))
            (Prf1 (<pkg-state-PRF-<$<!bprf!><!n!>$>-PRF> prf-H611))
            (H0 (<pkg-state-PRF-<$<!bprf!><!n!>$>-H> prf-H610))
            (H1 (<pkg-state-PRF-<$<!bprf!><!n!>$>-H> prf-H611)))
        (and (= nonces-H610 nonces-H611)
             (= Ltk0 Ltk1)
             (= H0 H1)
             (= (<pkg-state-PRF-<$<!bprf!><!n!>$>-kid_> prf-H610)
                (<pkg-state-PRF-<$<!bprf!><!n!>$>-kid_> prf-H611))
             (= ctr0 ctr1)
             (= State0 State1)
             (= RevTested0 RevTested1)
             ;;(= RevTestEval0 RevTestEval1)
             (= Fresh0 Fresh1)

             (= RevTestEval1 RevTestEval1-old)
             (let ((sid (maybe-get (el11-10 (maybe-get (select State0 ctr))))))
               (= (select RevTested0 sid) (mk-some true)))

             (prf-table-empty State0 RevTestEval0-old RevTested0-old Prf0-old ctr)

             ;;(revtesteval-matches-sometimes State0 RevTestEval0 RevTestEval1 RevTested0)
             (no-overwriting-prf prf-H610)
             (no-overwriting-game State0 ctr0)
             (sid-is-wellformed State0 Prf0)
             (sid-matches State0 Prf0)
             (own-nonce-is-unique State0 Nonces0)
             (revtesteval-populated RevTestEval0 H0 Prf0)
             (revtesteval-populated RevTestEval1 H1 Prf1)
             (prfeval-has-matching-session Prf0 RevTestEval0 RevTestEval1 RevTested0 State0)
             (key-not-computed-unless-test-or-reveal State0 RevTested0 Prf0 H0)
             (mac-keys-equal-in-prf Prf0 Prf1)
             (kmac-and-tau-are-computed-correctly State0 Prf0 H0 Ltk0)
             (kmac-and-tau-are-computed-correctly State1 Prf1 H1 Ltk1)
             (stuff-not-initialized-early State0)
             )))))
