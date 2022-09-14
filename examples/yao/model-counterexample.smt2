; hhh
  (define-fun hhh () Int 109)
; j
  (define-fun j () Int 109)
; The new bottom-left table has a bad shape (at position 109)
  (define-fun debug-bottom-left () Bool false)
; old bottom-left table
  (define-fun table-bottom-left-old () (Array Int (Maybe (Array Bool (Maybe Bits_n))))
    (_ as-array k!26712))
; new bottom-left table
  (define-fun table-bottom-left-new () (Array Int (Maybe (Array Bool (Maybe Bits_n))))
    (_ as-array k!26707))

; before in k!26712
(ite (= x!0 109) (as mk-none (Maybe (Array Bool (Maybe Bits_n))))

; after in k!26707
    (ite (= x!0 109)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (as mk-none (Maybe Bits_n))) ;Das ist ein store, was auf einem all-bot table gecallt wird?
                      false                          ;Warum schreibt er nur bei false etwas hin?
                      (mk-some Bits_n!val!0)))

;sampled on the right
  (define-fun Z-right () (Array Bool (Maybe Bits_n))
    (store (store ((as const (Array Bool (Maybe Bits_n))) (mk-some Bits_n!val!64))
              false
              (mk-some Bits_n!val!0))
       true
       (mk-some Bits_n!val!11)))

;sampled on the left
  (define-fun Z-left () (Array Bool (Maybe Bits_n))
    (store (store ((as const (Array Bool (Maybe Bits_n))) (mk-some Bits_n!val!67))
              false
              (as mk-none (Maybe Bits_n)))
       true
       (mk-some Bits_n!val!11)))

    
      (define-fun r-left () Bits_n
    Bits_n!val!11)
    
      (define-fun r-right () Bits_n
    Bits_n!val!11)

  (define-fun rr-right () Bits_n
    Bits_n!val!0)

      (define-fun rr-left () Bits_n
    Bits_n!val!0)

; 
 (define-fun k!26712 ((x!0 Int)) (Maybe (Array Bool (Maybe Bits_n)))
    (ite (= x!0 104)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!34))
                               false
                               (mk-some Bits_n!val!21))
                        true
                        (mk-some Bits_n!val!57))))
        (mk-some a!1))
    (ite (= x!0 125)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!33))
                      false
                      (mk-some Bits_n!val!30)))
    (ite (= x!0 103)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!27))
                               false
                               (mk-some Bits_n!val!22))
                        true
                        (mk-some Bits_n!val!58))))
        (mk-some a!1))
    (ite (= x!0 109) (as mk-none (Maybe (Array Bool (Maybe Bits_n))))
    (ite (= x!0 114)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!41))
                      false
                      (mk-some Bits_n!val!54)))
    (ite (= x!0 105)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!43))
                      false
                      (mk-some Bits_n!val!51)))
    (ite (= x!0 106)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!44))
                               false
                               (mk-some Bits_n!val!53))
                        true
                        (mk-some Bits_n!val!56))))
        (mk-some a!1))
    (ite (= x!0 112)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!39))
                      false
                      (mk-some Bits_n!val!63)))
    (ite (= x!0 107)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!48))
                      false
                      (mk-some Bits_n!val!55)))
      (mk-some ((as const (Array Bool (Maybe Bits_n))) (mk-some Bits_n!val!66)))))))))))))
 

  (define-fun k!26707 ((x!0 Int)) (Maybe (Array Bool (Maybe Bits_n)))
    (ite (= x!0 104)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!34))
                               false
                               (mk-some Bits_n!val!21))
                        true
                        (mk-some Bits_n!val!57))))
        (mk-some a!1))
    (ite (= x!0 103)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!27))
                               false
                               (mk-some Bits_n!val!22))
                        true
                        (mk-some Bits_n!val!58))))
        (mk-some a!1))
    (ite (= x!0 125)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!33))
                      false
                      (mk-some Bits_n!val!30)))
    (ite (= x!0 109)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (as mk-none (Maybe Bits_n)))
                      false
                      (mk-some Bits_n!val!0)))
    (ite (= x!0 114)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!41))
                      false
                      (mk-some Bits_n!val!54)))
    (ite (= x!0 105)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!43))
                      false
                      (mk-some Bits_n!val!51)))
    (ite (= x!0 106)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!44))
                               false
                               (mk-some Bits_n!val!53))
                        true
                        (mk-some Bits_n!val!56))))
        (mk-some a!1))
    (ite (= x!0 112)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!39))
                      false
                      (mk-some Bits_n!val!63)))
    (ite (= x!0 107)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!48))
                      false
                      (mk-some Bits_n!val!55)))
      (mk-some ((as const (Array Bool (Maybe Bits_n))) (mk-some Bits_n!val!66)))))))))))))


(
  ;; universe for Bits_n:
  ;;   Bits_n!val!47 Bits_n!val!38 Bits_n!val!65 Bits_n!val!25 Bits_n!val!3 Bits_n!val!15 Bits_n!val!39 Bits_n!val!66 Bits_n!val!24 Bits_n!val!11 Bits_n!val!41 Bits_n!val!29 Bits_n!val!53 Bits_n!val!46 Bits_n!val!31 Bits_n!val!28 Bits_n!val!1 Bits_n!val!33 Bits_n!val!51 Bits_n!val!10 Bits_n!val!61 Bits_n!val!22 Bits_n!val!35 Bits_n!val!0 Bits_n!val!27 Bits_n!val!20 Bits_n!val!5 Bits_n!val!9 Bits_n!val!4 Bits_n!val!13 Bits_n!val!32 Bits_n!val!7 Bits_n!val!40 Bits_n!val!26 Bits_n!val!50 Bits_n!val!57 Bits_n!val!17 Bits_n!val!34 Bits_n!val!37 Bits_n!val!19 Bits_n!val!59 Bits_n!val!64 Bits_n!val!30 Bits_n!val!54 Bits_n!val!56 Bits_n!val!49 Bits_n!val!14 Bits_n!val!43 Bits_n!val!36 Bits_n!val!12 Bits_n!val!23 Bits_n!val!45 Bits_n!val!48 Bits_n!val!58 Bits_n!val!63 Bits_n!val!6 Bits_n!val!52 Bits_n!val!55 Bits_n!val!44 Bits_n!val!67 Bits_n!val!16 Bits_n!val!18 Bits_n!val!60 Bits_n!val!21 Bits_n!val!42 Bits_n!val!8 Bits_n!val!2 Bits_n!val!62 
  ;; -----------
  ;; definitions for universe elements:
  (declare-fun Bits_n!val!47 () Bits_n)
  (declare-fun Bits_n!val!38 () Bits_n)
  (declare-fun Bits_n!val!65 () Bits_n)
  (declare-fun Bits_n!val!25 () Bits_n)
  (declare-fun Bits_n!val!3 () Bits_n)
  (declare-fun Bits_n!val!15 () Bits_n)
  (declare-fun Bits_n!val!39 () Bits_n)
  (declare-fun Bits_n!val!66 () Bits_n)
  (declare-fun Bits_n!val!24 () Bits_n)
  (declare-fun Bits_n!val!11 () Bits_n)
  (declare-fun Bits_n!val!41 () Bits_n)
  (declare-fun Bits_n!val!29 () Bits_n)
  (declare-fun Bits_n!val!53 () Bits_n)
  (declare-fun Bits_n!val!46 () Bits_n)
  (declare-fun Bits_n!val!31 () Bits_n)
  (declare-fun Bits_n!val!28 () Bits_n)
  (declare-fun Bits_n!val!1 () Bits_n)
  (declare-fun Bits_n!val!33 () Bits_n)
  (declare-fun Bits_n!val!51 () Bits_n)
  (declare-fun Bits_n!val!10 () Bits_n)
  (declare-fun Bits_n!val!61 () Bits_n)
  (declare-fun Bits_n!val!22 () Bits_n)
  (declare-fun Bits_n!val!35 () Bits_n)
  (declare-fun Bits_n!val!0 () Bits_n)
  (declare-fun Bits_n!val!27 () Bits_n)
  (declare-fun Bits_n!val!20 () Bits_n)
  (declare-fun Bits_n!val!5 () Bits_n)
  (declare-fun Bits_n!val!9 () Bits_n)
  (declare-fun Bits_n!val!4 () Bits_n)
  (declare-fun Bits_n!val!13 () Bits_n)
  (declare-fun Bits_n!val!32 () Bits_n)
  (declare-fun Bits_n!val!7 () Bits_n)
  (declare-fun Bits_n!val!40 () Bits_n)
  (declare-fun Bits_n!val!26 () Bits_n)
  (declare-fun Bits_n!val!50 () Bits_n)
  (declare-fun Bits_n!val!57 () Bits_n)
  (declare-fun Bits_n!val!17 () Bits_n)
  (declare-fun Bits_n!val!34 () Bits_n)
  (declare-fun Bits_n!val!37 () Bits_n)
  (declare-fun Bits_n!val!19 () Bits_n)
  (declare-fun Bits_n!val!59 () Bits_n)
  (declare-fun Bits_n!val!64 () Bits_n)
  (declare-fun Bits_n!val!30 () Bits_n)
  (declare-fun Bits_n!val!54 () Bits_n)
  (declare-fun Bits_n!val!56 () Bits_n)
  (declare-fun Bits_n!val!49 () Bits_n)
  (declare-fun Bits_n!val!14 () Bits_n)
  (declare-fun Bits_n!val!43 () Bits_n)
  (declare-fun Bits_n!val!36 () Bits_n)
  (declare-fun Bits_n!val!12 () Bits_n)
  (declare-fun Bits_n!val!23 () Bits_n)
  (declare-fun Bits_n!val!45 () Bits_n)
  (declare-fun Bits_n!val!48 () Bits_n)
  (declare-fun Bits_n!val!58 () Bits_n)
  (declare-fun Bits_n!val!63 () Bits_n)
  (declare-fun Bits_n!val!6 () Bits_n)
  (declare-fun Bits_n!val!52 () Bits_n)
  (declare-fun Bits_n!val!55 () Bits_n)
  (declare-fun Bits_n!val!44 () Bits_n)
  (declare-fun Bits_n!val!67 () Bits_n)
  (declare-fun Bits_n!val!16 () Bits_n)
  (declare-fun Bits_n!val!18 () Bits_n)
  (declare-fun Bits_n!val!60 () Bits_n)
  (declare-fun Bits_n!val!21 () Bits_n)
  (declare-fun Bits_n!val!42 () Bits_n)
  (declare-fun Bits_n!val!8 () Bits_n)
  (declare-fun Bits_n!val!2 () Bits_n)
  (declare-fun Bits_n!val!62 () Bits_n)
  ;; cardinality constraint:
  (forall ((x Bits_n))
          (or (= x Bits_n!val!47)
              (= x Bits_n!val!38)
              (= x Bits_n!val!65)
              (= x Bits_n!val!25)
              (= x Bits_n!val!3)
              (= x Bits_n!val!15)
              (= x Bits_n!val!39)
              (= x Bits_n!val!66)
              (= x Bits_n!val!24)
              (= x Bits_n!val!11)
              (= x Bits_n!val!41)
              (= x Bits_n!val!29)
              (= x Bits_n!val!53)
              (= x Bits_n!val!46)
              (= x Bits_n!val!31)
              (= x Bits_n!val!28)
              (= x Bits_n!val!1)
              (= x Bits_n!val!33)
              (= x Bits_n!val!51)
              (= x Bits_n!val!10)
              (= x Bits_n!val!61)
              (= x Bits_n!val!22)
              (= x Bits_n!val!35)
              (= x Bits_n!val!0)
              (= x Bits_n!val!27)
              (= x Bits_n!val!20)
              (= x Bits_n!val!5)
              (= x Bits_n!val!9)
              (= x Bits_n!val!4)
              (= x Bits_n!val!13)
              (= x Bits_n!val!32)
              (= x Bits_n!val!7)
              (= x Bits_n!val!40)
              (= x Bits_n!val!26)
              (= x Bits_n!val!50)
              (= x Bits_n!val!57)
              (= x Bits_n!val!17)
              (= x Bits_n!val!34)
              (= x Bits_n!val!37)
              (= x Bits_n!val!19)
              (= x Bits_n!val!59)
              (= x Bits_n!val!64)
              (= x Bits_n!val!30)
              (= x Bits_n!val!54)
              (= x Bits_n!val!56)
              (= x Bits_n!val!49)
              (= x Bits_n!val!14)
              (= x Bits_n!val!43)
              (= x Bits_n!val!36)
              (= x Bits_n!val!12)
              (= x Bits_n!val!23)
              (= x Bits_n!val!45)
              (= x Bits_n!val!48)
              (= x Bits_n!val!58)
              (= x Bits_n!val!63)
              (= x Bits_n!val!6)
              (= x Bits_n!val!52)
              (= x Bits_n!val!55)
              (= x Bits_n!val!44)
              (= x Bits_n!val!67)
              (= x Bits_n!val!16)
              (= x Bits_n!val!18)
              (= x Bits_n!val!60)
              (= x Bits_n!val!21)
              (= x Bits_n!val!42)
              (= x Bits_n!val!8)
              (= x Bits_n!val!2)
              (= x Bits_n!val!62)))
  ;; -----------
  ;; universe for Bits_m:
  ;;   Bits_m!val!10 Bits_m!val!0 Bits_m!val!9 Bits_m!val!4 Bits_m!val!1 Bits_m!val!3 Bits_m!val!5 Bits_m!val!6 Bits_m!val!7 Bits_m!val!2 Bits_m!val!8 
  ;; -----------
  ;; definitions for universe elements:
  (declare-fun Bits_m!val!10 () Bits_m)
  (declare-fun Bits_m!val!0 () Bits_m)
  (declare-fun Bits_m!val!9 () Bits_m)
  (declare-fun Bits_m!val!4 () Bits_m)
  (declare-fun Bits_m!val!1 () Bits_m)
  (declare-fun Bits_m!val!3 () Bits_m)
  (declare-fun Bits_m!val!5 () Bits_m)
  (declare-fun Bits_m!val!6 () Bits_m)
  (declare-fun Bits_m!val!7 () Bits_m)
  (declare-fun Bits_m!val!2 () Bits_m)
  (declare-fun Bits_m!val!8 () Bits_m)
  ;; cardinality constraint:
  (forall ((x Bits_m))
          (or (= x Bits_m!val!10)
              (= x Bits_m!val!0)
              (= x Bits_m!val!9)
              (= x Bits_m!val!4)
              (= x Bits_m!val!1)
              (= x Bits_m!val!3)
              (= x Bits_m!val!5)
              (= x Bits_m!val!6)
              (= x Bits_m!val!7)
              (= x Bits_m!val!2)
              (= x Bits_m!val!8)))
  ;; -----------
  ;; universe for Bits_p:
  ;;   Bits_p!val!2 Bits_p!val!3 Bits_p!val!0 Bits_p!val!4 Bits_p!val!1 
  ;; -----------
  ;; definitions for universe elements:
  (declare-fun Bits_p!val!2 () Bits_p)
  (declare-fun Bits_p!val!3 () Bits_p)
  (declare-fun Bits_p!val!0 () Bits_p)
  (declare-fun Bits_p!val!4 () Bits_p)
  (declare-fun Bits_p!val!1 () Bits_p)
  ;; cardinality constraint:
  (forall ((x Bits_p))
          (or (= x Bits_p!val!2)
              (= x Bits_p!val!3)
              (= x Bits_p!val!0)
              (= x Bits_p!val!4)
              (= x Bits_p!val!1)))
  ;; -----------
  (define-fun is-abort-left () Bool
    false)
  (define-fun ctr-rr-left-new () Int
    7720)
  (define-fun table-top-left-old () (Array Int (Maybe (Array Bool (Maybe Bits_n))))
    (_ as-array k!26710))
  (define-fun postcondition-holds () Bool
    false)
  (define-fun ctr-r-right () Int
    2096006)

  (define-fun table-top-right-old () (Array Int (Maybe (Array Bool (Maybe Bits_n))))
    (_ as-array k!26710))
  (define-fun lemma1 () Bool
    false)
  (define-fun ctr-rr-right-new () Int
    7719)
  (define-fun rr-right () Bits_n
    Bits_n!val!0)
  (define-fun table-bottom-right-new () (Array Int (Maybe (Array Bool (Maybe Bits_n))))
    (_ as-array k!26712))
  (define-fun state-left-new () CompositionState-Left
    (let ((a!1 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         34
                         (mk-some true))
                  109
                  (mk-some true)))
      (a!2 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         64
                         (as mk-none (Maybe Bool)))
                  50
                  (as mk-none (Maybe Bool))))
      (a!5 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         44
                         (mk-some true))
                  39
                  (mk-some true))))
(let ((a!3 (store (store (store a!2 48 (mk-some true)) 13 (mk-some true))
                  73
                  (as mk-none (Maybe Bool))))
      (a!6 (mk-state-Left-keys_bottom
             (_ as-array k!26707)
             (_ as-array k!26706)
             (store (store a!1 82 (mk-some true)) 57 (mk-some true))
             (store (store a!5 45 (as mk-none (Maybe Bool)))
                    63
                    (as mk-none (Maybe Bool))))))
(let ((a!4 (mk-state-Left-keys_top
             (_ as-array k!26710)
             (store (store a!1 82 (mk-some true)) 57 (mk-some true))
             (_ as-array k!26709)
             a!3)))
  (mk-composition-state-Left
    a!4
    a!6
    mk-state-Left-gate
    mk-state-Left-enc
    Bits_m!val!8
    14
    15
    16
    Bits_n!val!15
    17
    18
    19
    2096007
    7720
    2096005
    906851)))))
  (define-fun ctr-r-left-new () Int
    2096007)
  (define-fun r-left () Bits_n
    Bits_n!val!11)
  (define-fun table-top-left-new () (Array Int (Maybe (Array Bool (Maybe Bits_n))))
    (_ as-array k!26710))
  (define-fun ctr-r-left () Int
    2096006)
  (define-fun ctr-rr-right () Int
    7719)
  (define-fun l () Int
    10)
  (define-fun standard-postcondition-holds () Bool
    true)
  (define-fun debug-bottom-right () Bool
    true)
  (define-fun ctr-r-right-new () Int
    2096006)
  (define-fun lemmas-hold () Bool
    false)
  (define-fun state-left-old () CompositionState-Left
    (let ((a!1 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         34
                         (mk-some true))
                  109
                  (mk-some true)))
      (a!2 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         64
                         (as mk-none (Maybe Bool)))
                  50
                  (as mk-none (Maybe Bool))))
      (a!5 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         34
                         (mk-some true))
                  82
                  (mk-some true)))
      (a!6 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         44
                         (mk-some true))
                  39
                  (mk-some true))))
(let ((a!3 (store (store (store a!2 48 (mk-some true)) 13 (mk-some true))
                  73
                  (as mk-none (Maybe Bool)))))
(let ((a!4 (mk-state-Left-keys_top
             (_ as-array k!26710)
             (store (store a!1 82 (mk-some true)) 57 (mk-some true))
             (_ as-array k!26709)
             a!3)))
  (mk-composition-state-Left
    a!4
    (mk-state-Left-keys_bottom
      (_ as-array k!26712)
      (_ as-array k!26706)
      (store a!5 57 (mk-some true))
      (store (store a!6 45 (as mk-none (Maybe Bool)))
             63
             (as mk-none (Maybe Bool))))
    mk-state-Left-gate
    mk-state-Left-enc
    Bits_m!val!8
    14
    15
    16
    Bits_n!val!15
    17
    18
    19
    2096006
    7719
    2095997
    906847)))))
  (define-fun op () (Array (Tuple2 Bool Bool) (Maybe Bool))
    (store (store ((as const (Array (Tuple2 Bool Bool) (Maybe Bool)))
                (mk-some false))
              (mk-tuple2 true false)
              (mk-some true))
       (mk-tuple2 false true)
       (mk-some true)))
  (define-fun table-bottom-right-old () (Array Int (Maybe (Array Bool (Maybe Bits_n))))
    (_ as-array k!26712))
  (define-fun value-right () (Array Bits_p (Maybe Bool))
    (store ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))
       Bits_p!val!3
       (mk-some true)))
  (define-fun table-top-right-new () (Array Int (Maybe (Array Bool (Maybe Bits_n))))
    (_ as-array k!26710))
  (define-fun debug-bottom-left () Bool
    false)
  (define-fun return-right () Return_Right_simgate_GBLG
    (let ((a!1 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         10
                         (mk-some true))
                  13
                  (mk-some true)))
      (a!2 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         38
                         (mk-some true))
                  60
                  (mk-some true)))
      (a!4 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         76
                         (as mk-none (Maybe Bool)))
                  67
                  (as mk-none (Maybe Bool)))))
(let ((a!3 (store (store (store a!2 95 (mk-some true)) 10 (mk-some true))
                  71
                  (mk-some true)))
      (a!5 (store (store (store a!4 79 (mk-some true)) 100 (mk-some true))
                  27
                  (mk-some true))))
(let ((a!6 (mk-composition-state-Right
             (mk-state-Right-keys_top
               (_ as-array k!26710)
               (store a!1 30 (mk-some true))
               (_ as-array k!26719)
               (store a!3 93 (mk-some true)))
             (mk-state-Right-keys_bottom
               (_ as-array k!26712)
               (_ as-array k!26706)
               (_ as-array k!26717)
               (store a!5 52 (mk-some true)))
             mk-state-Right-simgate
             mk-state-Right-ev
             Bits_n!val!17
             Bits_m!val!9
             20
             21
             22
             23
             24
             25
             2096006
             7719
             21239
             2438
             8856
             11798
             8366
             32286
             10451
             30613)))
  (mk-return-Right-simgate-GBLG
    a!6
    (store ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))
           Bits_p!val!3
           (mk-some true)))))))
  (define-fun Z-right () (Array Bool (Maybe Bits_n))
    (store (store ((as const (Array Bool (Maybe Bits_n))) (mk-some Bits_n!val!64))
              false
              (mk-some Bits_n!val!0))
       true
       (mk-some Bits_n!val!11)))
  (define-fun hhh () Int
    109)
  (define-fun r-right () Bits_n
    Bits_n!val!11)
  (define-fun table-bottom-left-new () (Array Int (Maybe (Array Bool (Maybe Bits_n))))
    (_ as-array k!26707))
  (define-fun return-left () Return_Left_gate_GBLG
    (let ((a!1 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         34
                         (mk-some true))
                  109
                  (mk-some true)))
      (a!2 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         64
                         (as mk-none (Maybe Bool)))
                  50
                  (as mk-none (Maybe Bool))))
      (a!5 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         44
                         (mk-some true))
                  39
                  (mk-some true))))
(let ((a!3 (store (store (store a!2 48 (mk-some true)) 13 (mk-some true))
                  73
                  (as mk-none (Maybe Bool))))
      (a!6 (mk-state-Left-keys_bottom
             (_ as-array k!26707)
             (_ as-array k!26706)
             (store (store a!1 82 (mk-some true)) 57 (mk-some true))
             (store (store a!5 45 (as mk-none (Maybe Bool)))
                    63
                    (as mk-none (Maybe Bool))))))
(let ((a!4 (mk-state-Left-keys_top
             (_ as-array k!26710)
             (store (store a!1 82 (mk-some true)) 57 (mk-some true))
             (_ as-array k!26709)
             a!3)))
  (mk-return-Left-gate-GBLG
    (mk-composition-state-Left
      a!4
      a!6
      mk-state-Left-gate
      mk-state-Left-enc
      Bits_m!val!8
      14
      15
      16
      Bits_n!val!15
      17
      18
      19
      2096007
      7720
      2096005
      906851)
    (store ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))
           Bits_p!val!3
           (mk-some true)))))))
  (define-fun is-abort-right () Bool
    false)
  (define-fun r () Int
    13)
  (define-fun state-right-old () CompositionState-Right
    (let ((a!1 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         10
                         (mk-some true))
                  13
                  (mk-some true)))
      (a!2 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         38
                         (mk-some true))
                  60
                  (mk-some true)))
      (a!4 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         76
                         (as mk-none (Maybe Bool)))
                  67
                  (as mk-none (Maybe Bool)))))
(let ((a!3 (store (store (store a!2 95 (mk-some true)) 10 (mk-some true))
                  71
                  (mk-some true)))
      (a!5 (store (store (store a!4 79 (mk-some true)) 100 (mk-some true))
                  27
                  (mk-some true))))
  (mk-composition-state-Right
    (mk-state-Right-keys_top
      (_ as-array k!26710)
      (store a!1 30 (mk-some true))
      (_ as-array k!26719)
      (store a!3 93 (mk-some true)))
    (mk-state-Right-keys_bottom
      (_ as-array k!26712)
      (_ as-array k!26706)
      (_ as-array k!26721)
      (store a!5 52 (mk-some true)))
    mk-state-Right-simgate
    mk-state-Right-ev
    Bits_n!val!17
    Bits_m!val!9
    20
    21
    22
    23
    24
    25
    2096006
    7719
    21238
    2437
    8855
    11797
    8365
    32285
    10450
    30612))))
  (define-fun debug-top-right () Bool
    true)
  (define-fun ctr-rr-left () Int
    7719)
  (define-fun state-right-new () CompositionState-Right
    (let ((a!1 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         10
                         (mk-some true))
                  13
                  (mk-some true)))
      (a!2 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         38
                         (mk-some true))
                  60
                  (mk-some true)))
      (a!4 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         76
                         (as mk-none (Maybe Bool)))
                  67
                  (as mk-none (Maybe Bool)))))
(let ((a!3 (store (store (store a!2 95 (mk-some true)) 10 (mk-some true))
                  71
                  (mk-some true)))
      (a!5 (store (store (store a!4 79 (mk-some true)) 100 (mk-some true))
                  27
                  (mk-some true))))
  (mk-composition-state-Right
    (mk-state-Right-keys_top
      (_ as-array k!26710)
      (store a!1 30 (mk-some true))
      (_ as-array k!26719)
      (store a!3 93 (mk-some true)))
    (mk-state-Right-keys_bottom
      (_ as-array k!26712)
      (_ as-array k!26706)
      (_ as-array k!26717)
      (store a!5 52 (mk-some true)))
    mk-state-Right-simgate
    mk-state-Right-ev
    Bits_n!val!17
    Bits_m!val!9
    20
    21
    22
    23
    24
    25
    2096006
    7719
    21239
    2438
    8856
    11798
    8366
    32286
    10451
    30613))))
  (define-fun lemma4 () Bool
    true)
  (define-fun Z-left () (Array Bool (Maybe Bits_n))
    (store (store ((as const (Array Bool (Maybe Bits_n))) (mk-some Bits_n!val!67))
              false
              (as mk-none (Maybe Bits_n)))
       true
       (mk-some Bits_n!val!11)))
  (define-fun lemma3 () Bool
    false)
  (define-fun precondition-holds () Bool
    true)
  (define-fun lemma2 () Bool
    true)
  (define-fun j () Int
    109)
  (define-fun value-left () (Array Bits_p (Maybe Bool))
    (store ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))
       Bits_p!val!3
       (mk-some true)))
  (define-fun rr-left () Bits_n
    Bits_n!val!0)
  (define-fun debug-top-left () Bool
    true)
  (define-fun lemma5 () Bool
    false)
  (define-fun zero_bits_n () Bits_n
    Bits_n!val!47)
  (define-fun bit () Bool
    false)
  (define-fun zero_bits_p () Bits_p
    Bits_p!val!2)
  (define-fun zero_bits_m () Bits_m
    Bits_m!val!10)
  (define-fun handle () Int
    0)
  (define-fun k!26708 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 64) (as mk-none (Maybe Bool))
    (ite (= x!0 50) (as mk-none (Maybe Bool))
    (ite (= x!0 48) (mk-some true)
    (ite (= x!0 13) (mk-some true)
    (ite (= x!0 73) (as mk-none (Maybe Bool))
      (mk-some false)))))))
  (define-fun k!26695 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!51)
      (mk-some Bits_n!val!43)))
  (define-fun k!26681 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!59)
      (mk-some Bits_n!val!46)))
  (define-fun k!26709 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 29) (mk-some true)
    (ite (= x!0 109) (mk-some true)
    (ite (= x!0 75) (as mk-none (Maybe Bool))
    (ite (= x!0 10) (mk-some true)
    (ite (= x!0 99) (mk-some true)
    (ite (= x!0 31) (mk-some true)
    (ite (= x!0 70) (as mk-none (Maybe Bool))
    (ite (= x!0 43) (mk-some true)
    (ite (= x!0 66) (mk-some true)
      (mk-some false)))))))))))
  (define-fun k!26696 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!50)
      (mk-some Bits_n!val!45)))
  (define-fun k!26682 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!55)
      (mk-some Bits_n!val!48)))
  (define-fun __sample-rand-Right-Bits_n ((x!0 Int) (x!1 Int)) Bits_n
    (ite (and (= x!0 12) (= x!1 30612)) Bits_n!val!19
    (ite (and (= x!0 3) (= x!1 2096006)) Bits_n!val!11
    (ite (and (= x!0 4) (= x!1 7719)) Bits_n!val!0
      Bits_n!val!18))))
  (define-fun k!26697 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!21)
    (ite (= x!0 true) (mk-some Bits_n!val!57)
      (mk-some Bits_n!val!34))))
  (define-fun k!26683 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!61)
    (ite (= x!0 true) (mk-some Bits_n!val!52)
      (mk-some Bits_n!val!47))))
  (define-fun k!26711 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 34) (mk-some true)
    (ite (= x!0 82) (mk-some true)
    (ite (= x!0 57) (mk-some true)
      (mk-some false)))))
  (define-fun k!26698 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!22)
    (ite (= x!0 true) (mk-some Bits_n!val!58)
      (mk-some Bits_n!val!27))))
  (define-fun k!26684 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!30)
      (mk-some Bits_n!val!33)))
  (define-fun __func-Left-encm ((x!0 Bits_n) (x!1 Bits_m) (x!2 Bits_n)) Bits_p
    (ite (and (= x!0 Bits_n!val!16) (= x!1 Bits_m!val!3) (= x!2 Bits_n!val!6))
      Bits_p!val!1
    (ite (and (= x!0 Bits_n!val!13) (= x!1 Bits_m!val!5) (= x!2 Bits_n!val!9))
      Bits_p!val!2
    (ite (and (= x!0 Bits_n!val!13) (= x!1 Bits_m!val!7) (= x!2 Bits_n!val!14))
      Bits_p!val!3
      Bits_p!val!0))))
  (define-fun __sample-rand-Left-Bits_n ((x!0 Int) (x!1 Int)) Bits_n
    (ite (and (= x!0 5) (= x!1 2095997)) Bits_n!val!1
    (ite (and (= x!0 5) (= x!1 2095998)) Bits_n!val!2
    (ite (and (= x!0 6) (= x!1 906847)) Bits_n!val!3
    (ite (and (= x!0 5) (= x!1 2095999)) Bits_n!val!4
    (ite (and (= x!0 5) (= x!1 2096000)) Bits_n!val!5
    (ite (and (= x!0 6) (= x!1 906848)) Bits_n!val!6
    (ite (and (= x!0 5) (= x!1 2096001)) Bits_n!val!7
    (ite (and (= x!0 5) (= x!1 2096002)) Bits_n!val!8
    (ite (and (= x!0 6) (= x!1 906849)) Bits_n!val!9
    (ite (and (= x!0 5) (= x!1 2096003)) Bits_n!val!10
    (ite (and (= x!0 5) (= x!1 2096004)) Bits_n!val!12
    (ite (and (= x!0 6) (= x!1 906850)) Bits_n!val!14
    (ite (and (= x!0 3) (= x!1 2096006)) Bits_n!val!11
      Bits_n!val!0))))))))))))))
  (define-fun k!26699 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!16)
    (ite (= x!0 true) (mk-some Bits_n!val!13)
      (mk-some Bits_n!val!40))))
  (define-fun k!26685 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!23)
      (mk-some Bits_n!val!31)))
  (define-fun k!26700 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!0)
    (ite (= x!0 true) (mk-some Bits_n!val!11)
      (mk-some Bits_n!val!64))))
  (define-fun k!26686 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!24)
    (ite (= x!0 true) (mk-some Bits_n!val!49)
      (mk-some Bits_n!val!37))))
  (define-fun __func-Right-encn ((x!0 Bits_n) (x!1 Bits_n) (x!2 Bits_n)) Bits_m
    Bits_m!val!10)
  (define-fun k!26687 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!54)
      (mk-some Bits_n!val!41)))
  (define-fun k!26710 ((x!0 Int)) (Maybe (Array Bool (Maybe Bits_n)))
    (ite (= x!0 102)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!35))
                      false
                      (mk-some Bits_n!val!20)))
    (ite (= x!0 110)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!32))
                      false
                      (mk-some Bits_n!val!29)))
    (ite (= x!0 108)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!42))
                               false
                               (mk-some Bits_n!val!62))
                        true
                        (mk-some Bits_n!val!60))))
        (mk-some a!1))
    (ite (= x!0 101)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!38))
                      false
                      (mk-some Bits_n!val!36)))
    (ite (= x!0 109)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!47))
                               false
                               (mk-some Bits_n!val!61))
                        true
                        (mk-some Bits_n!val!52))))
        (mk-some a!1))
    (ite (= x!0 13)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!40))
                               false
                               (mk-some Bits_n!val!16))
                        true
                        (mk-some Bits_n!val!13))))
        (mk-some a!1))
    (ite (= x!0 105)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!45))
                      false
                      (mk-some Bits_n!val!50)))
    (ite (= x!0 126)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!31))
                      false
                      (mk-some Bits_n!val!23)))
    (ite (= x!0 10)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!64))
                               false
                               (mk-some Bits_n!val!0))
                        true
                        (mk-some Bits_n!val!11))))
        (mk-some a!1))
    (ite (= x!0 111)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!28))
                               false
                               (mk-some Bits_n!val!25))
                        true
                        (mk-some Bits_n!val!26))))
        (mk-some a!1))
    (ite (= x!0 127)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!37))
                               false
                               (mk-some Bits_n!val!24))
                        true
                        (mk-some Bits_n!val!49))))
        (mk-some a!1))
    (ite (= x!0 107)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!46))
                      false
                      (mk-some Bits_n!val!59)))
      (mk-some ((as const (Array Bool (Maybe Bits_n))) (mk-some Bits_n!val!65))))))))))))))))
  (define-fun k!26688 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!20)
      (mk-some Bits_n!val!35)))
  (define-fun k!26716 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 76) (as mk-none (Maybe Bool))
    (ite (= x!0 67) (as mk-none (Maybe Bool))
    (ite (= x!0 79) (mk-some true)
    (ite (= x!0 100) (mk-some true)
    (ite (= x!0 27) (mk-some true)
    (ite (= x!0 52) (mk-some true)
      (mk-some false))))))))
  (define-fun k!26689 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!63)
      (mk-some Bits_n!val!39)))
  (define-fun k!26717 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 89) (mk-some true)
    (ite (= x!0 109) (mk-some true)
    (ite (= x!0 54) (mk-some true)
    (ite (= x!0 83) (mk-some true)
    (ite (= x!0 85) (mk-some true)
    (ite (= x!0 86) (mk-some true)
    (ite (= x!0 35) (mk-some true)
    (ite (= x!0 88) (mk-some true)
    (ite (= x!0 87) (mk-some true)
    (ite (= x!0 55) (mk-some true)
    (ite (= x!0 97) (mk-some true)
    (ite (= x!0 41) (mk-some true)
    (ite (= x!0 91) (mk-some true)
      (mk-some false)))))))))))))))
  (define-fun k!26690 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!25)
    (ite (= x!0 true) (mk-some Bits_n!val!26)
      (mk-some Bits_n!val!28))))
  (define-fun k!26718 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 38) (mk-some true)
    (ite (= x!0 60) (mk-some true)
    (ite (= x!0 95) (mk-some true)
    (ite (= x!0 10) (mk-some true)
    (ite (= x!0 71) (mk-some true)
    (ite (= x!0 93) (mk-some true)
      (mk-some false))))))))
  (define-fun __func-Right-encm ((x!0 Bits_n) (x!1 Bits_m) (x!2 Bits_n)) Bits_p
    Bits_p!val!3)
  (define-fun k!26704 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 44) (mk-some true)
    (ite (= x!0 39) (mk-some true)
    (ite (= x!0 45) (as mk-none (Maybe Bool))
    (ite (= x!0 63) (as mk-none (Maybe Bool))
      (mk-some false))))))
  (define-fun k!26691 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!29)
      (mk-some Bits_n!val!32)))
  (define-fun k!26719 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 33) (mk-some true)
    (ite (= x!0 92) (mk-some true)
    (ite (= x!0 58) (mk-some true)
    (ite (= x!0 53) (mk-some true)
    (ite (= x!0 10) (mk-some true)
    (ite (= x!0 77) (as mk-none (Maybe Bool))
    (ite (= x!0 81) (mk-some true)
    (ite (= x!0 13) (mk-some true)
    (ite (= x!0 78) (mk-some true)
      (mk-some false)))))))))))
  (define-fun k!26705 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 34) (mk-some true)
    (ite (= x!0 109) (mk-some true)
    (ite (= x!0 82) (mk-some true)
    (ite (= x!0 57) (mk-some true)
      (mk-some false))))))
  (define-fun k!26692 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!0)
      (as mk-none (Maybe Bits_n))))
  (define-fun k!26720 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 10) (mk-some true)
    (ite (= x!0 13) (mk-some true)
    (ite (= x!0 30) (mk-some true)
      (mk-some false)))))
  (define-fun k!26706 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 68) (mk-some true)
    (ite (= x!0 72) (mk-some true)
    (ite (= x!0 96) (mk-some true)
    (ite (= x!0 109) (as mk-none (Maybe Bool))
    (ite (= x!0 28) (mk-some true)
    (ite (= x!0 42) (mk-some true)
    (ite (= x!0 40) (mk-some true)
    (ite (= x!0 94) (mk-some true)
      (mk-some false))))))))))
  (define-fun k!26693 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!62)
    (ite (= x!0 true) (mk-some Bits_n!val!60)
      (mk-some Bits_n!val!42))))
  (define-fun k!26721 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 89) (mk-some true)
    (ite (= x!0 54) (mk-some true)
    (ite (= x!0 83) (mk-some true)
    (ite (= x!0 85) (mk-some true)
    (ite (= x!0 86) (mk-some true)
    (ite (= x!0 35) (mk-some true)
    (ite (= x!0 55) (mk-some true)
    (ite (= x!0 41) (mk-some true)
    (ite (= x!0 88) (mk-some true)
    (ite (= x!0 97) (mk-some true)
    (ite (= x!0 91) (mk-some true)
    (ite (= x!0 87) (mk-some true)
      (mk-some false))))))))))))))
  (define-fun k!26694 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!53)
    (ite (= x!0 true) (mk-some Bits_n!val!56)
      (mk-some Bits_n!val!44))))
  (define-fun k!26680 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!36)
      (mk-some Bits_n!val!38)))
  (define-fun __func-Left-encn ((x!0 Bits_n) (x!1 Bits_n) (x!2 Bits_n)) Bits_m
    (ite (and (= x!0 Bits_n!val!0) (= x!1 Bits_n!val!15) (= x!2 Bits_n!val!2))
      Bits_m!val!1
    (ite (and (= x!0 Bits_n!val!11) (= x!1 Bits_n!val!0) (= x!2 Bits_n!val!4))
      Bits_m!val!2
    (ite (and (= x!0 Bits_n!val!11) (= x!1 Bits_n!val!15) (= x!2 Bits_n!val!5))
      Bits_m!val!3
    (ite (and (= x!0 Bits_n!val!0) (= x!1 Bits_n!val!0) (= x!2 Bits_n!val!7))
      Bits_m!val!4
    (ite (and (= x!0 Bits_n!val!0) (= x!1 Bits_n!val!15) (= x!2 Bits_n!val!8))
      Bits_m!val!5
    (ite (and (= x!0 Bits_n!val!11) (= x!1 Bits_n!val!0) (= x!2 Bits_n!val!10))
      Bits_m!val!6
    (ite (and (= x!0 Bits_n!val!11) (= x!1 Bits_n!val!15) (= x!2 Bits_n!val!12))
      Bits_m!val!7
      Bits_m!val!0))))))))
)
unknown
unknown
unknown
