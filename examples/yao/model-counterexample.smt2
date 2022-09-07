  (define-fun handle () Int
    92)
  (define-fun hhh () Int
    92)
  (define-fun j () Int
    92)
  (define-fun debug-bottom-left () Bool
    false)
  (define-fun table-bottom-left-new () (Array Int (Maybe (Array Bool (Maybe Bits_n))))
    (_ as-array k!1112))

    ;At position 92, it does the following:

    ite (= x!0 92)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (as mk-none (Maybe Bits_n)))
                      false
                      (mk-some Bits_n!val!0)))






  (define-fun k!1112 ((x!0 Int)) (Maybe (Array Bool (Maybe Bits_n)))
    (ite (= x!0 86)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!29))
                               false
                               (mk-some Bits_n!val!24))
                        true
                        (mk-some Bits_n!val!42))))
        (mk-some a!1))
    (ite (= x!0 85)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!34))
                      false
                      (mk-some Bits_n!val!23)))
    (ite (= x!0 104)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!67))
                      false
                      (mk-some Bits_n!val!37)))
    (ite (= x!0 92)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (as mk-none (Maybe Bits_n)))
                      false
                      (mk-some Bits_n!val!0)))
    (ite (= x!0 101)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!61))
                      false
                      (mk-some Bits_n!val!51)))
    (ite (= x!0 87)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!59))
                               false
                               (mk-some Bits_n!val!47))
                        true
                        (mk-some Bits_n!val!56))))
        (mk-some a!1))
    (ite (= x!0 105) (as mk-none (Maybe (Array Bool (Maybe Bits_n))))
    (ite (= x!0 91)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!46))
                      false
                      (mk-some Bits_n!val!65)))
    (ite (= x!0 88)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!60))
                               false
                               (mk-some Bits_n!val!50))
                        true
                        (mk-some Bits_n!val!45))))
        (mk-some a!1))
    (ite (= x!0 89)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!53))
                               false
                               (mk-some Bits_n!val!44))
                        true
                        (mk-some Bits_n!val!55))))
        (mk-some a!1))
      (mk-some ((as const (Array Bool (Maybe Bits_n))) (mk-some Bits_n!val!72))))))))))))))


(
  ;; universe for Bits_n:
  ;;   Bits_n!val!47 Bits_n!val!38 Bits_n!val!65 Bits_n!val!25 Bits_n!val!70 Bits_n!val!3 Bits_n!val!15 Bits_n!val!39 Bits_n!val!66 Bits_n!val!24 Bits_n!val!11 Bits_n!val!41 Bits_n!val!29 Bits_n!val!53 Bits_n!val!46 Bits_n!val!31 Bits_n!val!28 Bits_n!val!1 Bits_n!val!33 Bits_n!val!51 Bits_n!val!10 Bits_n!val!74 Bits_n!val!61 Bits_n!val!22 Bits_n!val!35 Bits_n!val!0 Bits_n!val!27 Bits_n!val!20 Bits_n!val!5 Bits_n!val!9 Bits_n!val!4 Bits_n!val!13 Bits_n!val!32 Bits_n!val!7 Bits_n!val!40 Bits_n!val!26 Bits_n!val!50 Bits_n!val!57 Bits_n!val!17 Bits_n!val!34 Bits_n!val!37 Bits_n!val!19 Bits_n!val!59 Bits_n!val!71 Bits_n!val!64 Bits_n!val!30 Bits_n!val!54 Bits_n!val!56 Bits_n!val!49 Bits_n!val!14 Bits_n!val!43 Bits_n!val!68 Bits_n!val!36 Bits_n!val!12 Bits_n!val!23 Bits_n!val!45 Bits_n!val!48 Bits_n!val!58 Bits_n!val!63 Bits_n!val!72 Bits_n!val!6 Bits_n!val!52 Bits_n!val!55 Bits_n!val!44 Bits_n!val!67 Bits_n!val!16 Bits_n!val!18 Bits_n!val!60 Bits_n!val!21 Bits_n!val!73 Bits_n!val!69 Bits_n!val!42 Bits_n!val!8 Bits_n!val!2 Bits_n!val!62 
  ;; -----------
  ;; definitions for universe elements:
  (declare-fun Bits_n!val!47 () Bits_n)
  (declare-fun Bits_n!val!38 () Bits_n)
  (declare-fun Bits_n!val!65 () Bits_n)
  (declare-fun Bits_n!val!25 () Bits_n)
  (declare-fun Bits_n!val!70 () Bits_n)
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
  (declare-fun Bits_n!val!74 () Bits_n)
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
  (declare-fun Bits_n!val!71 () Bits_n)
  (declare-fun Bits_n!val!64 () Bits_n)
  (declare-fun Bits_n!val!30 () Bits_n)
  (declare-fun Bits_n!val!54 () Bits_n)
  (declare-fun Bits_n!val!56 () Bits_n)
  (declare-fun Bits_n!val!49 () Bits_n)
  (declare-fun Bits_n!val!14 () Bits_n)
  (declare-fun Bits_n!val!43 () Bits_n)
  (declare-fun Bits_n!val!68 () Bits_n)
  (declare-fun Bits_n!val!36 () Bits_n)
  (declare-fun Bits_n!val!12 () Bits_n)
  (declare-fun Bits_n!val!23 () Bits_n)
  (declare-fun Bits_n!val!45 () Bits_n)
  (declare-fun Bits_n!val!48 () Bits_n)
  (declare-fun Bits_n!val!58 () Bits_n)
  (declare-fun Bits_n!val!63 () Bits_n)
  (declare-fun Bits_n!val!72 () Bits_n)
  (declare-fun Bits_n!val!6 () Bits_n)
  (declare-fun Bits_n!val!52 () Bits_n)
  (declare-fun Bits_n!val!55 () Bits_n)
  (declare-fun Bits_n!val!44 () Bits_n)
  (declare-fun Bits_n!val!67 () Bits_n)
  (declare-fun Bits_n!val!16 () Bits_n)
  (declare-fun Bits_n!val!18 () Bits_n)
  (declare-fun Bits_n!val!60 () Bits_n)
  (declare-fun Bits_n!val!21 () Bits_n)
  (declare-fun Bits_n!val!73 () Bits_n)
  (declare-fun Bits_n!val!69 () Bits_n)
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
              (= x Bits_n!val!70)
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
              (= x Bits_n!val!74)
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
              (= x Bits_n!val!71)
              (= x Bits_n!val!64)
              (= x Bits_n!val!30)
              (= x Bits_n!val!54)
              (= x Bits_n!val!56)
              (= x Bits_n!val!49)
              (= x Bits_n!val!14)
              (= x Bits_n!val!43)
              (= x Bits_n!val!68)
              (= x Bits_n!val!36)
              (= x Bits_n!val!12)
              (= x Bits_n!val!23)
              (= x Bits_n!val!45)
              (= x Bits_n!val!48)
              (= x Bits_n!val!58)
              (= x Bits_n!val!63)
              (= x Bits_n!val!72)
              (= x Bits_n!val!6)
              (= x Bits_n!val!52)
              (= x Bits_n!val!55)
              (= x Bits_n!val!44)
              (= x Bits_n!val!67)
              (= x Bits_n!val!16)
              (= x Bits_n!val!18)
              (= x Bits_n!val!60)
              (= x Bits_n!val!21)
              (= x Bits_n!val!73)
              (= x Bits_n!val!69)
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
  (define-fun return-right () Return_Right_simgate_GBLG
    (let ((a!1 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         29
                         (as mk-none (Maybe Bool)))
                  28
                  (mk-some true)))
      (a!3 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         26
                         (mk-some true))
                  67
                  (as mk-none (Maybe Bool))))
      (a!4 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         99
                         (mk-some true))
                  32
                  (as mk-none (Maybe Bool))))
      (a!7 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         65
                         (as mk-none (Maybe Bool)))
                  55
                  (mk-some true)))
      (a!8 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         77
                         (mk-some true))
                  70
                  (mk-some true))))
(let ((a!2 (store (store (store a!1 39 (mk-some true)) 2 (mk-some true))
                  63
                  (mk-some true)))
      (a!5 (store (store (store a!4 81 (mk-some true)) 52 (mk-some true))
                  61
                  (mk-some true)))
      (a!9 (store (store (store a!8 56 (mk-some true)) 38 (mk-some true))
                  96
                  (mk-some true))))
(let ((a!6 (mk-state-Right-keys_top
             (_ as-array k!1114)
             a!2
             (store (store a!3 7 (mk-some true)) 2 (mk-some true))
             a!5))
      (a!10 (mk-state-Right-keys_bottom
              (_ as-array k!1116)
              (store (store (store a!7 68 (as mk-none (Maybe Bool)))
                            46
                            (mk-some true))
                     92
                     (as mk-none (Maybe Bool)))
              (_ as-array k!1122)
              a!9)))
  (mk-return-Right-simgate-GBLG
    (mk-composition-state-Right
      a!6
      a!10
      mk-state-Right-simgate
      mk-state-Right-ev
      Bits_n!val!18
      Bits_m!val!9
      16
      17
      18
      19
      20
      21
      2596311
      7719
      21239
      2438
      8856
      11798
      8366
      32286
      10451
      30613)
    (store ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))
           Bits_p!val!4
           (mk-some true)))))))
  (define-fun postcondition-holds () Bool
    false)
  (define-fun ctr-r-right () Int
    2596311)
  (define-fun table-bottom-left-old () (Array Int (Maybe (Array Bool (Maybe Bits_n))))
    (_ as-array k!1116))
  (define-fun table-top-right-old () (Array Int (Maybe (Array Bool (Maybe Bits_n))))
    (_ as-array k!1114))
  (define-fun lemma1 () Bool
    false)
  (define-fun ctr-rr-right-new () Int
    7719)
  (define-fun rr-right () Bits_n
    Bits_n!val!0)
  (define-fun table-bottom-right-new () (Array Int (Maybe (Array Bool (Maybe Bits_n))))
    (_ as-array k!1116))
  (define-fun state-left-new () CompositionState-Left
    (let ((a!1 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         60
                         (mk-some true))
                  79
                  (mk-some true)))
      (a!3 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         54
                         (as mk-none (Maybe Bool)))
                  35
                  (mk-some true))))
(let ((a!2 (store (store (store a!1 25 (mk-some true)) 73 (mk-some true))
                  24
                  (mk-some true))))
(let ((a!4 (mk-state-Left-keys_top
             (_ as-array k!1114)
             a!2
             (_ as-array k!1110)
             (store (store a!3 30 (mk-some true)) 43 (as mk-none (Maybe Bool))))))
  (mk-composition-state-Left
    a!4
    (mk-state-Left-keys_bottom
      (_ as-array k!1112)
      a!2
      (_ as-array k!1110)
      (_ as-array k!1110))
    mk-state-Left-gate
    mk-state-Left-enc
    Bits_m!val!8
    8
    9
    10
    Bits_n!val!16
    13
    14
    15
    2596312
    7720
    2596307
    2617258)))))
  (define-fun table-top-left-old () (Array Int (Maybe (Array Bool (Maybe Bits_n))))
    (_ as-array k!1114))
  (define-fun lemma4 () Bool
    false)
  (define-fun ctr-r-left-new () Int
    2596312)
  (define-fun table-top-left-new () (Array Int (Maybe (Array Bool (Maybe Bits_n))))
    (_ as-array k!1114))
  (define-fun r-left () Bits_n
    Bits_n!val!21)
  (define-fun standard-postcondition-holds () Bool
    false)
  (define-fun handle () Int
    92)
  (define-fun debug-bottom-right () Bool
    true)
  (define-fun ctr-r-right-new () Int
    2596311)
  (define-fun lemmas-hold () Bool
    false)
  (define-fun state-left-old () CompositionState-Left
    (let ((a!1 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         60
                         (mk-some true))
                  79
                  (mk-some true)))
      (a!3 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         54
                         (as mk-none (Maybe Bool)))
                  35
                  (mk-some true))))
(let ((a!2 (store (store (store a!1 25 (mk-some true)) 73 (mk-some true))
                  24
                  (mk-some true))))
(let ((a!4 (mk-state-Left-keys_top
             (_ as-array k!1114)
             a!2
             (_ as-array k!1110)
             (store (store a!3 30 (mk-some true)) 43 (as mk-none (Maybe Bool))))))
  (mk-composition-state-Left
    a!4
    (mk-state-Left-keys_bottom
      (_ as-array k!1116)
      a!2
      (_ as-array k!1115)
      (_ as-array k!1110))
    mk-state-Left-gate
    mk-state-Left-enc
    Bits_m!val!8
    8
    9
    10
    Bits_n!val!16
    13
    14
    15
    2596311
    7719
    2596299
    2617254)))))
  (define-fun ctr-r-left () Int
    2596311)
  (define-fun table-bottom-right-old () (Array Int (Maybe (Array Bool (Maybe Bits_n))))
    (_ as-array k!1116))
  (define-fun state-right-new () CompositionState-Right
    (let ((a!1 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         29
                         (as mk-none (Maybe Bool)))
                  28
                  (mk-some true)))
      (a!3 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         26
                         (mk-some true))
                  67
                  (as mk-none (Maybe Bool))))
      (a!4 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         99
                         (mk-some true))
                  32
                  (as mk-none (Maybe Bool))))
      (a!7 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         65
                         (as mk-none (Maybe Bool)))
                  55
                  (mk-some true)))
      (a!8 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         77
                         (mk-some true))
                  70
                  (mk-some true))))
(let ((a!2 (store (store (store a!1 39 (mk-some true)) 2 (mk-some true))
                  63
                  (mk-some true)))
      (a!5 (store (store (store a!4 81 (mk-some true)) 52 (mk-some true))
                  61
                  (mk-some true)))
      (a!9 (store (store (store a!8 56 (mk-some true)) 38 (mk-some true))
                  96
                  (mk-some true))))
(let ((a!6 (mk-state-Right-keys_top
             (_ as-array k!1114)
             a!2
             (store (store a!3 7 (mk-some true)) 2 (mk-some true))
             a!5))
      (a!10 (mk-state-Right-keys_bottom
              (_ as-array k!1116)
              (store (store (store a!7 68 (as mk-none (Maybe Bool)))
                            46
                            (mk-some true))
                     92
                     (as mk-none (Maybe Bool)))
              (_ as-array k!1122)
              a!9)))
  (mk-composition-state-Right
    a!6
    a!10
    mk-state-Right-simgate
    mk-state-Right-ev
    Bits_n!val!18
    Bits_m!val!9
    16
    17
    18
    19
    20
    21
    2596311
    7719
    21239
    2438
    8856
    11798
    8366
    32286
    10451
    30613)))))
  (define-fun value-right () (Array Bits_p (Maybe Bool))
    (store ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))
       Bits_p!val!4
       (mk-some true)))

  (define-fun table-top-right-new () (Array Int (Maybe (Array Bool (Maybe Bits_n))))
    (_ as-array k!1114))

  (define-fun Z-right () (Array Bool (Maybe Bits_n))
    (store (store ((as const (Array Bool (Maybe Bits_n))) (mk-some Bits_n!val!74))
              false
              (mk-some Bits_n!val!0))
       true
       (mk-some Bits_n!val!21)))

  (define-fun r-right () Bits_n
    Bits_n!val!21)
  (define-fun return-left () Return_Left_gate_GBLG
    (let ((a!1 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         60
                         (mk-some true))
                  79
                  (mk-some true)))
      (a!3 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         54
                         (as mk-none (Maybe Bool)))
                  35
                  (mk-some true))))
(let ((a!2 (store (store (store a!1 25 (mk-some true)) 73 (mk-some true))
                  24
                  (mk-some true))))
(let ((a!4 (mk-state-Left-keys_top
             (_ as-array k!1114)
             a!2
             (_ as-array k!1110)
             (store (store a!3 30 (mk-some true)) 43 (as mk-none (Maybe Bool))))))
  (mk-return-Left-gate-GBLG
    (mk-composition-state-Left
      a!4
      (mk-state-Left-keys_bottom
        (_ as-array k!1112)
        a!2
        (_ as-array k!1110)
        (_ as-array k!1110))
      mk-state-Left-gate
      mk-state-Left-enc
      Bits_m!val!8
      8
      9
      10
      Bits_n!val!16
      13
      14
      15
      2596312
      7720
      2596307
      2617258)
    (store ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))
           Bits_p!val!3
           (mk-some true)))))))
  (define-fun ctr-rr-right () Int
    7719)
  (define-fun is-abort-right () Bool
    false)
  (define-fun r () Int
    7)
  (define-fun state-right-old () CompositionState-Right
    (let ((a!1 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         29
                         (as mk-none (Maybe Bool)))
                  28
                  (mk-some true)))
      (a!3 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         26
                         (mk-some true))
                  67
                  (as mk-none (Maybe Bool))))
      (a!4 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         99
                         (mk-some true))
                  32
                  (as mk-none (Maybe Bool))))
      (a!7 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         65
                         (as mk-none (Maybe Bool)))
                  55
                  (mk-some true)))
      (a!8 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         77
                         (mk-some true))
                  70
                  (mk-some true))))
(let ((a!2 (store (store (store a!1 39 (mk-some true)) 2 (mk-some true))
                  63
                  (mk-some true)))
      (a!5 (store (store (store a!4 81 (mk-some true)) 52 (mk-some true))
                  61
                  (mk-some true)))
      (a!9 (store (store (store a!8 56 (mk-some true)) 38 (mk-some true))
                  96
                  (mk-some true))))
(let ((a!6 (mk-state-Right-keys_top
             (_ as-array k!1114)
             a!2
             (store (store a!3 7 (mk-some true)) 2 (mk-some true))
             a!5))
      (a!10 (mk-state-Right-keys_bottom
              (_ as-array k!1116)
              (store (store (store a!7 68 (as mk-none (Maybe Bool)))
                            46
                            (mk-some true))
                     92
                     (as mk-none (Maybe Bool)))
              (_ as-array k!1127)
              a!9)))
  (mk-composition-state-Right
    a!6
    a!10
    mk-state-Right-simgate
    mk-state-Right-ev
    Bits_n!val!18
    Bits_m!val!9
    16
    17
    18
    19
    20
    21
    2596311
    7719
    21238
    2437
    8855
    11797
    8365
    32285
    10450
    30612)))))
  (define-fun debug-top-right () Bool
    true)
  (define-fun ctr-rr-left () Int
    7719)
  (define-fun lemma2 () Bool
    true)
  (define-fun l () Int
    2)
  (define-fun Z-left () (Array Bool (Maybe Bits_n))
    (store (store ((as const (Array Bool (Maybe Bits_n))) (mk-some Bits_n!val!73))
              false
              (as mk-none (Maybe Bits_n)))
       true
       (mk-some Bits_n!val!21)))
  (define-fun op () (Array (Tuple2 Bool Bool) (Maybe Bool))
    ((as const (Array (Tuple2 Bool Bool) (Maybe Bool))) (mk-some false)))
  (define-fun precondition-holds () Bool
    true)
  (define-fun lemma3 () Bool
    false)
  (define-fun debug-top-left () Bool
    true)

  (define-fun value-left () (Array Bits_p (Maybe Bool))
    (store ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))
       Bits_p!val!3
       (mk-some true)))
  (define-fun rr-left () Bits_n
    Bits_n!val!0)
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
  (define-fun k!1095 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!65)
      (mk-some Bits_n!val!46)))
  (define-fun k!1123 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 65) (as mk-none (Maybe Bool))
    (ite (= x!0 55) (mk-some true)
    (ite (= x!0 68) (as mk-none (Maybe Bool))
    (ite (= x!0 46) (mk-some true)
    (ite (= x!0 92) (as mk-none (Maybe Bool))
      (mk-some false)))))))
  (define-fun k!1096 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!58)
    (ite (= x!0 true) (mk-some Bits_n!val!57)
      (mk-some Bits_n!val!69))))
  (define-fun __sample-rand-Right-Bits_n ((x!0 Int) (x!1 Int)) Bits_n
    (ite (and (= x!0 12) (= x!1 30612)) Bits_n!val!20
    (ite (and (= x!0 3) (= x!1 2596311)) Bits_n!val!21
    (ite (and (= x!0 4) (= x!1 7719)) Bits_n!val!0
      Bits_n!val!19))))
  (define-fun k!1124 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 99) (mk-some true)
    (ite (= x!0 32) (as mk-none (Maybe Bool))
    (ite (= x!0 81) (mk-some true)
    (ite (= x!0 52) (mk-some true)
    (ite (= x!0 61) (mk-some true)
      (mk-some false)))))))
  (define-fun k!1110 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 59) (mk-some true)
    (ite (= x!0 92) (mk-some true)
    (ite (= x!0 47) (as mk-none (Maybe Bool))
    (ite (= x!0 51) (mk-some true)
    (ite (= x!0 2) (mk-some true)
    (ite (= x!0 31) (mk-some true)
    (ite (= x!0 41) (mk-some true)
    (ite (= x!0 7) (mk-some true)
    (ite (= x!0 23) (mk-some true)
      (mk-some false)))))))))))
  (define-fun k!1097 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!63)
    (ite (= x!0 true) (mk-some Bits_n!val!48)
      (mk-some Bits_n!val!66))))
  (define-fun k!1125 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 26) (mk-some true)
    (ite (= x!0 67) (as mk-none (Maybe Bool))
    (ite (= x!0 7) (mk-some true)
    (ite (= x!0 2) (mk-some true)
      (mk-some false))))))
  (define-fun k!1111 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 60) (mk-some true)
    (ite (= x!0 79) (mk-some true)
    (ite (= x!0 25) (mk-some true)
    (ite (= x!0 73) (mk-some true)
    (ite (= x!0 24) (mk-some true)
      (mk-some false)))))))
  (define-fun k!1098 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!44)
    (ite (= x!0 true) (mk-some Bits_n!val!55)
      (mk-some Bits_n!val!53))))
  (define-fun __func-Left-encm ((x!0 Bits_n) (x!1 Bits_m) (x!2 Bits_n)) Bits_p
    (ite (and (= x!0 Bits_n!val!6) (= x!1 Bits_m!val!3) (= x!2 Bits_n!val!7))
      Bits_p!val!1
    (ite (and (= x!0 Bits_n!val!17) (= x!1 Bits_m!val!5) (= x!2 Bits_n!val!11))
      Bits_p!val!2
    (ite (and (= x!0 Bits_n!val!17) (= x!1 Bits_m!val!7) (= x!2 Bits_n!val!15))
      Bits_p!val!3
      Bits_p!val!0))))
  (define-fun k!1126 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 29) (as mk-none (Maybe Bool))
    (ite (= x!0 28) (mk-some true)
    (ite (= x!0 39) (mk-some true)
    (ite (= x!0 2) (mk-some true)
    (ite (= x!0 63) (mk-some true)
      (mk-some false)))))))
  (define-fun __sample-rand-Left-Bits_n ((x!0 Int) (x!1 Int)) Bits_n
    (ite (and (= x!0 5) (= x!1 2596299)) Bits_n!val!1
    (ite (and (= x!0 5) (= x!1 2596300)) Bits_n!val!2
    (ite (and (= x!0 6) (= x!1 2617254)) Bits_n!val!3
    (ite (and (= x!0 5) (= x!1 2596301)) Bits_n!val!4
    (ite (and (= x!0 5) (= x!1 2596302)) Bits_n!val!5
    (ite (and (= x!0 6) (= x!1 2617255)) Bits_n!val!7
    (ite (and (= x!0 5) (= x!1 2596303)) Bits_n!val!8
    (ite (and (= x!0 5) (= x!1 2596304)) Bits_n!val!10
    (ite (and (= x!0 6) (= x!1 2617256)) Bits_n!val!11
    (ite (and (= x!0 5) (= x!1 2596305)) Bits_n!val!12
    (ite (and (= x!0 5) (= x!1 2596306)) Bits_n!val!14
    (ite (and (= x!0 6) (= x!1 2617257)) Bits_n!val!15
    (ite (and (= x!0 3) (= x!1 2596311)) Bits_n!val!21
      Bits_n!val!0))))))))))))))
  (define-fun k!1099 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!49)
      (mk-some Bits_n!val!43)))
  (define-fun k!1085 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!37)
      (mk-some Bits_n!val!67)))
  (define-fun k!1127 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 72) (mk-some true)
    (ite (= x!0 49) (mk-some true)
    (ite (= x!0 71) (mk-some true)
    (ite (= x!0 58) (mk-some true)
    (ite (= x!0 48) (mk-some true)
    (ite (= x!0 53) (as mk-none (Maybe Bool))
    (ite (= x!0 80) (as mk-none (Maybe Bool))
    (ite (= x!0 100) (mk-some true)
      (mk-some false))))))))))
  (define-fun k!1113 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 54) (as mk-none (Maybe Bool))
    (ite (= x!0 35) (mk-some true)
    (ite (= x!0 30) (mk-some true)
    (ite (= x!0 43) (as mk-none (Maybe Bool))
      (mk-some false))))))
  (define-fun k!1100 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!50)
    (ite (= x!0 true) (mk-some Bits_n!val!45)
      (mk-some Bits_n!val!60))))
  (define-fun k!1086 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!36)
      (mk-some Bits_n!val!68)))
  (define-fun __func-Right-encn ((x!0 Bits_n) (x!1 Bits_n) (x!2 Bits_n)) Bits_m
    Bits_m!val!10)
  (define-fun k!1101 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!47)
    (ite (= x!0 true) (mk-some Bits_n!val!56)
      (mk-some Bits_n!val!59))))
  (define-fun k!1087 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!25)
      (mk-some Bits_n!val!39)))
  (define-fun k!1115 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 59) (mk-some true)
    (ite (= x!0 47) (as mk-none (Maybe Bool))
    (ite (= x!0 51) (mk-some true)
    (ite (= x!0 2) (mk-some true)
    (ite (= x!0 31) (mk-some true)
    (ite (= x!0 41) (mk-some true)
    (ite (= x!0 7) (mk-some true)
    (ite (= x!0 23) (mk-some true)
      (mk-some false))))))))))
  (define-fun k!1102 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!64)
      (mk-some Bits_n!val!54)))
  (define-fun k!1088 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!28)
    (ite (= x!0 true) (mk-some Bits_n!val!40)
      (mk-some Bits_n!val!32))))
  (define-fun k!1103 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!24)
    (ite (= x!0 true) (mk-some Bits_n!val!42)
      (mk-some Bits_n!val!29))))
  (define-fun k!1089 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!27)
    (ite (= x!0 true) (as mk-none (Maybe Bits_n))
      (mk-some Bits_n!val!35))))

  (define-fun k!1104 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!23)
      (mk-some Bits_n!val!34)))
  (define-fun k!1090 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!51)
      (mk-some Bits_n!val!61)))
  (define-fun __func-Right-encm ((x!0 Bits_n) (x!1 Bits_m) (x!2 Bits_n)) Bits_p
    Bits_p!val!4)
  (define-fun k!1105 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!6)
    (ite (= x!0 true) (mk-some Bits_n!val!17)
      (mk-some Bits_n!val!62))))
  (define-fun k!1091 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!22)
    (ite (= x!0 true) (mk-some Bits_n!val!41)
      (mk-some Bits_n!val!38))))
  (define-fun k!1114 ((x!0 Int)) (Maybe (Array Bool (Maybe Bits_n)))
    (ite (= x!0 103)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!39))
                      false
                      (mk-some Bits_n!val!25)))
    (ite (= x!0 84)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!38))
                               false
                               (mk-some Bits_n!val!22))
                        true
                        (mk-some Bits_n!val!41))))
        (mk-some a!1))
    (ite (= x!0 93)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!30))
                      false
                      (mk-some Bits_n!val!26)))
    (ite (= x!0 90)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!66))
                               false
                               (mk-some Bits_n!val!63))
                        true
                        (mk-some Bits_n!val!48))))
        (mk-some a!1))
    (ite (= x!0 83)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!68))
                      false
                      (mk-some Bits_n!val!36)))
    (ite (= x!0 7)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!62))
                               false
                               (mk-some Bits_n!val!6))
                        true
                        (mk-some Bits_n!val!17))))
        (mk-some a!1))
    (ite (= x!0 87)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!54))
                      false
                      (mk-some Bits_n!val!64)))
    (ite (= x!0 91)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!69))
                               false
                               (mk-some Bits_n!val!58))
                        true
                        (mk-some Bits_n!val!57))))
        (mk-some a!1))
    (ite (= x!0 94)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!33))
                               false
                               (mk-some Bits_n!val!31))
                        true
                        (mk-some Bits_n!val!52))))
        (mk-some a!1))
    (ite (= x!0 2)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!70))
                               false
                               (mk-some Bits_n!val!9))
                        true
                        (mk-some Bits_n!val!13))))
        (mk-some a!1))
    (ite (= x!0 102)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!32))
                               false
                               (mk-some Bits_n!val!28))
                        true
                        (mk-some Bits_n!val!40))))
        (mk-some a!1))
    (ite (= x!0 89)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!43))
                      false
                      (mk-some Bits_n!val!49)))
      (mk-some ((as const (Array Bool (Maybe Bits_n))) (mk-some Bits_n!val!71))))))))))))))))
  (define-fun k!1106 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!9)
    (ite (= x!0 true) (mk-some Bits_n!val!13)
      (mk-some Bits_n!val!70))))
  (define-fun k!1092 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!31)
    (ite (= x!0 true) (mk-some Bits_n!val!52)
      (mk-some Bits_n!val!33))))
  (define-fun k!1093 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!26)
      (mk-some Bits_n!val!30)))
  (define-fun k!1116 ((x!0 Int)) (Maybe (Array Bool (Maybe Bits_n)))
    (ite (= x!0 86)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!29))
                               false
                               (mk-some Bits_n!val!24))
                        true
                        (mk-some Bits_n!val!42))))
        (mk-some a!1))
    (ite (= x!0 85)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!34))
                      false
                      (mk-some Bits_n!val!23)))
    (ite (= x!0 104)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!67))
                      false
                      (mk-some Bits_n!val!37)))
    (ite (= x!0 92) (as mk-none (Maybe (Array Bool (Maybe Bits_n))))
    (ite (= x!0 101)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!61))
                      false
                      (mk-some Bits_n!val!51)))
    (ite (= x!0 87)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!59))
                               false
                               (mk-some Bits_n!val!47))
                        true
                        (mk-some Bits_n!val!56))))
        (mk-some a!1))
    (ite (= x!0 105) (as mk-none (Maybe (Array Bool (Maybe Bits_n))))
    (ite (= x!0 91)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!46))
                      false
                      (mk-some Bits_n!val!65)))
    (ite (= x!0 88)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!60))
                               false
                               (mk-some Bits_n!val!50))
                        true
                        (mk-some Bits_n!val!45))))
        (mk-some a!1))
    (ite (= x!0 89)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!53))
                               false
                               (mk-some Bits_n!val!44))
                        true
                        (mk-some Bits_n!val!55))))
        (mk-some a!1))
      (mk-some ((as const (Array Bool (Maybe Bits_n))) (mk-some Bits_n!val!72))))))))))))))
  (define-fun k!1121 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 77) (mk-some true)
    (ite (= x!0 70) (mk-some true)
    (ite (= x!0 56) (mk-some true)
    (ite (= x!0 38) (mk-some true)
    (ite (= x!0 96) (mk-some true)
      (mk-some false)))))))
  (define-fun k!1094 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!0)
      (as mk-none (Maybe Bits_n))))
  (define-fun __func-Left-encn ((x!0 Bits_n) (x!1 Bits_n) (x!2 Bits_n)) Bits_m
    (ite (and (= x!0 Bits_n!val!9) (= x!1 Bits_n!val!16) (= x!2 Bits_n!val!2))
      Bits_m!val!1
    (ite (and (= x!0 Bits_n!val!13) (= x!1 Bits_n!val!0) (= x!2 Bits_n!val!4))
      Bits_m!val!2
    (ite (and (= x!0 Bits_n!val!13) (= x!1 Bits_n!val!16) (= x!2 Bits_n!val!5))
      Bits_m!val!3
    (ite (and (= x!0 Bits_n!val!9) (= x!1 Bits_n!val!0) (= x!2 Bits_n!val!8))
      Bits_m!val!4
    (ite (and (= x!0 Bits_n!val!9) (= x!1 Bits_n!val!16) (= x!2 Bits_n!val!10))
      Bits_m!val!5
    (ite (and (= x!0 Bits_n!val!13) (= x!1 Bits_n!val!0) (= x!2 Bits_n!val!12))
      Bits_m!val!6
    (ite (and (= x!0 Bits_n!val!13) (= x!1 Bits_n!val!16) (= x!2 Bits_n!val!14))
      Bits_m!val!7
      Bits_m!val!0))))))))
  (define-fun k!1122 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 49) (mk-some true)
    (ite (= x!0 92) (mk-some true)
    (ite (= x!0 71) (mk-some true)
    (ite (= x!0 58) (mk-some true)
    (ite (= x!0 48) (mk-some true)
    (ite (= x!0 72) (mk-some true)
    (ite (= x!0 53) (as mk-none (Maybe Bool))
    (ite (= x!0 80) (as mk-none (Maybe Bool))
    (ite (= x!0 100) (mk-some true)
      (mk-some false)))))))))))
)
sat
unknown
unknown
