; Keine aborts
  (define-fun is-abort-left () Bool
    false)
  (define-fun is-abort-right () Bool
    false)

; hhh is not the same as handle
  (define-fun hhh () Int
    99)
  (define-fun handle () Int
    97)

; Old key package state is completely different from new key package state - how can that be?
  (define-fun table-top-right-old () (Array Int (Maybe (Array Bool (Maybe Bits_n))))
    (_ as-array k!448))
  (define-fun table-top-right-new () (Array Int (Maybe (Array Bool (Maybe Bits_n))))
    (let ((a!1 ((as const (Array Int (Maybe (Array Bool (Maybe Bits_n)))))
             (mk-some ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!73)))))
      (a!2 (store (store ((as const (Array Bool (Maybe Bits_n)))
                           (mk-some Bits_n!val!24))
                         false
                         (as mk-none (Maybe Bits_n)))
                  true
                  (mk-some Bits_n!val!26)))
      (a!3 (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                             (mk-some Bits_n!val!34))
                           false
                           (mk-some Bits_n!val!36))))
      (a!4 (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                             (mk-some Bits_n!val!59))
                           false
                           (mk-some Bits_n!val!70))))
      (a!6 (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                             (mk-some Bits_n!val!54))
                           false
                           (mk-some Bits_n!val!47)))))
(let ((a!5 (store (store (store a!1 96 (mk-some a!2)) 92 a!3) 89 a!4)))
  (store (store a!5 106 (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
         72
         a!6))))


(
  ;; universe for Bits_n:
  ;;   Bits_n!val!47 Bits_n!val!38 Bits_n!val!65 Bits_n!val!25 Bits_n!val!70 Bits_n!val!78 Bits_n!val!3 Bits_n!val!15 Bits_n!val!39 Bits_n!val!66 Bits_n!val!24 Bits_n!val!11 Bits_n!val!41 Bits_n!val!29 Bits_n!val!53 Bits_n!val!77 Bits_n!val!46 Bits_n!val!31 Bits_n!val!28 Bits_n!val!1 Bits_n!val!33 Bits_n!val!51 Bits_n!val!10 Bits_n!val!74 Bits_n!val!61 Bits_n!val!22 Bits_n!val!35 Bits_n!val!0 Bits_n!val!27 Bits_n!val!20 Bits_n!val!5 Bits_n!val!9 Bits_n!val!4 Bits_n!val!13 Bits_n!val!32 Bits_n!val!7 Bits_n!val!40 Bits_n!val!26 Bits_n!val!50 Bits_n!val!57 Bits_n!val!17 Bits_n!val!34 Bits_n!val!37 Bits_n!val!19 Bits_n!val!59 Bits_n!val!71 Bits_n!val!75 Bits_n!val!64 Bits_n!val!30 Bits_n!val!54 Bits_n!val!56 Bits_n!val!76 Bits_n!val!49 Bits_n!val!14 Bits_n!val!43 Bits_n!val!68 Bits_n!val!36 Bits_n!val!12 Bits_n!val!23 Bits_n!val!45 Bits_n!val!48 Bits_n!val!58 Bits_n!val!63 Bits_n!val!72 Bits_n!val!6 Bits_n!val!52 Bits_n!val!55 Bits_n!val!44 Bits_n!val!67 Bits_n!val!16 Bits_n!val!18 Bits_n!val!60 Bits_n!val!21 Bits_n!val!73 Bits_n!val!69 Bits_n!val!42 Bits_n!val!8 Bits_n!val!2 Bits_n!val!62 
  ;; -----------
  ;; definitions for universe elements:
  (declare-fun Bits_n!val!47 () Bits_n)
  (declare-fun Bits_n!val!38 () Bits_n)
  (declare-fun Bits_n!val!65 () Bits_n)
  (declare-fun Bits_n!val!25 () Bits_n)
  (declare-fun Bits_n!val!70 () Bits_n)
  (declare-fun Bits_n!val!78 () Bits_n)
  (declare-fun Bits_n!val!3 () Bits_n)
  (declare-fun Bits_n!val!15 () Bits_n)
  (declare-fun Bits_n!val!39 () Bits_n)
  (declare-fun Bits_n!val!66 () Bits_n)
  (declare-fun Bits_n!val!24 () Bits_n)
  (declare-fun Bits_n!val!11 () Bits_n)
  (declare-fun Bits_n!val!41 () Bits_n)
  (declare-fun Bits_n!val!29 () Bits_n)
  (declare-fun Bits_n!val!53 () Bits_n)
  (declare-fun Bits_n!val!77 () Bits_n)
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
  (declare-fun Bits_n!val!75 () Bits_n)
  (declare-fun Bits_n!val!64 () Bits_n)
  (declare-fun Bits_n!val!30 () Bits_n)
  (declare-fun Bits_n!val!54 () Bits_n)
  (declare-fun Bits_n!val!56 () Bits_n)
  (declare-fun Bits_n!val!76 () Bits_n)
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
              (= x Bits_n!val!78)
              (= x Bits_n!val!3)
              (= x Bits_n!val!15)
              (= x Bits_n!val!39)
              (= x Bits_n!val!66)
              (= x Bits_n!val!24)
              (= x Bits_n!val!11)
              (= x Bits_n!val!41)
              (= x Bits_n!val!29)
              (= x Bits_n!val!53)
              (= x Bits_n!val!77)
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
              (= x Bits_n!val!75)
              (= x Bits_n!val!64)
              (= x Bits_n!val!30)
              (= x Bits_n!val!54)
              (= x Bits_n!val!56)
              (= x Bits_n!val!76)
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
  (define-fun ctr-rr-left-new () Int
    7719)
  (define-fun rr-right () Bits_n
    Bits_n!val!0)
  (define-fun postcondition-holds () Bool
    false)
  (define-fun ctr-r-right () Int
    504902)
  (define-fun table-bottom-left-old () (Array Int (Maybe (Array Bool (Maybe Bits_n))))
    (_ as-array k!461))
  (define-fun lemma1 () Bool
    false)
  (define-fun ctr-rr-right-new () Int
    7719)
  (define-fun table-bottom-right-new () (Array Int (Maybe (Array Bool (Maybe Bits_n))))
    (let ((a!1 ((as const (Array Int (Maybe (Array Bool (Maybe Bits_n)))))
             (mk-some ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!78)))))
      (a!2 (store (store ((as const (Array Bool (Maybe Bits_n)))
                           (mk-some Bits_n!val!45))
                         false
                         (mk-some Bits_n!val!58))
                  true
                  (mk-some Bits_n!val!65)))
      (a!3 (store (store ((as const (Array Bool (Maybe Bits_n)))
                           (mk-some Bits_n!val!39))
                         false
                         (mk-some Bits_n!val!31))
                  true
                  (mk-some Bits_n!val!50))))
  (store (store a!1 99 (mk-some a!2)) 95 (mk-some a!3))))
  (define-fun lemma3 () Bool
    false)
  (define-fun ctr-r-left-new () Int
    504902)
  (define-fun table-top-left-new () (Array Int (Maybe (Array Bool (Maybe Bits_n))))
    (let ((a!1 ((as const (Array Int (Maybe (Array Bool (Maybe Bits_n)))))
             (mk-some ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!71)))))
      (a!2 (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                             (mk-some Bits_n!val!53))
                           false
                           (mk-some Bits_n!val!66))))
      (a!3 (store (store ((as const (Array Bool (Maybe Bits_n)))
                           (mk-some Bits_n!val!32))
                         false
                         (mk-some Bits_n!val!51))
                  true
                  (mk-some Bits_n!val!62)))
      (a!4 (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                             (mk-some Bits_n!val!52))
                           false
                           (mk-some Bits_n!val!61))))
      (a!5 (store (store ((as const (Array Bool (Maybe Bits_n)))
                           (mk-some Bits_n!val!23))
                         false
                         (as mk-none (Maybe Bits_n)))
                  true
                  (mk-some Bits_n!val!13)))
      (a!7 (store (store ((as const (Array Bool (Maybe Bits_n)))
                           (mk-some Bits_n!val!27))
                         false
                         (mk-some Bits_n!val!11))
                  true
                  (mk-some Bits_n!val!28))))
(let ((a!6 (store (store (store (store a!1 91 a!2) 108 (mk-some a!3)) 92 a!4)
                  94
                  (mk-some a!5))))
  (store a!6 72 (mk-some a!7)))))
  (define-fun return-right () Return_Right_simgate_GBLG
    (let ((a!1 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         34
                         (mk-some true))
                  2
                  (mk-some true)))
      (a!3 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         2
                         (mk-some true))
                  32
                  (mk-some true)))
      (a!5 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         60
                         (mk-some true))
                  49
                  (mk-some true)))
      (a!8 ((as const (Array Int (Maybe (Array Bool (Maybe Bits_n)))))
             (mk-some ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!73)))))
      (a!9 (store (store ((as const (Array Bool (Maybe Bits_n)))
                           (mk-some Bits_n!val!24))
                         false
                         (as mk-none (Maybe Bits_n)))
                  true
                  (mk-some Bits_n!val!26)))
      (a!10 (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                              (mk-some Bits_n!val!34))
                            false
                            (mk-some Bits_n!val!36))))
      (a!11 (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                              (mk-some Bits_n!val!59))
                            false
                            (mk-some Bits_n!val!70))))
      (a!13 (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                              (mk-some Bits_n!val!54))
                            false
                            (mk-some Bits_n!val!47))))
      (a!14 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                          42
                          (mk-some true))
                   50
                   (mk-some true))))
(let ((a!2 (store (store (store a!1 101 (mk-some true)) 45 (mk-some true))
                  82
                  (mk-some true)))
      (a!4 (store (store (store a!3 44 (mk-some true)) 7 (mk-some true))
                  76
                  (mk-some true)))
      (a!6 (store (store (store a!5 51 (mk-some true)) 83 (mk-some true))
                  48
                  (mk-some true)))
      (a!12 (store (store (store a!8 96 (mk-some a!9)) 92 a!10) 89 a!11))
      (a!15 (store (store (store a!5 72 (mk-some true)) 83 (mk-some true))
                   51
                   (mk-some true))))
(let ((a!7 (mk-state-Right-keys_top
             (_ as-array k!448)
             (store (store a!2 7 (mk-some true)) 57 (mk-some true))
             a!4
             (store a!6 37 (mk-some true))))
      (a!16 (mk-state-Right-keys_bottom
              (store (store a!12
                            106
                            (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
                     72
                     a!13)
              (store (store a!14 75 (mk-some true))
                     72
                     (as mk-none (Maybe Bool)))
              (store (store a!15 37 (mk-some true)) 48 (mk-some true))
              (store a!6 37 (mk-some true)))))
  (mk-return-Right-simgate-GBLG
    (mk-composition-state-Right
      a!7
      a!16
      mk-state-Right-simgate
      mk-state-Right-ev
      Bits_n!val!19
      Bits_m!val!9
      16
      17
      18
      19
      20
      21
      504902
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
  (define-fun standard-postcondition-holds () Bool
    false)

  (define-fun state-left-new () CompositionState-Left
    (let ((a!1 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         22
                         (mk-some true))
                  53
                  (mk-some true)))
      (a!2 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         33
                         (mk-some true))
                  100
                  (mk-some true)))
      (a!4 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         26
                         (mk-some true))
                  38
                  (mk-some true)))
      (a!7 ((as const (Array Int (Maybe (Array Bool (Maybe Bits_n)))))
             (mk-some ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!71)))))
      (a!8 (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                             (mk-some Bits_n!val!53))
                           false
                           (mk-some Bits_n!val!66))))
      (a!9 (store (store ((as const (Array Bool (Maybe Bits_n)))
                           (mk-some Bits_n!val!32))
                         false
                         (mk-some Bits_n!val!51))
                  true
                  (mk-some Bits_n!val!62)))
      (a!10 (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                              (mk-some Bits_n!val!52))
                            false
                            (mk-some Bits_n!val!61))))
      (a!11 (store (store ((as const (Array Bool (Maybe Bits_n)))
                            (mk-some Bits_n!val!23))
                          false
                          (as mk-none (Maybe Bits_n)))
                   true
                   (mk-some Bits_n!val!13)))
      (a!13 (store (store ((as const (Array Bool (Maybe Bits_n)))
                            (mk-some Bits_n!val!27))
                          false
                          (mk-some Bits_n!val!11))
                   true
                   (mk-some Bits_n!val!28)))
      (a!14 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                          60
                          (mk-some true))
                   49
                   (mk-some true)))
      (a!16 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                          35
                          (mk-some true))
                   41
                   (mk-some true))))
(let ((a!3 (store (store (store a!2 46 (mk-some true)) 2 (mk-some true))
                  54
                  (mk-some true)))
      (a!5 (store (store (store a!4 78 (mk-some true)) 24 (mk-some true))
                  23
                  (mk-some true)))
      (a!12 (store (store (store (store a!7 91 a!8) 108 (mk-some a!9)) 92 a!10)
                   94
                   (mk-some a!11)))
      (a!15 (store (store (store a!14 72 (mk-some true)) 83 (mk-some true))
                   51
                   (mk-some true)))
      (a!17 (store (store (store a!16 73 (mk-some true)) 84 (mk-some true))
                   58
                   (mk-some true))))
(let ((a!6 (mk-state-Left-keys_top
             (_ as-array k!448)
             a!1
             (store (store a!3 28 (mk-some true)) 7 (mk-some true))
             (store a!5 77 (mk-some true))))
      (a!18 (mk-state-Left-keys_bottom
              (store a!12 72 (mk-some a!13))
              (_ as-array k!443)
              (store (store a!15 37 (mk-some true)) 48 (mk-some true))
              (store (store a!17 61 (mk-some true)) 102 (mk-some true)))))
  (mk-composition-state-Left
    a!6
    a!18
    mk-state-Left-gate
    mk-state-Left-enc
    Bits_m!val!8
    8
    9
    10
    Bits_n!val!17
    13
    14
    15
    504902
    7719
    476808
    489017)))))
  (define-fun ctr-r-right-new () Int
    504902)
  (define-fun lemmas-hold () Bool
    false)
  (define-fun state-left-old () CompositionState-Left
    (let ((a!1 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         22
                         (mk-some true))
                  53
                  (mk-some true)))
      (a!2 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         33
                         (mk-some true))
                  100
                  (mk-some true)))
      (a!4 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         26
                         (mk-some true))
                  38
                  (mk-some true)))
      (a!7 ((as const (Array Int (Maybe (Array Bool (Maybe Bits_n)))))
             (mk-some ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!71)))))
      (a!8 (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                             (mk-some Bits_n!val!53))
                           false
                           (mk-some Bits_n!val!66))))
      (a!9 (store (store ((as const (Array Bool (Maybe Bits_n)))
                           (mk-some Bits_n!val!32))
                         false
                         (mk-some Bits_n!val!51))
                  true
                  (mk-some Bits_n!val!62)))
      (a!10 (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                              (mk-some Bits_n!val!52))
                            false
                            (mk-some Bits_n!val!61))))
      (a!11 (store (store ((as const (Array Bool (Maybe Bits_n)))
                            (mk-some Bits_n!val!23))
                          false
                          (as mk-none (Maybe Bits_n)))
                   true
                   (mk-some Bits_n!val!13)))
      (a!13 (store (store ((as const (Array Bool (Maybe Bits_n)))
                            (mk-some Bits_n!val!27))
                          false
                          (mk-some Bits_n!val!11))
                   true
                   (mk-some Bits_n!val!28)))
      (a!14 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                          60
                          (mk-some true))
                   49
                   (mk-some true)))
      (a!16 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                          35
                          (mk-some true))
                   41
                   (mk-some true))))
(let ((a!3 (store (store (store a!2 46 (mk-some true)) 2 (mk-some true))
                  54
                  (mk-some true)))
      (a!5 (store (store (store a!4 78 (mk-some true)) 24 (mk-some true))
                  23
                  (mk-some true)))
      (a!12 (store (store (store (store a!7 91 a!8) 108 (mk-some a!9)) 92 a!10)
                   94
                   (mk-some a!11)))
      (a!15 (store (store (store a!14 51 (mk-some true)) 83 (mk-some true))
                   48
                   (mk-some true)))
      (a!17 (store (store (store a!16 73 (mk-some true)) 84 (mk-some true))
                   58
                   (mk-some true))))
(let ((a!6 (mk-state-Left-keys_top
             (_ as-array k!448)
             a!1
             (store (store a!3 28 (mk-some true)) 7 (mk-some true))
             (store a!5 77 (mk-some true))))
      (a!18 (mk-state-Left-keys_bottom
              (store a!12 72 (mk-some a!13))
              (_ as-array k!443)
              (store a!15 37 (mk-some true))
              (store (store a!17 61 (mk-some true)) 102 (mk-some true)))))
  (mk-composition-state-Left
    a!6
    a!18
    mk-state-Left-gate
    mk-state-Left-enc
    Bits_m!val!8
    8
    9
    10
    Bits_n!val!17
    13
    14
    15
    504902
    7719
    476800
    489013)))))
  (define-fun r-left () Bits_n
    Bits_n!val!22)
  (define-fun table-bottom-right-old () (Array Int (Maybe (Array Bool (Maybe Bits_n))))
    (_ as-array k!461))
  (define-fun value-right () (Array Bits_p (Maybe Bool))
    (store ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))
       Bits_p!val!4
       (mk-some true)))
  (define-fun table-top-left-old () (Array Int (Maybe (Array Bool (Maybe Bits_n))))
    (_ as-array k!448))
  (define-fun Z-right () (Array Bool (Maybe Bits_n))
    (store (store ((as const (Array Bool (Maybe Bits_n))) (mk-some Bits_n!val!75))
              false
              (mk-some Bits_n!val!0))
       true
       (mk-some Bits_n!val!22)))
  (define-fun r-right () Bits_n
    Bits_n!val!22)
  (define-fun return-left () Return_Left_gate_GBLG
    (let ((a!1 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         22
                         (mk-some true))
                  53
                  (mk-some true)))
      (a!2 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         33
                         (mk-some true))
                  100
                  (mk-some true)))
      (a!4 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         26
                         (mk-some true))
                  38
                  (mk-some true)))
      (a!7 ((as const (Array Int (Maybe (Array Bool (Maybe Bits_n)))))
             (mk-some ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!71)))))
      (a!8 (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                             (mk-some Bits_n!val!53))
                           false
                           (mk-some Bits_n!val!66))))
      (a!9 (store (store ((as const (Array Bool (Maybe Bits_n)))
                           (mk-some Bits_n!val!32))
                         false
                         (mk-some Bits_n!val!51))
                  true
                  (mk-some Bits_n!val!62)))
      (a!10 (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                              (mk-some Bits_n!val!52))
                            false
                            (mk-some Bits_n!val!61))))
      (a!11 (store (store ((as const (Array Bool (Maybe Bits_n)))
                            (mk-some Bits_n!val!23))
                          false
                          (as mk-none (Maybe Bits_n)))
                   true
                   (mk-some Bits_n!val!13)))
      (a!13 (store (store ((as const (Array Bool (Maybe Bits_n)))
                            (mk-some Bits_n!val!27))
                          false
                          (mk-some Bits_n!val!11))
                   true
                   (mk-some Bits_n!val!28)))
      (a!14 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                          60
                          (mk-some true))
                   49
                   (mk-some true)))
      (a!16 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                          35
                          (mk-some true))
                   41
                   (mk-some true))))
(let ((a!3 (store (store (store a!2 46 (mk-some true)) 2 (mk-some true))
                  54
                  (mk-some true)))
      (a!5 (store (store (store a!4 78 (mk-some true)) 24 (mk-some true))
                  23
                  (mk-some true)))
      (a!12 (store (store (store (store a!7 91 a!8) 108 (mk-some a!9)) 92 a!10)
                   94
                   (mk-some a!11)))
      (a!15 (store (store (store a!14 72 (mk-some true)) 83 (mk-some true))
                   51
                   (mk-some true)))
      (a!17 (store (store (store a!16 73 (mk-some true)) 84 (mk-some true))
                   58
                   (mk-some true))))
(let ((a!6 (mk-state-Left-keys_top
             (_ as-array k!448)
             a!1
             (store (store a!3 28 (mk-some true)) 7 (mk-some true))
             (store a!5 77 (mk-some true))))
      (a!18 (mk-state-Left-keys_bottom
              (store a!12 72 (mk-some a!13))
              (_ as-array k!443)
              (store (store a!15 37 (mk-some true)) 48 (mk-some true))
              (store (store a!17 61 (mk-some true)) 102 (mk-some true)))))
  (mk-return-Left-gate-GBLG
    (mk-composition-state-Left
      a!6
      a!18
      mk-state-Left-gate
      mk-state-Left-enc
      Bits_m!val!8
      8
      9
      10
      Bits_n!val!17
      13
      14
      15
      504902
      7719
      476808
      489017)
    (store ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))
           Bits_p!val!3
           (mk-some true)))))))
  (define-fun ctr-r-left () Int
    504902)
  (define-fun r () Int
    7)
  (define-fun state-right-old () CompositionState-Right
    (let ((a!1 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         34
                         (mk-some true))
                  2
                  (mk-some true)))
      (a!3 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         2
                         (mk-some true))
                  32
                  (mk-some true)))
      (a!5 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         60
                         (mk-some true))
                  49
                  (mk-some true)))
      (a!8 ((as const (Array Int (Maybe (Array Bool (Maybe Bits_n)))))
             (mk-some ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!73)))))
      (a!9 (store (store ((as const (Array Bool (Maybe Bits_n)))
                           (mk-some Bits_n!val!24))
                         false
                         (as mk-none (Maybe Bits_n)))
                  true
                  (mk-some Bits_n!val!26)))
      (a!10 (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                              (mk-some Bits_n!val!34))
                            false
                            (mk-some Bits_n!val!36))))
      (a!11 (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                              (mk-some Bits_n!val!59))
                            false
                            (mk-some Bits_n!val!70))))
      (a!13 (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                              (mk-some Bits_n!val!54))
                            false
                            (mk-some Bits_n!val!47))))
      (a!14 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                          42
                          (mk-some true))
                   50
                   (mk-some true))))
(let ((a!2 (store (store (store a!1 101 (mk-some true)) 45 (mk-some true))
                  82
                  (mk-some true)))
      (a!4 (store (store (store a!3 44 (mk-some true)) 7 (mk-some true))
                  76
                  (mk-some true)))
      (a!6 (store (store (store a!5 51 (mk-some true)) 83 (mk-some true))
                  48
                  (mk-some true)))
      (a!12 (store (store (store a!8 96 (mk-some a!9)) 92 a!10) 89 a!11)))
(let ((a!7 (mk-state-Right-keys_top
             (_ as-array k!448)
             (store (store a!2 7 (mk-some true)) 57 (mk-some true))
             a!4
             (store a!6 37 (mk-some true))))
      (a!15 (mk-state-Right-keys_bottom
              (store (store a!12
                            106
                            (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
                     72
                     a!13)
              (store (store a!14 75 (mk-some true))
                     72
                     (as mk-none (Maybe Bool)))
              (store a!6 37 (mk-some true))
              (store a!6 37 (mk-some true)))))
  (mk-composition-state-Right
    a!7
    a!15
    mk-state-Right-simgate
    mk-state-Right-ev
    Bits_n!val!19
    Bits_m!val!9
    16
    17
    18
    19
    20
    21
    504902
    7719
    21238
    2437
    8855
    11797
    8365
    32285
    10450
    30612)))))
  (define-fun ctr-rr-left () Int
    7719)
  (define-fun Z-left () (Array Bool (Maybe Bits_n))
    (store (store ((as const (Array Bool (Maybe Bits_n))) (mk-some Bits_n!val!74))
              false
              (mk-some Bits_n!val!0))
       true
       (mk-some Bits_n!val!22)))
  (define-fun ctr-rr-right () Int
    7719)
  (define-fun l () Int
    2)
  (define-fun j () Int
    72)
  (define-fun value-left () (Array Bits_p (Maybe Bool))
    (store ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))
       Bits_p!val!3
       (mk-some true)))
  (define-fun lemma2 () Bool
    false)
  (define-fun rr-left () Bits_n
    Bits_n!val!0)
  (define-fun state-right-new () CompositionState-Right
    (let ((a!1 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         34
                         (mk-some true))
                  2
                  (mk-some true)))
      (a!3 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         2
                         (mk-some true))
                  32
                  (mk-some true)))
      (a!5 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         60
                         (mk-some true))
                  49
                  (mk-some true)))
      (a!8 ((as const (Array Int (Maybe (Array Bool (Maybe Bits_n)))))
             (mk-some ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!73)))))
      (a!9 (store (store ((as const (Array Bool (Maybe Bits_n)))
                           (mk-some Bits_n!val!24))
                         false
                         (as mk-none (Maybe Bits_n)))
                  true
                  (mk-some Bits_n!val!26)))
      (a!10 (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                              (mk-some Bits_n!val!34))
                            false
                            (mk-some Bits_n!val!36))))
      (a!11 (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                              (mk-some Bits_n!val!59))
                            false
                            (mk-some Bits_n!val!70))))
      (a!13 (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                              (mk-some Bits_n!val!54))
                            false
                            (mk-some Bits_n!val!47))))
      (a!14 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                          42
                          (mk-some true))
                   50
                   (mk-some true))))
(let ((a!2 (store (store (store a!1 101 (mk-some true)) 45 (mk-some true))
                  82
                  (mk-some true)))
      (a!4 (store (store (store a!3 44 (mk-some true)) 7 (mk-some true))
                  76
                  (mk-some true)))
      (a!6 (store (store (store a!5 51 (mk-some true)) 83 (mk-some true))
                  48
                  (mk-some true)))
      (a!12 (store (store (store a!8 96 (mk-some a!9)) 92 a!10) 89 a!11))
      (a!15 (store (store (store a!5 72 (mk-some true)) 83 (mk-some true))
                   51
                   (mk-some true))))
(let ((a!7 (mk-state-Right-keys_top
             (_ as-array k!448)
             (store (store a!2 7 (mk-some true)) 57 (mk-some true))
             a!4
             (store a!6 37 (mk-some true))))
      (a!16 (mk-state-Right-keys_bottom
              (store (store a!12
                            106
                            (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
                     72
                     a!13)
              (store (store a!14 75 (mk-some true))
                     72
                     (as mk-none (Maybe Bool)))
              (store (store a!15 37 (mk-some true)) 48 (mk-some true))
              (store a!6 37 (mk-some true)))))
  (mk-composition-state-Right
    a!7
    a!16
    mk-state-Right-simgate
    mk-state-Right-ev
    Bits_n!val!19
    Bits_m!val!9
    16
    17
    18
    19
    20
    21
    504902
    7719
    21239
    2438
    8856
    11798
    8366
    32286
    10451
    30613)))))
  (define-fun op () (Array (Tuple2 Bool Bool) (Maybe Bool))
    ((as const (Array (Tuple2 Bool Bool) (Maybe Bool))) (mk-some false)))
  (define-fun table-bottom-left-new () (Array Int (Maybe (Array Bool (Maybe Bits_n))))
    (let ((a!1 ((as const (Array Int (Maybe (Array Bool (Maybe Bits_n)))))
             (mk-some ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!77)))))
      (a!2 (store (store ((as const (Array Bool (Maybe Bits_n)))
                           (mk-some Bits_n!val!24))
                         false
                         (as mk-none (Maybe Bits_n)))
                  true
                  (mk-some Bits_n!val!26)))
      (a!3 (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                             (mk-some Bits_n!val!55))
                           false
                           (mk-some Bits_n!val!67)))))
  (store (store a!1 93 (mk-some a!2)) 98 a!3)))
  (define-fun precondition-holds () Bool
    true)
  (define-fun lemma4 () Bool
    false)
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
  (define-fun k!412 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!31)
    (ite (= x!0 true) (mk-some Bits_n!val!50)
      (mk-some Bits_n!val!39))))
  (define-fun k!447 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 22) (mk-some true)
    (ite (= x!0 53) (mk-some true)
      (mk-some false))))
  (define-fun k!427 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!49)
      (mk-some Bits_n!val!44)))
  (define-fun k!420 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!57)
    (ite (= x!0 true) (mk-some Bits_n!val!68)
      (mk-some Bits_n!val!40))))
  (define-fun k!413 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!47)
      (mk-some Bits_n!val!54)))
  (define-fun k!455 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 42) (mk-some true)
    (ite (= x!0 50) (mk-some true)
    (ite (= x!0 75) (mk-some true)
    (ite (= x!0 72) (as mk-none (Maybe Bool))
      (mk-some false))))))
  (define-fun k!441 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 35) (mk-some true)
    (ite (= x!0 41) (mk-some true)
    (ite (= x!0 73) (mk-some true)
    (ite (= x!0 84) (mk-some true)
    (ite (= x!0 58) (mk-some true)
    (ite (= x!0 61) (mk-some true)
    (ite (= x!0 102) (mk-some true)
      (mk-some false)))))))))
  (define-fun __sample-rand-Right-Bits_n ((x!0 Int) (x!1 Int)) Bits_n
    (ite (and (= x!0 12) (= x!1 30612)) Bits_n!val!21
    (ite (and (= x!0 3) (= x!1 504902)) Bits_n!val!22
    (ite (and (= x!0 4) (= x!1 7719)) Bits_n!val!0
      Bits_n!val!20))))
  (define-fun k!428 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!25)
      (mk-some Bits_n!val!29)))
  (define-fun k!451 ((x!0 Int)) (Maybe (Array Bool (Maybe Bits_n)))
    (ite (= x!0 91)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!53))
                      false
                      (mk-some Bits_n!val!66)))
    (ite (= x!0 108)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!32))
                               false
                               (mk-some Bits_n!val!51))
                        true
                        (mk-some Bits_n!val!62))))
        (mk-some a!1))
    (ite (= x!0 92)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!52))
                      false
                      (mk-some Bits_n!val!61)))
    (ite (= x!0 94)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!23))
                               false
                               (as mk-none (Maybe Bits_n)))
                        true
                        (mk-some Bits_n!val!13))))
        (mk-some a!1))
    (ite (= x!0 72)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (as mk-none (Maybe Bits_n)))
                      false
                      (mk-some Bits_n!val!0)))
      (mk-some ((as const (Array Bool (Maybe Bits_n))) (mk-some Bits_n!val!71)))))))))
  (define-fun k!421 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (as mk-none (Maybe Bits_n))
    (ite (= x!0 true) (mk-some Bits_n!val!26)
      (mk-some Bits_n!val!24))))
  (define-fun k!444 ((x!0 Int)) (Maybe (Array Bool (Maybe Bits_n)))
    (ite (= x!0 91)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!53))
                      false
                      (mk-some Bits_n!val!66)))
    (ite (= x!0 108)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!32))
                               false
                               (mk-some Bits_n!val!51))
                        true
                        (mk-some Bits_n!val!62))))
        (mk-some a!1))
    (ite (= x!0 92)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!52))
                      false
                      (mk-some Bits_n!val!61)))
    (ite (= x!0 94)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!23))
                               false
                               (as mk-none (Maybe Bits_n)))
                        true
                        (mk-some Bits_n!val!13))))
        (mk-some a!1))
    (ite (= x!0 72)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!27))
                               false
                               (mk-some Bits_n!val!11))
                        true
                        (mk-some Bits_n!val!28))))
        (mk-some a!1))
      (mk-some ((as const (Array Bool (Maybe Bits_n))) (mk-some Bits_n!val!71)))))))))
  (define-fun k!414 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!36)
      (mk-some Bits_n!val!34)))
  (define-fun k!449 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 60) (mk-some true)
    (ite (= x!0 49) (mk-some true)
    (ite (= x!0 51) (mk-some true)
    (ite (= x!0 83) (mk-some true)
    (ite (= x!0 48) (mk-some true)
    (ite (= x!0 37) (mk-some true)
      (mk-some false))))))))
  (define-fun k!442 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 60) (mk-some true)
    (ite (= x!0 49) (mk-some true)
    (ite (= x!0 72) (mk-some true)
    (ite (= x!0 83) (mk-some true)
    (ite (= x!0 51) (mk-some true)
    (ite (= x!0 37) (mk-some true)
    (ite (= x!0 48) (mk-some true)
      (mk-some false)))))))))
  (define-fun k!429 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!70)
      (mk-some Bits_n!val!59)))
  (define-fun k!422 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!60)
      (mk-some Bits_n!val!69)))
  (define-fun k!415 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!30)
      (mk-some Bits_n!val!56)))
  (define-fun __func-Right-encm ((x!0 Bits_n) (x!1 Bits_m) (x!2 Bits_n)) Bits_p
    Bits_p!val!4)
  (define-fun k!457 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 2) (mk-some true)
    (ite (= x!0 32) (mk-some true)
    (ite (= x!0 44) (mk-some true)
    (ite (= x!0 7) (mk-some true)
    (ite (= x!0 76) (mk-some true)
      (mk-some false)))))))
  (define-fun k!443 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 39) (mk-some true)
    (ite (= x!0 81) (mk-some true)
    (ite (= x!0 30) (mk-some true)
    (ite (= x!0 29) (mk-some true)
    (ite (= x!0 31) (mk-some true)
    (ite (= x!0 55) (mk-some true)
    (ite (= x!0 80) (mk-some true)
    (ite (= x!0 79) (mk-some true)
      (mk-some false))))))))))
  (define-fun __func-Left-encm ((x!0 Bits_n) (x!1 Bits_m) (x!2 Bits_n)) Bits_p
    (ite (and (= x!0 Bits_n!val!18) (= x!1 Bits_m!val!3) (= x!2 Bits_n!val!6))
      Bits_p!val!1
    (ite (and (= x!0 Bits_n!val!15) (= x!1 Bits_m!val!5) (= x!2 Bits_n!val!10))
      Bits_p!val!2
    (ite (and (= x!0 Bits_n!val!15) (= x!1 Bits_m!val!7) (= x!2 Bits_n!val!16))
      Bits_p!val!3
      Bits_p!val!0))))
  (define-fun k!430 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (as mk-none (Maybe Bits_n))
    (ite (= x!0 true) (mk-some Bits_n!val!13)
      (mk-some Bits_n!val!23))))
  (define-fun k!423 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!35)
      (mk-some Bits_n!val!43)))
  (define-fun k!416 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!61)
      (mk-some Bits_n!val!52)))
  (define-fun __sample-rand-Left-Bits_n ((x!0 Int) (x!1 Int)) Bits_n
    (ite (and (= x!0 5) (= x!1 476800)) Bits_n!val!1
    (ite (and (= x!0 5) (= x!1 476801)) Bits_n!val!2
    (ite (and (= x!0 6) (= x!1 489013)) Bits_n!val!3
    (ite (and (= x!0 5) (= x!1 476802)) Bits_n!val!4
    (ite (and (= x!0 5) (= x!1 476803)) Bits_n!val!5
    (ite (and (= x!0 6) (= x!1 489014)) Bits_n!val!6
    (ite (and (= x!0 5) (= x!1 476804)) Bits_n!val!7
    (ite (and (= x!0 5) (= x!1 476805)) Bits_n!val!9
    (ite (and (= x!0 6) (= x!1 489015)) Bits_n!val!10
    (ite (and (= x!0 5) (= x!1 476806)) Bits_n!val!12
    (ite (and (= x!0 5) (= x!1 476807)) Bits_n!val!14
    (ite (and (= x!0 6) (= x!1 489016)) Bits_n!val!16
    (ite (and (= x!0 3) (= x!1 504902)) Bits_n!val!22
      Bits_n!val!0))))))))))))))
  (define-fun k!458 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 34) (mk-some true)
    (ite (= x!0 2) (mk-some true)
    (ite (= x!0 101) (mk-some true)
    (ite (= x!0 45) (mk-some true)
    (ite (= x!0 82) (mk-some true)
    (ite (= x!0 7) (mk-some true)
    (ite (= x!0 57) (mk-some true)
      (mk-some false)))))))))
  (define-fun k!461 ((x!0 Int)) (Maybe (Array Bool (Maybe Bits_n)))
    (ite (= x!0 87) (as mk-none (Maybe (Array Bool (Maybe Bits_n))))
    (ite (= x!0 88)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!56))
                      false
                      (mk-some Bits_n!val!30)))
    (ite (= x!0 108) (as mk-none (Maybe (Array Bool (Maybe Bits_n))))
    (ite (= x!0 99)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!69))
                      false
                      (mk-some Bits_n!val!60)))
    (ite (= x!0 106)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!40))
                               false
                               (mk-some Bits_n!val!57))
                        true
                        (mk-some Bits_n!val!68))))
        (mk-some a!1))
    (ite (= x!0 98)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!43))
                      false
                      (mk-some Bits_n!val!35)))
    (ite (= x!0 72) (as mk-none (Maybe (Array Bool (Maybe Bits_n))))
    (ite (= x!0 107)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!63))
                      false
                      (mk-some Bits_n!val!41)))
      (mk-some ((as const (Array Bool (Maybe Bits_n))) (mk-some Bits_n!val!76))))))))))))
  (define-fun k!431 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!18)
    (ite (= x!0 true) (mk-some Bits_n!val!15)
      (mk-some Bits_n!val!33))))
  (define-fun k!424 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!37)
      (mk-some Bits_n!val!46)))
  (define-fun k!417 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!51)
    (ite (= x!0 true) (mk-some Bits_n!val!62)
      (mk-some Bits_n!val!32))))
  (define-fun k!410 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!58)
    (ite (= x!0 true) (mk-some Bits_n!val!65)
      (mk-some Bits_n!val!45))))
  (define-fun k!445 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 26) (mk-some true)
    (ite (= x!0 38) (mk-some true)
    (ite (= x!0 78) (mk-some true)
    (ite (= x!0 24) (mk-some true)
    (ite (= x!0 23) (mk-some true)
    (ite (= x!0 77) (mk-some true)
      (mk-some false))))))))
  (define-fun k!432 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!0)
      (as mk-none (Maybe Bits_n))))
  (define-fun k!425 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!64)
      (mk-some Bits_n!val!42)))
  (define-fun k!448 ((x!0 Int)) (Maybe (Array Bool (Maybe Bits_n)))
    (ite (= x!0 86) (as mk-none (Maybe (Array Bool (Maybe Bits_n))))
    (ite (= x!0 85) (as mk-none (Maybe (Array Bool (Maybe Bits_n))))
    (ite (= x!0 72)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!46))
                      false
                      (mk-some Bits_n!val!37)))
    (ite (= x!0 7)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!33))
                               false
                               (mk-some Bits_n!val!18))
                        true
                        (mk-some Bits_n!val!15))))
        (mk-some a!1))
    (ite (= x!0 90)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!44))
                      false
                      (mk-some Bits_n!val!49)))
    (ite (= x!0 91)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!42))
                      false
                      (mk-some Bits_n!val!64)))
    (ite (= x!0 89)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!29))
                      false
                      (mk-some Bits_n!val!25)))
    (ite (= x!0 2) (as mk-none (Maybe (Array Bool (Maybe Bits_n))))
    (ite (= x!0 107)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!48))
                      false
                      (mk-some Bits_n!val!38)))
      (mk-some ((as const (Array Bool (Maybe Bits_n))) (mk-some Bits_n!val!72)))))))))))))
  (define-fun k!418 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!38)
      (mk-some Bits_n!val!48)))
  (define-fun __func-Right-encn ((x!0 Bits_n) (x!1 Bits_n) (x!2 Bits_n)) Bits_m
    Bits_m!val!10)
  (define-fun k!411 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!67)
      (mk-some Bits_n!val!55)))
  (define-fun k!446 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 33) (mk-some true)
    (ite (= x!0 100) (mk-some true)
    (ite (= x!0 46) (mk-some true)
    (ite (= x!0 2) (mk-some true)
    (ite (= x!0 54) (mk-some true)
    (ite (= x!0 28) (mk-some true)
    (ite (= x!0 7) (mk-some true)
      (mk-some false)))))))))
  (define-fun k!433 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!11)
    (ite (= x!0 true) (mk-some Bits_n!val!28)
      (mk-some Bits_n!val!27))))
  (define-fun k!456 ((x!0 Int)) (Maybe (Array Bool (Maybe Bits_n)))
    (ite (= x!0 96)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!24))
                               false
                               (as mk-none (Maybe Bits_n)))
                        true
                        (mk-some Bits_n!val!26))))
        (mk-some a!1))
    (ite (= x!0 92)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!34))
                      false
                      (mk-some Bits_n!val!36)))
    (ite (= x!0 89)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!59))
                      false
                      (mk-some Bits_n!val!70)))
    (ite (= x!0 106) (as mk-none (Maybe (Array Bool (Maybe Bits_n))))
    (ite (= x!0 72)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!54))
                      false
                      (mk-some Bits_n!val!47)))
      (mk-some ((as const (Array Bool (Maybe Bits_n))) (mk-some Bits_n!val!73)))))))))
  (define-fun k!426 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!66)
      (mk-some Bits_n!val!53)))
  (define-fun __func-Left-encn ((x!0 Bits_n) (x!1 Bits_n) (x!2 Bits_n)) Bits_m
    (ite (and (= x!0 Bits_n!val!8) (= x!1 Bits_n!val!17) (= x!2 Bits_n!val!2))
      Bits_m!val!1
    (ite (and (= x!0 Bits_n!val!13) (= x!1 Bits_n!val!11) (= x!2 Bits_n!val!4))
      Bits_m!val!2
    (ite (and (= x!0 Bits_n!val!13) (= x!1 Bits_n!val!17) (= x!2 Bits_n!val!5))
      Bits_m!val!3
    (ite (and (= x!0 Bits_n!val!8) (= x!1 Bits_n!val!11) (= x!2 Bits_n!val!7))
      Bits_m!val!4
    (ite (and (= x!0 Bits_n!val!8) (= x!1 Bits_n!val!17) (= x!2 Bits_n!val!9))
      Bits_m!val!5
    (ite (and (= x!0 Bits_n!val!13) (= x!1 Bits_n!val!11) (= x!2 Bits_n!val!12))
      Bits_m!val!6
    (ite (and (= x!0 Bits_n!val!13) (= x!1 Bits_n!val!17) (= x!2 Bits_n!val!14))
      Bits_m!val!7
      Bits_m!val!0))))))))
  (define-fun k!419 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!41)
      (mk-some Bits_n!val!63)))
)
sat
sat
sat
sat
sat
unsat
