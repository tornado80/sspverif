  (define-fun table-bottom-left-new () (Array Int (Maybe (Array Bool (Maybe Bits_n))))
    (_ as-array k!4827))

  (define-fun table-bottom-right-new () (Array Int (Maybe (Array Bool (Maybe Bits_n))))
    (_ as-array k!4827))

  (define-fun table-bottom-right-old () (Array Int (Maybe (Array Bool (Maybe Bits_n))))
    (_ as-array k!4827))

  (define-fun table-bottom-left-new () (Array Int (Maybe (Array Bool (Maybe Bits_n))))
    (_ as-array k!4827))

(
  ;; universe for Bits_n:
  ;;   Bits_n!val!71 Bits_n!val!74 Bits_n!val!48 Bits_n!val!77 Bits_n!val!2 Bits_n!val!19 Bits_n!val!50 Bits_n!val!1 Bits_n!val!39 Bits_n!val!13 Bits_n!val!20 Bits_n!val!31 Bits_n!val!47 Bits_n!val!7 Bits_n!val!57 Bits_n!val!41 Bits_n!val!60 Bits_n!val!30 
Bits_n!val!34 Bits_n!val!0 Bits_n!val!33 Bits_n!val!66 Bits_n!val!75 Bits_n!val!11 Bits_n!val!17 Bits_n!val!43 Bits_n!val!25 Bits_n!val!68 Bits_n!val!45 Bits_n!val!22 Bits_n!val!29 Bits_n!val!32 Bits_n!val!37 Bits_n!val!62 Bits_n!val!14 Bits_n!val!53 Bits_n!val!78 Bits_n!val!79 Bits_n!val!69 Bits_n!val!27 Bits_n!val!42 Bits_n!val!56 Bits_n!val!55 Bits_n!val!46 Bits_n!val!52 Bits_n!val!76 Bits_n!val!6 Bits_n!val!10 Bits_n!val!26 Bits_n!val!63 Bits_n!val!8 Bits_n!val!80 Bits_n!val!18 Bits_n!val!51 Bits_n!val!64 Bits_n!val!36 Bits_n!val!65 Bits_n!val!3 Bits_n!val!28 Bits_n!val!61 Bits_n!val!73 Bits_n!val!59 Bits_n!val!58 Bits_n!val!23 
Bits_n!val!72 Bits_n!val!44 Bits_n!val!12 Bits_n!val!15 Bits_n!val!4 Bits_n!val!16 Bits_n!val!38 Bits_n!val!54 Bits_n!val!40 Bits_n!val!67 Bits_n!val!21 Bits_n!val!5 Bits_n!val!49 Bits_n!val!24 Bits_n!val!35 Bits_n!val!9 Bits_n!val!70 
  ;; -----------
  ;; definitions for universe elements:
  (declare-fun Bits_n!val!71 () Bits_n)
  (declare-fun Bits_n!val!74 () Bits_n)
  (declare-fun Bits_n!val!48 () Bits_n)
  (declare-fun Bits_n!val!77 () Bits_n)
  (declare-fun Bits_n!val!2 () Bits_n)
  (declare-fun Bits_n!val!19 () Bits_n)
  (declare-fun Bits_n!val!50 () Bits_n)
  (declare-fun Bits_n!val!1 () Bits_n)
  (declare-fun Bits_n!val!39 () Bits_n)
  (declare-fun Bits_n!val!13 () Bits_n)
  (declare-fun Bits_n!val!20 () Bits_n)
  (declare-fun Bits_n!val!31 () Bits_n)
  (declare-fun Bits_n!val!47 () Bits_n)
  (declare-fun Bits_n!val!7 () Bits_n)
  (declare-fun Bits_n!val!57 () Bits_n)
  (declare-fun Bits_n!val!41 () Bits_n)
  (declare-fun Bits_n!val!60 () Bits_n)
  (declare-fun Bits_n!val!30 () Bits_n)
  (declare-fun Bits_n!val!34 () Bits_n)
  (declare-fun Bits_n!val!0 () Bits_n)
  (declare-fun Bits_n!val!33 () Bits_n)
  (declare-fun Bits_n!val!66 () Bits_n)
  (declare-fun Bits_n!val!75 () Bits_n)
  (declare-fun Bits_n!val!11 () Bits_n)
  (declare-fun Bits_n!val!17 () Bits_n)
  (declare-fun Bits_n!val!43 () Bits_n)
  (declare-fun Bits_n!val!25 () Bits_n)
  (declare-fun Bits_n!val!68 () Bits_n)
  (declare-fun Bits_n!val!45 () Bits_n)
  (declare-fun Bits_n!val!22 () Bits_n)
  (declare-fun Bits_n!val!29 () Bits_n)
  (declare-fun Bits_n!val!32 () Bits_n)
  (declare-fun Bits_n!val!37 () Bits_n)
  (declare-fun Bits_n!val!62 () Bits_n)
  (declare-fun Bits_n!val!14 () Bits_n)
  (declare-fun Bits_n!val!53 () Bits_n)
  (declare-fun Bits_n!val!78 () Bits_n)
  (declare-fun Bits_n!val!79 () Bits_n)
  (declare-fun Bits_n!val!69 () Bits_n)
  (declare-fun Bits_n!val!27 () Bits_n)
  (declare-fun Bits_n!val!42 () Bits_n)
  (declare-fun Bits_n!val!56 () Bits_n)
  (declare-fun Bits_n!val!55 () Bits_n)
  (declare-fun Bits_n!val!46 () Bits_n)
  (declare-fun Bits_n!val!52 () Bits_n)
  (declare-fun Bits_n!val!76 () Bits_n)
  (declare-fun Bits_n!val!6 () Bits_n)
  (declare-fun Bits_n!val!10 () Bits_n)
  (declare-fun Bits_n!val!26 () Bits_n)
  (declare-fun Bits_n!val!63 () Bits_n)
  (declare-fun Bits_n!val!8 () Bits_n)
  (declare-fun Bits_n!val!80 () Bits_n)
  (declare-fun Bits_n!val!18 () Bits_n)
  (declare-fun Bits_n!val!51 () Bits_n)
  (declare-fun Bits_n!val!64 () Bits_n)
  (declare-fun Bits_n!val!36 () Bits_n)
  (declare-fun Bits_n!val!65 () Bits_n)
  (declare-fun Bits_n!val!3 () Bits_n)
  (declare-fun Bits_n!val!28 () Bits_n)
  (declare-fun Bits_n!val!61 () Bits_n)
  (declare-fun Bits_n!val!73 () Bits_n)
  (declare-fun Bits_n!val!59 () Bits_n)
  (declare-fun Bits_n!val!58 () Bits_n)
  (declare-fun Bits_n!val!23 () Bits_n)
  (declare-fun Bits_n!val!72 () Bits_n)
  (declare-fun Bits_n!val!44 () Bits_n)
  (declare-fun Bits_n!val!12 () Bits_n)
  (declare-fun Bits_n!val!15 () Bits_n)
  (declare-fun Bits_n!val!4 () Bits_n)
  (declare-fun Bits_n!val!16 () Bits_n)
  (declare-fun Bits_n!val!38 () Bits_n)
  (declare-fun Bits_n!val!54 () Bits_n)
  (declare-fun Bits_n!val!40 () Bits_n)
  (declare-fun Bits_n!val!67 () Bits_n)
  (declare-fun Bits_n!val!21 () Bits_n)
  (declare-fun Bits_n!val!5 () Bits_n)
  (declare-fun Bits_n!val!49 () Bits_n)
  (declare-fun Bits_n!val!24 () Bits_n)
  (declare-fun Bits_n!val!35 () Bits_n)
  (declare-fun Bits_n!val!9 () Bits_n)
  (declare-fun Bits_n!val!70 () Bits_n)
  ;; cardinality constraint:
  (forall ((x Bits_n))
          (or (= x Bits_n!val!71)
              (= x Bits_n!val!74)
              (= x Bits_n!val!48)
              (= x Bits_n!val!77)
              (= x Bits_n!val!2)
              (= x Bits_n!val!19)
              (= x Bits_n!val!50)
              (= x Bits_n!val!1)
              (= x Bits_n!val!39)
              (= x Bits_n!val!13)
              (= x Bits_n!val!20)
              (= x Bits_n!val!31)
              (= x Bits_n!val!47)
              (= x Bits_n!val!7)
              (= x Bits_n!val!57)
              (= x Bits_n!val!41)
              (= x Bits_n!val!60)
              (= x Bits_n!val!30)
              (= x Bits_n!val!34)
              (= x Bits_n!val!0)
              (= x Bits_n!val!33)
              (= x Bits_n!val!66)
              (= x Bits_n!val!75)
              (= x Bits_n!val!11)
              (= x Bits_n!val!17)
              (= x Bits_n!val!43)
              (= x Bits_n!val!25)
              (= x Bits_n!val!68)
              (= x Bits_n!val!45)
              (= x Bits_n!val!22)
              (= x Bits_n!val!29)
              (= x Bits_n!val!32)
              (= x Bits_n!val!37)
              (= x Bits_n!val!62)
              (= x Bits_n!val!14)
              (= x Bits_n!val!53)
              (= x Bits_n!val!78)
              (= x Bits_n!val!79)
              (= x Bits_n!val!69)
              (= x Bits_n!val!27)
              (= x Bits_n!val!42)
              (= x Bits_n!val!56)
              (= x Bits_n!val!55)
              (= x Bits_n!val!46)
              (= x Bits_n!val!52)
              (= x Bits_n!val!76)
              (= x Bits_n!val!6)
              (= x Bits_n!val!10)
              (= x Bits_n!val!26)
              (= x Bits_n!val!63)
              (= x Bits_n!val!8)
              (= x Bits_n!val!80)
              (= x Bits_n!val!18)
              (= x Bits_n!val!51)
              (= x Bits_n!val!64)
              (= x Bits_n!val!36)
              (= x Bits_n!val!65)
              (= x Bits_n!val!3)
              (= x Bits_n!val!28)
              (= x Bits_n!val!61)
              (= x Bits_n!val!73)
              (= x Bits_n!val!59)
              (= x Bits_n!val!58)
              (= x Bits_n!val!23)
              (= x Bits_n!val!72)
              (= x Bits_n!val!44)
              (= x Bits_n!val!12)
              (= x Bits_n!val!15)
              (= x Bits_n!val!4)
              (= x Bits_n!val!16)
              (= x Bits_n!val!38)
              (= x Bits_n!val!54)
              (= x Bits_n!val!40)
              (= x Bits_n!val!67)
              (= x Bits_n!val!21)
              (= x Bits_n!val!5)
              (= x Bits_n!val!49)
              (= x Bits_n!val!24)
              (= x Bits_n!val!35)
              (= x Bits_n!val!9)
              (= x Bits_n!val!70)))
  ;; -----------
  ;; universe for Bits_m:
  ;;   Bits_m!val!10 Bits_m!val!0 Bits_m!val!9 Bits_m!val!4 Bits_m!val!1 Bits_m!val!3 Bits_m!val!7 Bits_m!val!2 Bits_m!val!12 Bits_m!val!11 Bits_m!val!13 Bits_m!val!5 Bits_m!val!6 Bits_m!val!8
  ;; -----------
  ;; definitions for universe elements:
  (declare-fun Bits_m!val!10 () Bits_m)
  (declare-fun Bits_m!val!0 () Bits_m)
  (declare-fun Bits_m!val!9 () Bits_m)
  (declare-fun Bits_m!val!4 () Bits_m)
  (declare-fun Bits_m!val!1 () Bits_m)
  (declare-fun Bits_m!val!3 () Bits_m)
  (declare-fun Bits_m!val!7 () Bits_m)
  (declare-fun Bits_m!val!2 () Bits_m)
  (declare-fun Bits_m!val!12 () Bits_m)
  (declare-fun Bits_m!val!11 () Bits_m)
  (declare-fun Bits_m!val!13 () Bits_m)
  (declare-fun Bits_m!val!5 () Bits_m)
  (declare-fun Bits_m!val!6 () Bits_m)
  (declare-fun Bits_m!val!8 () Bits_m)
  ;; cardinality constraint:
  (forall ((x Bits_m))
          (or (= x Bits_m!val!10)
              (= x Bits_m!val!0)
              (= x Bits_m!val!9)
              (= x Bits_m!val!4)
              (= x Bits_m!val!1)
              (= x Bits_m!val!3)
              (= x Bits_m!val!7)
              (= x Bits_m!val!2)
              (= x Bits_m!val!12)
              (= x Bits_m!val!11)
              (= x Bits_m!val!13)
              (= x Bits_m!val!5)
              (= x Bits_m!val!6)
              (= x Bits_m!val!8)))
  ;; -----------
  ;; universe for Bits_p:
  ;;   Bits_p!val!1 Bits_p!val!3 Bits_p!val!2 Bits_p!val!0
  ;; -----------
  ;; definitions for universe elements:
  (declare-fun Bits_p!val!1 () Bits_p)
  (declare-fun Bits_p!val!3 () Bits_p)
  (declare-fun Bits_p!val!2 () Bits_p)
  (declare-fun Bits_p!val!0 () Bits_p)
  ;; cardinality constraint:
  (forall ((x Bits_p))
          (or (= x Bits_p!val!1)
              (= x Bits_p!val!3)
              (= x Bits_p!val!2)
              (= x Bits_p!val!0)))
  ;; -----------
  (define-fun table-bottom-left-old () (Array Int (Maybe (Array Bool (Maybe Bits_n))))
    (_ as-array k!4827))
  (define-fun lemma2 () Bool
    true)
  (define-fun table-top-right-old () (Array Int (Maybe (Array Bool (Maybe Bits_n))))
    (_ as-array k!4830))
  (define-fun is-abort-left () Bool
    false)
  (define-fun ctr-rr-left-new () Int
    11797)
  (define-fun return-right () Return_Right_simgate_GBLG
    (let ((a!1 (store (store (store ((as const (Array Bits_p (Maybe Bool)))
                                  (as mk-none (Maybe Bool)))
                                Bits_p!val!1
                                (mk-some true))
                         Bits_p!val!2
                         (mk-some true))
                  Bits_p!val!3
                  (mk-some true))))
  (mk-return-Right-simgate-GBLG
    (mk-composition-state-Right
      (mk-state-Right-keys_top
        (_ as-array k!4830)
        (_ as-array k!4844)
        (_ as-array k!4843))
      (mk-state-Right-keys_bottom
        (_ as-array k!4827)
        (_ as-array k!4842)
        (_ as-array k!4841))
      mk-state-Right-simgate
      mk-state-Right-ev
      20
      Bits_m!val!9
      21
      Bits_n!val!18
      22
      23
      24
      25
      5457401
      11797
      28101
      1143
      282
      20538
      15922
      8946
      26286
      2998)
    a!1)))
  (define-fun postcondition-holds () Bool
    true)
  (define-fun ctr-r-right () Int
    5457401)
  (define-fun table-bottom-right-new () (Array Int (Maybe (Array Bool (Maybe Bits_n))))
    (_ as-array k!4827))
  (define-fun lemma1 () Bool
    true)
  (define-fun ctr-rr-right-new () Int
    11797)
  (define-fun table-top-left-new () (Array Int (Maybe (Array Bool (Maybe Bits_n))))
    (_ as-array k!4830))
  (define-fun debug-top-left () Bool
    true)
  (define-fun ctr-r-left-new () Int
    5457401)
  (define-fun rr-right () Bits_n
    Bits_n!val!0)
  (define-fun lemma4 () Bool
    false)
  (define-fun standard-postcondition-holds () Bool
    false)
  (define-fun table-bottom-right-old () (Array Int (Maybe (Array Bool (Maybe Bits_n))))
    (_ as-array k!4827))
  (define-fun debug-bottom-right () Bool
    true)
  (define-fun table-top-right-new () (Array Int (Maybe (Array Bool (Maybe Bits_n))))
    (_ as-array k!4830))
  (define-fun ctr-r-right-new () Int
    5457401)
  (define-fun lemmas-hold () Bool
    false)
  (define-fun state-left-old () CompositionState-Left
    (let ((a!1 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         116
                         (as mk-none (Maybe Bool)))
                  2
                  (mk-some true)))
      (a!3 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         95
                         (mk-some true))
                  64
                  (mk-some true))))
(let ((a!2 (store (store (store (store a!1 96 (as mk-none (Maybe Bool)))
                                57
                                (mk-some true))
                         13
                         (mk-some true))
                  86
                  (mk-some true)))
      (a!4 (store (store (store a!3 128 (mk-some true)) 58 (mk-some true))
                  28
                  (mk-some true))))
(let ((a!5 (mk-state-Left-keys_bottom
             (_ as-array k!4827)
             (store (store a!4 125 (mk-some true)) 107 (mk-some true))
             (_ as-array k!4831))))
  (mk-composition-state-Left
    (mk-state-Left-keys_top (_ as-array k!4830) (_ as-array k!4829) a!2)
    a!5
    mk-state-Left-gate
    mk-state-Left-enc
    Bits_m!val!4
    14
    15
    16
    Bits_n!val!7
    17
    18
    19
    5457401
    11797
    12527959
    5321479)))))
  (define-fun state-left-new () CompositionState-Left
    (let ((a!1 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         116
                         (as mk-none (Maybe Bool)))
                  2
                  (mk-some true)))
      (a!3 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         95
                         (mk-some true))
                  64
                  (mk-some true))))
(let ((a!2 (store (store (store (store a!1 96 (as mk-none (Maybe Bool)))
                                57
                                (mk-some true))
                         13
                         (mk-some true))
                  86
                  (mk-some true)))
      (a!4 (store (store (store a!3 128 (mk-some true)) 58 (mk-some true))
                  28
                  (mk-some true))))
(let ((a!5 (mk-state-Left-keys_bottom
             (_ as-array k!4827)
             (store (store a!4 125 (mk-some true)) 107 (mk-some true))
             (_ as-array k!4825))))
  (mk-composition-state-Left
    (mk-state-Left-keys_top (_ as-array k!4830) (_ as-array k!4829) a!2)
    a!5
    mk-state-Left-gate
    mk-state-Left-enc
    Bits_m!val!4
    14
    15
    16
    Bits_n!val!7
    17
    18
    19
    5457401
    11797
    12527967
    5321483)))))
  (define-fun r-right () Bits_n
    Bits_n!val!0)
  (define-fun debug-bottom-left () Bool
    true)
  (define-fun hhh () Int
    104)
  (define-fun ctr-r-left () Int
    5457401)
  (define-fun return-left () Return_Left_gate_GBLG
    (let ((a!1 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         116
                         (as mk-none (Maybe Bool)))
                  2
                  (mk-some true)))
      (a!3 (store (store ((as const (Array Int (Maybe Bool))) (mk-some false))
                         95
                         (mk-some true))
                  64
                  (mk-some true)))
      (a!6 (store (store (store ((as const (Array Bits_p (Maybe Bool)))
                                  (as mk-none (Maybe Bool)))
                                Bits_p!val!1
                                (mk-some true))
                         Bits_p!val!0
                         (mk-some true))
                  Bits_p!val!2
                  (mk-some true))))
(let ((a!2 (store (store (store (store a!1 96 (as mk-none (Maybe Bool)))
                                57
                                (mk-some true))
                         13
                         (mk-some true))
                  86
                  (mk-some true)))
      (a!4 (store (store (store a!3 128 (mk-some true)) 58 (mk-some true))
                  28
                  (mk-some true))))
(let ((a!5 (mk-state-Left-keys_bottom
             (_ as-array k!4827)
             (store (store a!4 125 (mk-some true)) 107 (mk-some true))
             (_ as-array k!4825))))
  (mk-return-Left-gate-GBLG
    (mk-composition-state-Left
      (mk-state-Left-keys_top (_ as-array k!4830) (_ as-array k!4829) a!2)
      a!5
      mk-state-Left-gate
      mk-state-Left-enc
      Bits_m!val!4
      14
      15
      16
      Bits_n!val!7
      17
      18
      19
      5457401
      11797
      12527967
      5321483)
    a!6)))))
  (define-fun is-abort-right () Bool
    false)
  (define-fun r () Int
    13)
  (define-fun state-right-old () CompositionState-Right
    (mk-composition-state-Right
  (mk-state-Right-keys_top
    (_ as-array k!4830)
    (_ as-array k!4844)
    (_ as-array k!4843))
  (mk-state-Right-keys_bottom
    (_ as-array k!4827)
    (_ as-array k!4842)
    (_ as-array k!4843))
  mk-state-Right-simgate
  mk-state-Right-ev
  20
  Bits_m!val!9
  21
  Bits_n!val!18
  22
  23
  24
  25
  5457401
  11797
  28100
  1142
  281
  20537
  15921
  8945
  26285
  2997))
  (define-fun debug-top-right () Bool
    true)
  (define-fun ctr-rr-left () Int
    11797)
  (define-fun rr-left () Bits_n
    Bits_n!val!0)
  (define-fun Z-right () (Array Bool (Maybe Bits_n))
    ((as const (Array Bool (Maybe Bits_n))) (as mk-none (Maybe Bits_n))))
  (define-fun table-bottom-left-new () (Array Int (Maybe (Array Bool (Maybe Bits_n))))
    (_ as-array k!4827))
  (define-fun state-right-new () CompositionState-Right
    (mk-composition-state-Right
  (mk-state-Right-keys_top
    (_ as-array k!4830)
    (_ as-array k!4844)
    (_ as-array k!4843))
  (mk-state-Right-keys_bottom
    (_ as-array k!4827)
    (_ as-array k!4842)
    (_ as-array k!4841))
  mk-state-Right-simgate
  mk-state-Right-ev
  20
  Bits_m!val!9
  21
  Bits_n!val!18
  22
  23
  24
  25
  5457401
  11797
  28101
  1143
  282
  20538
  15922
  8946
  26286
  2998))
  (define-fun value-right () (Array Bits_p (Maybe Bool))
    (store (store (store ((as const (Array Bits_p (Maybe Bool)))
                       (as mk-none (Maybe Bool)))
                     Bits_p!val!1
                     (mk-some true))
              Bits_p!val!2
              (mk-some true))
       Bits_p!val!3
       (mk-some true)))
  (define-fun l () Int
    2)
  (define-fun ctr-rr-right () Int
    11797)
  (define-fun j () Int
    129)
  (define-fun r-left () Bits_n
    Bits_n!val!0)
  (define-fun value-left () (Array Bits_p (Maybe Bool))
    (store (store (store ((as const (Array Bits_p (Maybe Bool)))
                       (as mk-none (Maybe Bool)))
                     Bits_p!val!1
                     (mk-some true))
              Bits_p!val!0
              (mk-some true))
       Bits_p!val!2
       (mk-some true)))
  (define-fun lemma3 () Bool
    false)
  (define-fun op () (Array (Tuple2 Bool Bool) (Maybe Bool))
    ((as const (Array (Tuple2 Bool Bool) (Maybe Bool))) (mk-some false)))
  (define-fun Z-left () (Array Bool (Maybe Bits_n))
    (store ((as const (Array Bool (Maybe Bits_n))) (as mk-none (Maybe Bits_n)))
       false
       (mk-some Bits_n!val!0)))
  (define-fun table-top-left-old () (Array Int (Maybe (Array Bool (Maybe Bits_n))))
    (_ as-array k!4830))
  (define-fun precondition-holds () Bool
    true)
  (define-fun lemma5 () Bool
    false)
  (define-fun zero_bits_n () Bits_n
    Bits_n!val!71)
  (define-fun bit () Bool
    false)
  (define-fun zero_bits_p () Bits_p
    Bits_p!val!1)
  (define-fun zero_bits_m () Bits_m
    Bits_m!val!10)
  (define-fun handle () Int
    0)
  (define-fun __sample-rand-Right-Bits_n ((x!0 Int) (x!1 Int)) Bits_n
    (ite (and (= x!0 5) (= x!1 28100)) Bits_n!val!20
    (ite (and (= x!0 6) (= x!1 1142)) Bits_n!val!21
    (ite (and (= x!0 7) (= x!1 281)) Bits_n!val!22
    (ite (and (= x!0 8) (= x!1 20537)) Bits_n!val!23
    (ite (and (= x!0 9) (= x!1 15921)) Bits_n!val!24
    (ite (and (= x!0 10) (= x!1 8945)) Bits_n!val!25
    (ite (and (= x!0 11) (= x!1 26285)) Bits_n!val!26
    (ite (and (= x!0 12) (= x!1 2997)) Bits_n!val!27
      Bits_n!val!0)))))))))
  (define-fun k!4820 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!0)
    (ite (= x!0 true) (mk-some Bits_n!val!0)
      (as mk-none (Maybe Bits_n)))))
  (define-fun k!4830 ((x!0 Int)) (Maybe (Array Bool (Maybe Bits_n)))
    (ite (= x!0 100)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!44))
                      false
                      (mk-some Bits_n!val!63)))
    (ite (= x!0 129)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!59))
                      false
                      (mk-some Bits_n!val!70)))
    (ite (= x!0 92)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!49))
                      false
                      (mk-some Bits_n!val!28)))
    (ite (= x!0 91)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!54))
                      false
                      (mk-some Bits_n!val!31)))
    (ite (= x!0 101)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!45))
                      false
                      (mk-some Bits_n!val!66)))
    (ite (= x!0 105)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!48))
                      false
                      (mk-some Bits_n!val!30)))
    (ite (= x!0 13)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!56))
                               false
                               (mk-some Bits_n!val!8))
                        true
                        (mk-some Bits_n!val!17))))
        (mk-some a!1))
    (ite (= x!0 103)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!55))
                               false
                               (mk-some Bits_n!val!71))
                        true
                        (mk-some Bits_n!val!75))))
        (mk-some a!1))
    (ite (= x!0 99)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!42))
                      false
                      (mk-some Bits_n!val!74)))
    (ite (= x!0 2)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!78))
                               false
                               (mk-some Bits_n!val!10))
                        true
                        (mk-some Bits_n!val!5))))
        (mk-some a!1))
    (ite (= x!0 109)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!57))
                               false
                               (mk-some Bits_n!val!29))
                        true
                        (mk-some Bits_n!val!77))))
        (mk-some a!1))
    (ite (= x!0 106)
      (mk-some (store (store ((as const (Array Bool (Maybe Bits_n)))
                               (as mk-none (Maybe Bits_n)))
                             false
                             (mk-some Bits_n!val!36))
                      true
                      (mk-some Bits_n!val!41)))
    (ite (= x!0 110)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!51))
                               false
                               (mk-some Bits_n!val!38))
                        true
                        (mk-some Bits_n!val!62))))
        (mk-some a!1))
      (mk-some ((as const (Array Bool (Maybe Bits_n))) (mk-some Bits_n!val!79)))))))))))))))))
  (define-fun k!4807 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!0)
      (as mk-none (Maybe Bits_n))))
  (define-fun __sample-rand-Left-Bits_n ((x!0 Int) (x!1 Int)) Bits_n
    (ite (and (= x!0 5) (= x!1 12527959)) Bits_n!val!1
    (ite (and (= x!0 5) (= x!1 12527960)) Bits_n!val!2
    (ite (and (= x!0 6) (= x!1 5321479)) Bits_n!val!3
    (ite (and (= x!0 5) (= x!1 12527961)) Bits_n!val!4
    (ite (and (= x!0 5) (= x!1 12527962)) Bits_n!val!6
    (ite (and (= x!0 6) (= x!1 5321480)) Bits_n!val!9
    (ite (and (= x!0 5) (= x!1 12527963)) Bits_n!val!11
    (ite (and (= x!0 5) (= x!1 12527964)) Bits_n!val!12
    (ite (and (= x!0 6) (= x!1 5321481)) Bits_n!val!13
    (ite (and (= x!0 5) (= x!1 12527965)) Bits_n!val!14
    (ite (and (= x!0 5) (= x!1 12527966)) Bits_n!val!15
    (ite (and (= x!0 6) (= x!1 5321482)) Bits_n!val!16
      Bits_n!val!0)))))))))))))
  (define-fun __func-Left-encn ((x!0 Bits_n) (x!1 Bits_n) (x!2 Bits_n)) Bits_m
    (ite (and (= x!0 Bits_n!val!10) (= x!1 Bits_n!val!7) (= x!2 Bits_n!val!2))
      Bits_m!val!1
    (ite (and (= x!0 Bits_n!val!5) (= x!1 Bits_n!val!19) (= x!2 Bits_n!val!4))
      Bits_m!val!2
    (ite (and (= x!0 Bits_n!val!5) (= x!1 Bits_n!val!7) (= x!2 Bits_n!val!6))
      Bits_m!val!3
    (ite (and (= x!0 Bits_n!val!10) (= x!1 Bits_n!val!19) (= x!2 Bits_n!val!11))
      Bits_m!val!5
    (ite (and (= x!0 Bits_n!val!10) (= x!1 Bits_n!val!7) (= x!2 Bits_n!val!12))
      Bits_m!val!6
    (ite (and (= x!0 Bits_n!val!5) (= x!1 Bits_n!val!19) (= x!2 Bits_n!val!14))
      Bits_m!val!7
    (ite (and (= x!0 Bits_n!val!5) (= x!1 Bits_n!val!7) (= x!2 Bits_n!val!15))
      Bits_m!val!8
      Bits_m!val!0))))))))
  (define-fun k!4808 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!36)
    (ite (= x!0 true) (mk-some Bits_n!val!41)
      (as mk-none (Maybe Bits_n)))))
  (define-fun __func-Left-encm ((x!0 Bits_n) (x!1 Bits_m) (x!2 Bits_n)) Bits_p
    (ite (and (= x!0 Bits_n!val!8) (= x!1 Bits_m!val!1) (= x!2 Bits_n!val!3))
      Bits_p!val!0
    (ite (and (= x!0 Bits_n!val!17) (= x!1 Bits_m!val!8) (= x!2 Bits_n!val!16))
      Bits_p!val!2
      Bits_p!val!1)))
  (define-fun k!4809 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!34)
    (ite (= x!0 true) (mk-some Bits_n!val!67)
      (mk-some Bits_n!val!32))))
  (define-fun k!4825 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 53) (mk-some true)
    (ite (= x!0 61) (mk-some true)
    (ite (= x!0 77) (as mk-none (Maybe Bool))
    (ite (= x!0 60) (as mk-none (Maybe Bool))
    (ite (= x!0 34) (mk-some true)
    (ite (= x!0 74) (as mk-none (Maybe Bool))
    (ite (= x!0 26) (mk-some true)
    (ite (= x!0 62) (mk-some true)
    (ite (= x!0 119) (as mk-none (Maybe Bool))
    (ite (= x!0 66) (mk-some true)
    (ite (= x!0 129) (mk-some true)
    (ite (= x!0 65) (as mk-none (Maybe Bool))
    (ite (= x!0 93) (mk-some true)
    (ite (= x!0 55) (mk-some true)
      (mk-some false))))))))))))))))
  (define-fun k!4834 ((x!0 Int)) (Maybe (Array Bool (Maybe Bits_n)))
    (ite (= x!0 100)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!47))
                      false
                      (mk-some Bits_n!val!60)))
    (ite (= x!0 129)
      (mk-some (store (store ((as const (Array Bool (Maybe Bits_n)))
                               (as mk-none (Maybe Bits_n)))
                             false
                             (mk-some Bits_n!val!0))
                      true
                      (mk-some Bits_n!val!0)))
    (ite (= x!0 112)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!58))
                      false
                      (mk-some Bits_n!val!39)))
    (ite (= x!0 33)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!43))
                               false
                               (mk-some Bits_n!val!61))
                        true
                        (mk-some Bits_n!val!72))))
        (mk-some a!1))
    (ite (= x!0 101)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!52))
                               false
                               (mk-some Bits_n!val!76))
                        true
                        (mk-some Bits_n!val!73))))
        (mk-some a!1))
    (ite (= x!0 104)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!32))
                               false
                               (mk-some Bits_n!val!34))
                        true
                        (mk-some Bits_n!val!67))))
        (mk-some a!1))
    (ite (= x!0 90)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!53))
                      false
                      (mk-some Bits_n!val!35)))
    (ite (= x!0 111)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!50))
                               false
                               (mk-some Bits_n!val!33))
                        true
                        (mk-some Bits_n!val!64))))
        (mk-some a!1))
    (ite (= x!0 103)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!46))
                      false
                      (mk-some Bits_n!val!69)))
    (ite (= x!0 102)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!40))
                               false
                               (mk-some Bits_n!val!68))
                        true
                        (mk-some Bits_n!val!65))))
        (mk-some a!1))
      (mk-some ((as const (Array Bool (Maybe Bits_n))) (mk-some Bits_n!val!80))))))))))))))
  (define-fun k!4811 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!71)
    (ite (= x!0 true) (mk-some Bits_n!val!75)
      (mk-some Bits_n!val!55))))
  (define-fun k!4826 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 95) (mk-some true)
    (ite (= x!0 64) (mk-some true)
    (ite (= x!0 128) (mk-some true)
    (ite (= x!0 58) (mk-some true)
    (ite (= x!0 28) (mk-some true)
    (ite (= x!0 125) (mk-some true)
    (ite (= x!0 107) (mk-some true)
      (mk-some false)))))))))
  (define-fun k!4797 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!33)
    (ite (= x!0 true) (mk-some Bits_n!val!64)
      (mk-some Bits_n!val!50))))
  (define-fun k!4841 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 113) (mk-some true)
    (ite (= x!0 115) (as mk-none (Maybe Bool))
    (ite (= x!0 70) (mk-some true)
    (ite (= x!0 2) (mk-some true)
    (ite (= x!0 33) (as mk-none (Maybe Bool))
    (ite (= x!0 35) (mk-some true)
    (ite (= x!0 129) (mk-some true)
    (ite (= x!0 29) (mk-some true)
    (ite (= x!0 98) (mk-some true)
    (ite (= x!0 87) (mk-some true)
    (ite (= x!0 13) (mk-some true)
      (mk-some false)))))))))))))
  (define-fun k!4812 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!68)
    (ite (= x!0 true) (mk-some Bits_n!val!65)
      (mk-some Bits_n!val!40))))
  (define-fun k!4798 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!38)
    (ite (= x!0 true) (mk-some Bits_n!val!62)
      (mk-some Bits_n!val!51))))
  (define-fun k!4842 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 80) (as mk-none (Maybe Bool))
    (ite (= x!0 97) (as mk-none (Maybe Bool))
    (ite (= x!0 36) (mk-some true)
    (ite (= x!0 108) (mk-some true)
    (ite (= x!0 124) (mk-some true)
    (ite (= x!0 76) (as mk-none (Maybe Bool))
    (ite (= x!0 117) (mk-some true)
    (ite (= x!0 85) (as mk-none (Maybe Bool))
    (ite (= x!0 129) (as mk-none (Maybe Bool))
      (mk-some false)))))))))))
  (define-fun k!4828 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 116) (as mk-none (Maybe Bool))
    (ite (= x!0 2) (mk-some true)
    (ite (= x!0 96) (as mk-none (Maybe Bool))
    (ite (= x!0 57) (mk-some true)
    (ite (= x!0 13) (mk-some true)
    (ite (= x!0 86) (mk-some true)
      (mk-some false))))))))
  (define-fun k!4799 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!29)
    (ite (= x!0 true) (mk-some Bits_n!val!77)
      (mk-some Bits_n!val!57))))
  (define-fun k!4843 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 113) (mk-some true)
    (ite (= x!0 2) (mk-some true)
    (ite (= x!0 70) (mk-some true)
    (ite (= x!0 115) (as mk-none (Maybe Bool))
    (ite (= x!0 33) (as mk-none (Maybe Bool))
    (ite (= x!0 35) (mk-some true)
    (ite (= x!0 29) (mk-some true)
    (ite (= x!0 98) (mk-some true)
    (ite (= x!0 87) (mk-some true)
    (ite (= x!0 13) (mk-some true)
      (mk-some false))))))))))))
  (define-fun __func-Right-encn ((x!0 Bits_n) (x!1 Bits_n) (x!2 Bits_n)) Bits_m
    (ite (and (= x!0 Bits_n!val!0) (= x!1 Bits_n!val!18) (= x!2 Bits_n!val!22))
      Bits_m!val!11
    (ite (and (= x!0 Bits_n!val!17) (= x!1 Bits_n!val!18) (= x!2 Bits_n!val!24))
      Bits_m!val!12
    (ite (and (= x!0 Bits_n!val!17) (= x!1 Bits_n!val!18) (= x!2 Bits_n!val!26))
      Bits_m!val!13
      Bits_m!val!10))))
  (define-fun k!4814 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!76)
    (ite (= x!0 true) (mk-some Bits_n!val!73)
      (mk-some Bits_n!val!52))))
  (define-fun k!4829 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 123) (as mk-none (Maybe Bool))
    (ite (= x!0 83) (as mk-none (Maybe Bool))
    (ite (= x!0 75) (mk-some true)
    (ite (= x!0 51) (as mk-none (Maybe Bool))
    (ite (= x!0 89) (as mk-none (Maybe Bool))
    (ite (= x!0 63) (as mk-none (Maybe Bool))
    (ite (= x!0 72) (mk-some true)
    (ite (= x!0 114) (mk-some true)
    (ite (= x!0 94) (mk-some true)
    (ite (= x!0 31) (mk-some true)
    (ite (= x!0 84) (mk-some true)
      (mk-some false)))))))))))))
  (define-fun k!4844 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 78) (mk-some true)
    (ite (= x!0 73) (mk-some true)
    (ite (= x!0 81) (as mk-none (Maybe Bool))
    (ite (= x!0 82) (as mk-none (Maybe Bool))
    (ite (= x!0 126) (mk-some true)
    (ite (= x!0 127) (as mk-none (Maybe Bool))
    (ite (= x!0 122) (mk-some true)
    (ite (= x!0 121) (as mk-none (Maybe Bool))
      (mk-some false))))))))))
  (define-fun __func-Right-encm ((x!0 Bits_n) (x!1 Bits_m) (x!2 Bits_n)) Bits_p
    (ite (and (= x!0 Bits_n!val!5) (= x!1 Bits_m!val!10) (= x!2 Bits_n!val!21))
      Bits_p!val!3
    (ite (and (= x!0 Bits_n!val!10) (= x!1 Bits_m!val!13) (= x!2 Bits_n!val!27))
      Bits_p!val!1
      Bits_p!val!2)))
  (define-fun k!4831 ((x!0 Int)) (Maybe Bool)
    (ite (= x!0 53) (mk-some true)
    (ite (= x!0 61) (mk-some true)
    (ite (= x!0 60) (as mk-none (Maybe Bool))
    (ite (= x!0 34) (mk-some true)
    (ite (= x!0 77) (as mk-none (Maybe Bool))
    (ite (= x!0 74) (as mk-none (Maybe Bool))
    (ite (= x!0 26) (mk-some true)
    (ite (= x!0 62) (mk-some true)
    (ite (= x!0 119) (as mk-none (Maybe Bool))
    (ite (= x!0 66) (mk-some true)
    (ite (= x!0 65) (as mk-none (Maybe Bool))
    (ite (= x!0 93) (mk-some true)
    (ite (= x!0 55) (mk-some true)
      (mk-some false)))))))))))))))
  (define-fun k!4827 ((x!0 Int)) (Maybe (Array Bool (Maybe Bits_n)))
    (ite (= x!0 100)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!47))
                      false
                      (mk-some Bits_n!val!60)))
    (ite (= x!0 129)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!37))
                      false
                      (mk-some Bits_n!val!19)))
    (ite (= x!0 112)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!58))
                      false
                      (mk-some Bits_n!val!39)))
    (ite (= x!0 33)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!43))
                               false
                               (mk-some Bits_n!val!61))
                        true
                        (mk-some Bits_n!val!72))))
        (mk-some a!1))
    (ite (= x!0 101)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!52))
                               false
                               (mk-some Bits_n!val!76))
                        true
                        (mk-some Bits_n!val!73))))
        (mk-some a!1))
    (ite (= x!0 104)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!32))
                               false
                               (mk-some Bits_n!val!34))
                        true
                        (mk-some Bits_n!val!67))))
        (mk-some a!1))
    (ite (= x!0 90)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!53))
                      false
                      (mk-some Bits_n!val!35)))
    (ite (= x!0 111)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!50))
                               false
                               (mk-some Bits_n!val!33))
                        true
                        (mk-some Bits_n!val!64))))
        (mk-some a!1))
    (ite (= x!0 103)
      (mk-some (store ((as const (Array Bool (Maybe Bits_n)))
                        (mk-some Bits_n!val!46))
                      false
                      (mk-some Bits_n!val!69)))
    (ite (= x!0 102)
      (let ((a!1 (store (store ((as const (Array Bool (Maybe Bits_n)))
                                 (mk-some Bits_n!val!40))
                               false
                               (mk-some Bits_n!val!68))
                        true
                        (mk-some Bits_n!val!65))))
        (mk-some a!1))
      (mk-some ((as const (Array Bool (Maybe Bits_n))) (mk-some Bits_n!val!80))))))))))))))
  (define-fun k!4804 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!61)
    (ite (= x!0 true) (mk-some Bits_n!val!72)
      (mk-some Bits_n!val!43))))
  (define-fun k!4819 ((x!0 Bool)) (Maybe Bits_n)
    (ite (= x!0 false) (mk-some Bits_n!val!8)
    (ite (= x!0 true) (mk-some Bits_n!val!17)
      (mk-some Bits_n!val!56))))
)