(declare-datatypes ((Maybe 1)) ((par (T) ((mk-some (maybe-get T)) (mk-none)))))
(declare-datatypes
  ((Tuple2 2))
  ((par (T1 T2) ((mk-tuple2 (el1 T1) (el2 T2)))))); Left
(declare-sort Bits_m 0)
(declare-const zero_bits_m Bits_m)
(declare-sort Bits_p 0)
(declare-const zero_bits_p Bits_p)
(declare-sort Bits_n 0)
(declare-const zero_bits_n Bits_n)
(declare-fun __sample-rand-Left-Bits_n (Int Int) Bits_n)
(declare-fun __func-Left-encm (Bits_n Bits_m Bits_n) Bits_p)
(declare-fun __func-Left-encn (Bits_n Bits_n Bits_n) Bits_m)
(declare-datatype
  State_Left_keys_top
  (
    (mk-state-Left-keys_top
      (state-Left-keys_top-T (Array Int (Maybe (Array Bool (Maybe Bits_n)))))
      (state-Left-keys_top-z (Array Int (Maybe Bool)))
      (state-Left-keys_top-aflag (Array Int (Maybe Bool)))
      (state-Left-keys_top-bflag (Array Int (Maybe Bool))))))
(declare-datatype
  State_Left_keys_bottom
  (
    (mk-state-Left-keys_bottom
      (state-Left-keys_bottom-T (Array Int (Maybe (Array Bool (Maybe Bits_n)))))
      (state-Left-keys_bottom-z (Array Int (Maybe Bool)))
      (state-Left-keys_bottom-aflag (Array Int (Maybe Bool)))
      (state-Left-keys_bottom-bflag (Array Int (Maybe Bool))))))
(declare-datatype State_Left_gate ((mk-state-Left-gate)))
(declare-datatype State_Left_enc ((mk-state-Left-enc)))
(declare-datatype
  CompositionState-Left
  (
    (mk-composition-state-Left
      (composition-pkgstate-Left-keys_top State_Left_keys_top)
      (composition-pkgstate-Left-keys_bottom State_Left_keys_bottom)
      (composition-pkgstate-Left-gate State_Left_gate)
      (composition-pkgstate-Left-enc State_Left_enc)
      (composition-param-Left-zerom Bits_m)
      (composition-param-Left-m Int)
      (composition-param-Left-p Int)
      (composition-param-Left-n Int)
      (composition-param-Left-zeron Bits_n)
      (composition-rand-Left-0 Int)
      (composition-rand-Left-1 Int)
      (composition-rand-Left-2 Int)
      (composition-rand-Left-3 Int)
      (composition-rand-Left-4 Int)
      (composition-rand-Left-5 Int)
      (composition-rand-Left-6 Int))))
(declare-datatype
  Return_Left_keys_top_GETKEYSIN
  (
    (mk-abort-Left-keys_top-GETKEYSIN)
    (mk-return-Left-keys_top-GETKEYSIN
      (return-Left-keys_top-GETKEYSIN-state CompositionState-Left)
      (return-Left-keys_top-GETKEYSIN-value (Array Bool (Maybe Bits_n))))))
(declare-datatype
  Return_Left_keys_top_GETKEYSOUT
  (
    (mk-abort-Left-keys_top-GETKEYSOUT)
    (mk-return-Left-keys_top-GETKEYSOUT
      (return-Left-keys_top-GETKEYSOUT-state CompositionState-Left)
      (return-Left-keys_top-GETKEYSOUT-value (Array Bool (Maybe Bits_n))))))
(declare-datatype
  Return_Left_keys_top_GETAOUT
  (
    (mk-abort-Left-keys_top-GETAOUT)
    (mk-return-Left-keys_top-GETAOUT
      (return-Left-keys_top-GETAOUT-state CompositionState-Left)
      (return-Left-keys_top-GETAOUT-value Bits_n))))
(declare-datatype
  Return_Left_keys_top_GETINAOUT
  (
    (mk-abort-Left-keys_top-GETINAOUT)
    (mk-return-Left-keys_top-GETINAOUT
      (return-Left-keys_top-GETINAOUT-state CompositionState-Left)
      (return-Left-keys_top-GETINAOUT-value Bits_n))))
(declare-datatype
  Return_Left_keys_top_GETAIN
  (
    (mk-abort-Left-keys_top-GETAIN)
    (mk-return-Left-keys_top-GETAIN
      (return-Left-keys_top-GETAIN-state CompositionState-Left)
      (return-Left-keys_top-GETAIN-value Bits_n))))
(declare-datatype
  Return_Left_keys_top_GETINAIN
  (
    (mk-abort-Left-keys_top-GETINAIN)
    (mk-return-Left-keys_top-GETINAIN
      (return-Left-keys_top-GETINAIN-state CompositionState-Left)
      (return-Left-keys_top-GETINAIN-value Bits_n))))
(declare-datatype
  Return_Left_keys_top_GETBIT
  (
    (mk-abort-Left-keys_top-GETBIT)
    (mk-return-Left-keys_top-GETBIT
      (return-Left-keys_top-GETBIT-state CompositionState-Left)
      (return-Left-keys_top-GETBIT-value Bool))))
(declare-datatype
  Return_Left_keys_top_SETBIT
  (
    (mk-abort-Left-keys_top-SETBIT)
    (mk-return-Left-keys_top-SETBIT
      (return-Left-keys_top-SETBIT-state CompositionState-Left))))
(declare-datatype
  Return_Left_keys_bottom_GETKEYSIN
  (
    (mk-abort-Left-keys_bottom-GETKEYSIN)
    (mk-return-Left-keys_bottom-GETKEYSIN
      (return-Left-keys_bottom-GETKEYSIN-state CompositionState-Left)
      (return-Left-keys_bottom-GETKEYSIN-value (Array Bool (Maybe Bits_n))))))
(declare-datatype
  Return_Left_keys_bottom_GETKEYSOUT
  (
    (mk-abort-Left-keys_bottom-GETKEYSOUT)
    (mk-return-Left-keys_bottom-GETKEYSOUT
      (return-Left-keys_bottom-GETKEYSOUT-state CompositionState-Left)
      (return-Left-keys_bottom-GETKEYSOUT-value (Array Bool (Maybe Bits_n))))))
(declare-datatype
  Return_Left_keys_bottom_GETAOUT
  (
    (mk-abort-Left-keys_bottom-GETAOUT)
    (mk-return-Left-keys_bottom-GETAOUT
      (return-Left-keys_bottom-GETAOUT-state CompositionState-Left)
      (return-Left-keys_bottom-GETAOUT-value Bits_n))))
(declare-datatype
  Return_Left_keys_bottom_GETINAOUT
  (
    (mk-abort-Left-keys_bottom-GETINAOUT)
    (mk-return-Left-keys_bottom-GETINAOUT
      (return-Left-keys_bottom-GETINAOUT-state CompositionState-Left)
      (return-Left-keys_bottom-GETINAOUT-value Bits_n))))
(declare-datatype
  Return_Left_keys_bottom_GETAIN
  (
    (mk-abort-Left-keys_bottom-GETAIN)
    (mk-return-Left-keys_bottom-GETAIN
      (return-Left-keys_bottom-GETAIN-state CompositionState-Left)
      (return-Left-keys_bottom-GETAIN-value Bits_n))))
(declare-datatype
  Return_Left_keys_bottom_GETINAIN
  (
    (mk-abort-Left-keys_bottom-GETINAIN)
    (mk-return-Left-keys_bottom-GETINAIN
      (return-Left-keys_bottom-GETINAIN-state CompositionState-Left)
      (return-Left-keys_bottom-GETINAIN-value Bits_n))))
(declare-datatype
  Return_Left_keys_bottom_GETBIT
  (
    (mk-abort-Left-keys_bottom-GETBIT)
    (mk-return-Left-keys_bottom-GETBIT
      (return-Left-keys_bottom-GETBIT-state CompositionState-Left)
      (return-Left-keys_bottom-GETBIT-value Bool))))
(declare-datatype
  Return_Left_keys_bottom_SETBIT
  (
    (mk-abort-Left-keys_bottom-SETBIT)
    (mk-return-Left-keys_bottom-SETBIT
      (return-Left-keys_bottom-SETBIT-state CompositionState-Left))))
(declare-datatype
  Return_Left_gate_GBLG
  (
    (mk-abort-Left-gate-GBLG)
    (mk-return-Left-gate-GBLG
      (return-Left-gate-GBLG-state CompositionState-Left)
      (return-Left-gate-GBLG-value (Array Bits_p (Maybe Bool))))))
(declare-datatype
  Return_Left_enc_ENCN
  (
    (mk-abort-Left-enc-ENCN)
    (mk-return-Left-enc-ENCN
      (return-Left-enc-ENCN-state CompositionState-Left)
      (return-Left-enc-ENCN-value Bits_m))))
(declare-datatype
  Return_Left_enc_ENCM
  (
    (mk-abort-Left-enc-ENCM)
    (mk-return-Left-enc-ENCM
      (return-Left-enc-ENCM-state CompositionState-Left)
      (return-Left-enc-ENCM-value Bits_p)))); Composition of Left
(define-fun
  oracle-Left-keys_top-GETKEYSIN
  ((__global_state CompositionState-Left) (h Int))
  Return_Left_keys_top_GETKEYSIN
  (let
    ((__self_state (composition-pkgstate-Left-keys_top __global_state)))
    (ite
      (not
        (= (select (state-Left-keys_top-z __self_state) h) (as mk-none (Maybe Bool))))
      (ite
        (or
          (= (select (state-Left-keys_top-aflag __self_state) h) (mk-some true))
          (= (select (state-Left-keys_top-bflag __self_state) h) (mk-some true)))
        (let
          ((unwrap-1 (maybe-get (select (state-Left-keys_top-T __self_state) h))))
          (let
            ((Z unwrap-1))
            (let
              (
                (__global_state
                  (mk-composition-state-Left
                    __self_state
                    (composition-pkgstate-Left-keys_bottom __global_state)
                    (composition-pkgstate-Left-gate __global_state)
                    (composition-pkgstate-Left-enc __global_state)
                    (composition-param-Left-zerom __global_state)
                    (composition-param-Left-m __global_state)
                    (composition-param-Left-p __global_state)
                    (composition-param-Left-n __global_state)
                    (composition-param-Left-zeron __global_state)
                    (composition-rand-Left-0 __global_state)
                    (composition-rand-Left-1 __global_state)
                    (composition-rand-Left-2 __global_state)
                    (composition-rand-Left-3 __global_state)
                    (composition-rand-Left-4 __global_state)
                    (composition-rand-Left-5 __global_state)
                    (composition-rand-Left-6 __global_state))))
              (mk-return-Left-keys_top-GETKEYSIN __global_state Z))))
        mk-abort-Left-keys_top-GETKEYSIN)
      mk-abort-Left-keys_top-GETKEYSIN)))
(define-fun
  oracle-Left-keys_top-GETKEYSOUT
  ((__global_state CompositionState-Left) (h Int))
  Return_Left_keys_top_GETKEYSOUT
  (let
    ((__self_state (composition-pkgstate-Left-keys_top __global_state)))
    (let
      (
        (__self_state
          (mk-state-Left-keys_top
            (state-Left-keys_top-T __self_state)
            (state-Left-keys_top-z __self_state)
            (store (state-Left-keys_top-aflag __self_state) h (mk-some true))
            (state-Left-keys_top-bflag __self_state))))
      (let
        ((Z ((as const (Array Bool (Maybe Bits_n))) (as mk-none (Maybe Bits_n)))))
        (ite
          (=
            (select (state-Left-keys_top-T __self_state) h)
            (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
          (let
            ((r (__sample-rand-Left-Bits_n 1 (composition-rand-Left-1 __global_state))))
            (let
              (
                (__global_state
                  (mk-composition-state-Left
                    (composition-pkgstate-Left-keys_top __global_state)
                    (composition-pkgstate-Left-keys_bottom __global_state)
                    (composition-pkgstate-Left-gate __global_state)
                    (composition-pkgstate-Left-enc __global_state)
                    (composition-param-Left-zerom __global_state)
                    (composition-param-Left-m __global_state)
                    (composition-param-Left-p __global_state)
                    (composition-param-Left-n __global_state)
                    (composition-param-Left-zeron __global_state)
                    (composition-rand-Left-0 __global_state)
                    (+ 1 (composition-rand-Left-1 __global_state))
                    (composition-rand-Left-2 __global_state)
                    (composition-rand-Left-3 __global_state)
                    (composition-rand-Left-4 __global_state)
                    (composition-rand-Left-5 __global_state)
                    (composition-rand-Left-6 __global_state))))
              (let
                ((Z ((as const (Array Bool (Maybe Bits_n))) (as mk-none (Maybe Bits_n)))))
                (let
                  ((Z (store Z true (mk-some r))))
                  (let
                    ((rr (__sample-rand-Left-Bits_n 2 (composition-rand-Left-2 __global_state))))
                    (let
                      (
                        (__global_state
                          (mk-composition-state-Left
                            (composition-pkgstate-Left-keys_top __global_state)
                            (composition-pkgstate-Left-keys_bottom __global_state)
                            (composition-pkgstate-Left-gate __global_state)
                            (composition-pkgstate-Left-enc __global_state)
                            (composition-param-Left-zerom __global_state)
                            (composition-param-Left-m __global_state)
                            (composition-param-Left-p __global_state)
                            (composition-param-Left-n __global_state)
                            (composition-param-Left-zeron __global_state)
                            (composition-rand-Left-0 __global_state)
                            (composition-rand-Left-1 __global_state)
                            (+ 1 (composition-rand-Left-2 __global_state))
                            (composition-rand-Left-3 __global_state)
                            (composition-rand-Left-4 __global_state)
                            (composition-rand-Left-5 __global_state)
                            (composition-rand-Left-6 __global_state))))
                      (let
                        ((Z ((as const (Array Bool (Maybe Bits_n))) (as mk-none (Maybe Bits_n)))))
                        (let
                          ((Z (store Z false (mk-some rr))))
                          (let
                            (
                              (__self_state
                                (mk-state-Left-keys_top
                                  (store (state-Left-keys_top-T __self_state) h (mk-some Z))
                                  (state-Left-keys_top-z __self_state)
                                  (state-Left-keys_top-aflag __self_state)
                                  (state-Left-keys_top-bflag __self_state))))
                            (let
                              ((unwrap-1 (maybe-get (select (state-Left-keys_top-T __self_state) h))))
                              (let
                                ((Z unwrap-1))
                                (let
                                  (
                                    (__global_state
                                      (mk-composition-state-Left
                                        __self_state
                                        (composition-pkgstate-Left-keys_bottom __global_state)
                                        (composition-pkgstate-Left-gate __global_state)
                                        (composition-pkgstate-Left-enc __global_state)
                                        (composition-param-Left-zerom __global_state)
                                        (composition-param-Left-m __global_state)
                                        (composition-param-Left-p __global_state)
                                        (composition-param-Left-n __global_state)
                                        (composition-param-Left-zeron __global_state)
                                        (composition-rand-Left-0 __global_state)
                                        (composition-rand-Left-1 __global_state)
                                        (composition-rand-Left-2 __global_state)
                                        (composition-rand-Left-3 __global_state)
                                        (composition-rand-Left-4 __global_state)
                                        (composition-rand-Left-5 __global_state)
                                        (composition-rand-Left-6 __global_state))))
                                  (mk-return-Left-keys_top-GETKEYSOUT __global_state Z)))))))))))))
          (let
            ((unwrap-1 (maybe-get (select (state-Left-keys_top-T __self_state) h))))
            (let
              ((Z unwrap-1))
              (let
                (
                  (__global_state
                    (mk-composition-state-Left
                      __self_state
                      (composition-pkgstate-Left-keys_bottom __global_state)
                      (composition-pkgstate-Left-gate __global_state)
                      (composition-pkgstate-Left-enc __global_state)
                      (composition-param-Left-zerom __global_state)
                      (composition-param-Left-m __global_state)
                      (composition-param-Left-p __global_state)
                      (composition-param-Left-n __global_state)
                      (composition-param-Left-zeron __global_state)
                      (composition-rand-Left-0 __global_state)
                      (composition-rand-Left-1 __global_state)
                      (composition-rand-Left-2 __global_state)
                      (composition-rand-Left-3 __global_state)
                      (composition-rand-Left-4 __global_state)
                      (composition-rand-Left-5 __global_state)
                      (composition-rand-Left-6 __global_state))))
                (mk-return-Left-keys_top-GETKEYSOUT __global_state Z)))))))))
(define-fun
  oracle-Left-keys_top-GETAOUT
  ((__global_state CompositionState-Left) (h Int))
  Return_Left_keys_top_GETAOUT
  (let
    ((__self_state (composition-pkgstate-Left-keys_top __global_state)))
    (let
      (
        (__self_state
          (mk-state-Left-keys_top
            (state-Left-keys_top-T __self_state)
            (state-Left-keys_top-z __self_state)
            (store (state-Left-keys_top-aflag __self_state) h (mk-some true))
            (state-Left-keys_top-bflag __self_state))))
      (ite
        (or
          (= (select (state-Left-keys_top-aflag __self_state) h) (mk-some true))
          (= (select (state-Left-keys_top-bflag __self_state) h) (mk-some true)))
        (let
          ((unwrap-1 (maybe-get (select (state-Left-keys_top-T __self_state) h))))
          (let
            ((Z unwrap-1))
            (let
              ((unwrap-2 (maybe-get (select (state-Left-keys_top-z __self_state) h))))
              (let
                ((zz unwrap-2))
                (let
                  ((unwrap-3 (maybe-get (select Z zz))))
                  (let
                    ((k unwrap-3))
                    (let
                      (
                        (__global_state
                          (mk-composition-state-Left
                            __self_state
                            (composition-pkgstate-Left-keys_bottom __global_state)
                            (composition-pkgstate-Left-gate __global_state)
                            (composition-pkgstate-Left-enc __global_state)
                            (composition-param-Left-zerom __global_state)
                            (composition-param-Left-m __global_state)
                            (composition-param-Left-p __global_state)
                            (composition-param-Left-n __global_state)
                            (composition-param-Left-zeron __global_state)
                            (composition-rand-Left-0 __global_state)
                            (composition-rand-Left-1 __global_state)
                            (composition-rand-Left-2 __global_state)
                            (composition-rand-Left-3 __global_state)
                            (composition-rand-Left-4 __global_state)
                            (composition-rand-Left-5 __global_state)
                            (composition-rand-Left-6 __global_state))))
                      (mk-return-Left-keys_top-GETAOUT __global_state k))))))))
        mk-abort-Left-keys_top-GETAOUT))))
(define-fun
  oracle-Left-keys_top-GETINAOUT
  ((__global_state CompositionState-Left) (h Int))
  Return_Left_keys_top_GETINAOUT
  (let
    ((__self_state (composition-pkgstate-Left-keys_top __global_state)))
    (let
      (
        (__self_state
          (mk-state-Left-keys_top
            (state-Left-keys_top-T __self_state)
            (state-Left-keys_top-z __self_state)
            (store (state-Left-keys_top-aflag __self_state) h (mk-some true))
            (state-Left-keys_top-bflag __self_state))))
      (ite
        (or
          (= (select (state-Left-keys_top-aflag __self_state) h) (mk-some true))
          (= (select (state-Left-keys_top-bflag __self_state) h) (mk-some true)))
        (let
          ((unwrap-1 (maybe-get (select (state-Left-keys_top-T __self_state) h))))
          (let
            ((Z unwrap-1))
            (let
              ((unwrap-2 (maybe-get (select (state-Left-keys_top-z __self_state) h))))
              (let
                ((zz unwrap-2))
                (let
                  ((unwrap-3 (maybe-get (select Z (not zz)))))
                  (let
                    ((k unwrap-3))
                    (let
                      (
                        (__global_state
                          (mk-composition-state-Left
                            __self_state
                            (composition-pkgstate-Left-keys_bottom __global_state)
                            (composition-pkgstate-Left-gate __global_state)
                            (composition-pkgstate-Left-enc __global_state)
                            (composition-param-Left-zerom __global_state)
                            (composition-param-Left-m __global_state)
                            (composition-param-Left-p __global_state)
                            (composition-param-Left-n __global_state)
                            (composition-param-Left-zeron __global_state)
                            (composition-rand-Left-0 __global_state)
                            (composition-rand-Left-1 __global_state)
                            (composition-rand-Left-2 __global_state)
                            (composition-rand-Left-3 __global_state)
                            (composition-rand-Left-4 __global_state)
                            (composition-rand-Left-5 __global_state)
                            (composition-rand-Left-6 __global_state))))
                      (mk-return-Left-keys_top-GETINAOUT __global_state k))))))))
        mk-abort-Left-keys_top-GETINAOUT))))
(define-fun
  oracle-Left-keys_top-GETAIN
  ((__global_state CompositionState-Left) (h Int))
  Return_Left_keys_top_GETAIN
  (let
    ((__self_state (composition-pkgstate-Left-keys_top __global_state)))
    (ite
      (= (select (state-Left-keys_top-aflag __self_state) h) (mk-some true))
      (ite
        (or
          (= (select (state-Left-keys_top-aflag __self_state) h) (mk-some true))
          (= (select (state-Left-keys_top-bflag __self_state) h) (mk-some true)))
        (let
          ((unwrap-1 (maybe-get (select (state-Left-keys_top-T __self_state) h))))
          (let
            ((Z unwrap-1))
            (let
              ((unwrap-2 (maybe-get (select (state-Left-keys_top-z __self_state) h))))
              (let
                ((zz unwrap-2))
                (let
                  ((unwrap-3 (maybe-get (select Z zz))))
                  (let
                    ((k unwrap-3))
                    (let
                      (
                        (__global_state
                          (mk-composition-state-Left
                            __self_state
                            (composition-pkgstate-Left-keys_bottom __global_state)
                            (composition-pkgstate-Left-gate __global_state)
                            (composition-pkgstate-Left-enc __global_state)
                            (composition-param-Left-zerom __global_state)
                            (composition-param-Left-m __global_state)
                            (composition-param-Left-p __global_state)
                            (composition-param-Left-n __global_state)
                            (composition-param-Left-zeron __global_state)
                            (composition-rand-Left-0 __global_state)
                            (composition-rand-Left-1 __global_state)
                            (composition-rand-Left-2 __global_state)
                            (composition-rand-Left-3 __global_state)
                            (composition-rand-Left-4 __global_state)
                            (composition-rand-Left-5 __global_state)
                            (composition-rand-Left-6 __global_state))))
                      (mk-return-Left-keys_top-GETAIN __global_state k))))))))
        mk-abort-Left-keys_top-GETAIN)
      mk-abort-Left-keys_top-GETAIN)))
(define-fun
  oracle-Left-keys_top-GETINAIN
  ((__global_state CompositionState-Left) (h Int))
  Return_Left_keys_top_GETINAIN
  (let
    ((__self_state (composition-pkgstate-Left-keys_top __global_state)))
    (ite
      (= (select (state-Left-keys_top-aflag __self_state) h) (mk-some true))
      (ite
        (or
          (= (select (state-Left-keys_top-aflag __self_state) h) (mk-some true))
          (= (select (state-Left-keys_top-bflag __self_state) h) (mk-some true)))
        (let
          ((unwrap-1 (maybe-get (select (state-Left-keys_top-T __self_state) h))))
          (let
            ((Z unwrap-1))
            (let
              ((unwrap-2 (maybe-get (select (state-Left-keys_top-z __self_state) h))))
              (let
                ((zz unwrap-2))
                (let
                  ((unwrap-3 (maybe-get (select Z (not zz)))))
                  (let
                    ((k unwrap-3))
                    (let
                      (
                        (__global_state
                          (mk-composition-state-Left
                            __self_state
                            (composition-pkgstate-Left-keys_bottom __global_state)
                            (composition-pkgstate-Left-gate __global_state)
                            (composition-pkgstate-Left-enc __global_state)
                            (composition-param-Left-zerom __global_state)
                            (composition-param-Left-m __global_state)
                            (composition-param-Left-p __global_state)
                            (composition-param-Left-n __global_state)
                            (composition-param-Left-zeron __global_state)
                            (composition-rand-Left-0 __global_state)
                            (composition-rand-Left-1 __global_state)
                            (composition-rand-Left-2 __global_state)
                            (composition-rand-Left-3 __global_state)
                            (composition-rand-Left-4 __global_state)
                            (composition-rand-Left-5 __global_state)
                            (composition-rand-Left-6 __global_state))))
                      (mk-return-Left-keys_top-GETINAIN __global_state k))))))))
        mk-abort-Left-keys_top-GETINAIN)
      mk-abort-Left-keys_top-GETINAIN)))
(define-fun
  oracle-Left-keys_top-GETBIT
  ((__global_state CompositionState-Left) (h Int))
  Return_Left_keys_top_GETBIT
  (let
    ((__self_state (composition-pkgstate-Left-keys_top __global_state)))
    (ite
      (not
        (= (select (state-Left-keys_top-z __self_state) h) (as mk-none (Maybe Bool))))
      (let
        ((unwrap-1 (maybe-get (select (state-Left-keys_top-z __self_state) h))))
        (let
          ((zz unwrap-1))
          (let
            (
              (__global_state
                (mk-composition-state-Left
                  __self_state
                  (composition-pkgstate-Left-keys_bottom __global_state)
                  (composition-pkgstate-Left-gate __global_state)
                  (composition-pkgstate-Left-enc __global_state)
                  (composition-param-Left-zerom __global_state)
                  (composition-param-Left-m __global_state)
                  (composition-param-Left-p __global_state)
                  (composition-param-Left-n __global_state)
                  (composition-param-Left-zeron __global_state)
                  (composition-rand-Left-0 __global_state)
                  (composition-rand-Left-1 __global_state)
                  (composition-rand-Left-2 __global_state)
                  (composition-rand-Left-3 __global_state)
                  (composition-rand-Left-4 __global_state)
                  (composition-rand-Left-5 __global_state)
                  (composition-rand-Left-6 __global_state))))
            (mk-return-Left-keys_top-GETBIT __global_state zz))))
      mk-abort-Left-keys_top-GETBIT)))
(define-fun
  oracle-Left-keys_top-SETBIT
  ((__global_state CompositionState-Left) (h Int) (zz Bool))
  Return_Left_keys_top_SETBIT
  (let
    ((__self_state (composition-pkgstate-Left-keys_top __global_state)))
    (ite
      (= (select (state-Left-keys_top-z __self_state) h) (as mk-none (Maybe Bool)))
      (let
        (
          (__self_state
            (mk-state-Left-keys_top
              (state-Left-keys_top-T __self_state)
              (store (state-Left-keys_top-z __self_state) h (mk-some zz))
              (state-Left-keys_top-aflag __self_state)
              (state-Left-keys_top-bflag __self_state))))
        (mk-return-Left-keys_top-SETBIT __global_state))
      mk-abort-Left-keys_top-SETBIT)))
(define-fun
  oracle-Left-keys_bottom-GETKEYSIN
  ((__global_state CompositionState-Left) (h Int))
  Return_Left_keys_bottom_GETKEYSIN
  (let
    ((__self_state (composition-pkgstate-Left-keys_bottom __global_state)))
    (ite
      (not
        (=
          (select (state-Left-keys_bottom-z __self_state) h)
          (as mk-none (Maybe Bool))))
      (ite
        (or
          (= (select (state-Left-keys_bottom-aflag __self_state) h) (mk-some true))
          (= (select (state-Left-keys_bottom-bflag __self_state) h) (mk-some true)))
        (let
          ((unwrap-1 (maybe-get (select (state-Left-keys_bottom-T __self_state) h))))
          (let
            ((Z unwrap-1))
            (let
              (
                (__global_state
                  (mk-composition-state-Left
                    (composition-pkgstate-Left-keys_top __global_state)
                    __self_state
                    (composition-pkgstate-Left-gate __global_state)
                    (composition-pkgstate-Left-enc __global_state)
                    (composition-param-Left-zerom __global_state)
                    (composition-param-Left-m __global_state)
                    (composition-param-Left-p __global_state)
                    (composition-param-Left-n __global_state)
                    (composition-param-Left-zeron __global_state)
                    (composition-rand-Left-0 __global_state)
                    (composition-rand-Left-1 __global_state)
                    (composition-rand-Left-2 __global_state)
                    (composition-rand-Left-3 __global_state)
                    (composition-rand-Left-4 __global_state)
                    (composition-rand-Left-5 __global_state)
                    (composition-rand-Left-6 __global_state))))
              (mk-return-Left-keys_bottom-GETKEYSIN __global_state Z))))
        mk-abort-Left-keys_bottom-GETKEYSIN)
      mk-abort-Left-keys_bottom-GETKEYSIN)))
(define-fun
  oracle-Left-keys_bottom-GETKEYSOUT
  ((__global_state CompositionState-Left) (h Int))
  Return_Left_keys_bottom_GETKEYSOUT
  (let
    ((__self_state (composition-pkgstate-Left-keys_bottom __global_state)))
    (let
      (
        (__self_state
          (mk-state-Left-keys_bottom
            (state-Left-keys_bottom-T __self_state)
            (state-Left-keys_bottom-z __self_state)
            (store (state-Left-keys_bottom-aflag __self_state) h (mk-some true))
            (state-Left-keys_bottom-bflag __self_state))))
      (let
        ((Z ((as const (Array Bool (Maybe Bits_n))) (as mk-none (Maybe Bits_n)))))
        (ite
          (=
            (select (state-Left-keys_bottom-T __self_state) h)
            (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
          (let
            ((r (__sample-rand-Left-Bits_n 3 (composition-rand-Left-3 __global_state))))
            (let
              (
                (__global_state
                  (mk-composition-state-Left
                    (composition-pkgstate-Left-keys_top __global_state)
                    (composition-pkgstate-Left-keys_bottom __global_state)
                    (composition-pkgstate-Left-gate __global_state)
                    (composition-pkgstate-Left-enc __global_state)
                    (composition-param-Left-zerom __global_state)
                    (composition-param-Left-m __global_state)
                    (composition-param-Left-p __global_state)
                    (composition-param-Left-n __global_state)
                    (composition-param-Left-zeron __global_state)
                    (composition-rand-Left-0 __global_state)
                    (composition-rand-Left-1 __global_state)
                    (composition-rand-Left-2 __global_state)
                    (+ 1 (composition-rand-Left-3 __global_state))
                    (composition-rand-Left-4 __global_state)
                    (composition-rand-Left-5 __global_state)
                    (composition-rand-Left-6 __global_state))))
              (let
                ((Z ((as const (Array Bool (Maybe Bits_n))) (as mk-none (Maybe Bits_n)))))
                (let
                  ((Z (store Z true (mk-some r))))
                  (let
                    ((rr (__sample-rand-Left-Bits_n 4 (composition-rand-Left-4 __global_state))))
                    (let
                      (
                        (__global_state
                          (mk-composition-state-Left
                            (composition-pkgstate-Left-keys_top __global_state)
                            (composition-pkgstate-Left-keys_bottom __global_state)
                            (composition-pkgstate-Left-gate __global_state)
                            (composition-pkgstate-Left-enc __global_state)
                            (composition-param-Left-zerom __global_state)
                            (composition-param-Left-m __global_state)
                            (composition-param-Left-p __global_state)
                            (composition-param-Left-n __global_state)
                            (composition-param-Left-zeron __global_state)
                            (composition-rand-Left-0 __global_state)
                            (composition-rand-Left-1 __global_state)
                            (composition-rand-Left-2 __global_state)
                            (composition-rand-Left-3 __global_state)
                            (+ 1 (composition-rand-Left-4 __global_state))
                            (composition-rand-Left-5 __global_state)
                            (composition-rand-Left-6 __global_state))))
                      (let
                        ((Z ((as const (Array Bool (Maybe Bits_n))) (as mk-none (Maybe Bits_n)))))
                        (let
                          ((Z (store Z false (mk-some rr))))
                          (let
                            (
                              (__self_state
                                (mk-state-Left-keys_bottom
                                  (store (state-Left-keys_bottom-T __self_state) h (mk-some Z))
                                  (state-Left-keys_bottom-z __self_state)
                                  (state-Left-keys_bottom-aflag __self_state)
                                  (state-Left-keys_bottom-bflag __self_state))))
                            (let
                              ((unwrap-1 (maybe-get (select (state-Left-keys_bottom-T __self_state) h))))
                              (let
                                ((Z unwrap-1))
                                (let
                                  (
                                    (__global_state
                                      (mk-composition-state-Left
                                        (composition-pkgstate-Left-keys_top __global_state)
                                        __self_state
                                        (composition-pkgstate-Left-gate __global_state)
                                        (composition-pkgstate-Left-enc __global_state)
                                        (composition-param-Left-zerom __global_state)
                                        (composition-param-Left-m __global_state)
                                        (composition-param-Left-p __global_state)
                                        (composition-param-Left-n __global_state)
                                        (composition-param-Left-zeron __global_state)
                                        (composition-rand-Left-0 __global_state)
                                        (composition-rand-Left-1 __global_state)
                                        (composition-rand-Left-2 __global_state)
                                        (composition-rand-Left-3 __global_state)
                                        (composition-rand-Left-4 __global_state)
                                        (composition-rand-Left-5 __global_state)
                                        (composition-rand-Left-6 __global_state))))
                                  (mk-return-Left-keys_bottom-GETKEYSOUT __global_state Z)))))))))))))
          (let
            ((unwrap-1 (maybe-get (select (state-Left-keys_bottom-T __self_state) h))))
            (let
              ((Z unwrap-1))
              (let
                (
                  (__global_state
                    (mk-composition-state-Left
                      (composition-pkgstate-Left-keys_top __global_state)
                      __self_state
                      (composition-pkgstate-Left-gate __global_state)
                      (composition-pkgstate-Left-enc __global_state)
                      (composition-param-Left-zerom __global_state)
                      (composition-param-Left-m __global_state)
                      (composition-param-Left-p __global_state)
                      (composition-param-Left-n __global_state)
                      (composition-param-Left-zeron __global_state)
                      (composition-rand-Left-0 __global_state)
                      (composition-rand-Left-1 __global_state)
                      (composition-rand-Left-2 __global_state)
                      (composition-rand-Left-3 __global_state)
                      (composition-rand-Left-4 __global_state)
                      (composition-rand-Left-5 __global_state)
                      (composition-rand-Left-6 __global_state))))
                (mk-return-Left-keys_bottom-GETKEYSOUT __global_state Z)))))))))
(define-fun
  oracle-Left-keys_bottom-GETAOUT
  ((__global_state CompositionState-Left) (h Int))
  Return_Left_keys_bottom_GETAOUT
  (let
    ((__self_state (composition-pkgstate-Left-keys_bottom __global_state)))
    (let
      (
        (__self_state
          (mk-state-Left-keys_bottom
            (state-Left-keys_bottom-T __self_state)
            (state-Left-keys_bottom-z __self_state)
            (store (state-Left-keys_bottom-aflag __self_state) h (mk-some true))
            (state-Left-keys_bottom-bflag __self_state))))
      (ite
        (or
          (= (select (state-Left-keys_bottom-aflag __self_state) h) (mk-some true))
          (= (select (state-Left-keys_bottom-bflag __self_state) h) (mk-some true)))
        (let
          ((unwrap-1 (maybe-get (select (state-Left-keys_bottom-T __self_state) h))))
          (let
            ((Z unwrap-1))
            (let
              ((unwrap-2 (maybe-get (select (state-Left-keys_bottom-z __self_state) h))))
              (let
                ((zz unwrap-2))
                (let
                  ((unwrap-3 (maybe-get (select Z zz))))
                  (let
                    ((k unwrap-3))
                    (let
                      (
                        (__global_state
                          (mk-composition-state-Left
                            (composition-pkgstate-Left-keys_top __global_state)
                            __self_state
                            (composition-pkgstate-Left-gate __global_state)
                            (composition-pkgstate-Left-enc __global_state)
                            (composition-param-Left-zerom __global_state)
                            (composition-param-Left-m __global_state)
                            (composition-param-Left-p __global_state)
                            (composition-param-Left-n __global_state)
                            (composition-param-Left-zeron __global_state)
                            (composition-rand-Left-0 __global_state)
                            (composition-rand-Left-1 __global_state)
                            (composition-rand-Left-2 __global_state)
                            (composition-rand-Left-3 __global_state)
                            (composition-rand-Left-4 __global_state)
                            (composition-rand-Left-5 __global_state)
                            (composition-rand-Left-6 __global_state))))
                      (mk-return-Left-keys_bottom-GETAOUT __global_state k))))))))
        mk-abort-Left-keys_bottom-GETAOUT))))
(define-fun
  oracle-Left-keys_bottom-GETINAOUT
  ((__global_state CompositionState-Left) (h Int))
  Return_Left_keys_bottom_GETINAOUT
  (let
    ((__self_state (composition-pkgstate-Left-keys_bottom __global_state)))
    (let
      (
        (__self_state
          (mk-state-Left-keys_bottom
            (state-Left-keys_bottom-T __self_state)
            (state-Left-keys_bottom-z __self_state)
            (store (state-Left-keys_bottom-aflag __self_state) h (mk-some true))
            (state-Left-keys_bottom-bflag __self_state))))
      (ite
        (or
          (= (select (state-Left-keys_bottom-aflag __self_state) h) (mk-some true))
          (= (select (state-Left-keys_bottom-bflag __self_state) h) (mk-some true)))
        (let
          ((unwrap-1 (maybe-get (select (state-Left-keys_bottom-T __self_state) h))))
          (let
            ((Z unwrap-1))
            (let
              ((unwrap-2 (maybe-get (select (state-Left-keys_bottom-z __self_state) h))))
              (let
                ((zz unwrap-2))
                (let
                  ((unwrap-3 (maybe-get (select Z (not zz)))))
                  (let
                    ((k unwrap-3))
                    (let
                      (
                        (__global_state
                          (mk-composition-state-Left
                            (composition-pkgstate-Left-keys_top __global_state)
                            __self_state
                            (composition-pkgstate-Left-gate __global_state)
                            (composition-pkgstate-Left-enc __global_state)
                            (composition-param-Left-zerom __global_state)
                            (composition-param-Left-m __global_state)
                            (composition-param-Left-p __global_state)
                            (composition-param-Left-n __global_state)
                            (composition-param-Left-zeron __global_state)
                            (composition-rand-Left-0 __global_state)
                            (composition-rand-Left-1 __global_state)
                            (composition-rand-Left-2 __global_state)
                            (composition-rand-Left-3 __global_state)
                            (composition-rand-Left-4 __global_state)
                            (composition-rand-Left-5 __global_state)
                            (composition-rand-Left-6 __global_state))))
                      (mk-return-Left-keys_bottom-GETINAOUT __global_state k))))))))
        mk-abort-Left-keys_bottom-GETINAOUT))))
(define-fun
  oracle-Left-keys_bottom-GETAIN
  ((__global_state CompositionState-Left) (h Int))
  Return_Left_keys_bottom_GETAIN
  (let
    ((__self_state (composition-pkgstate-Left-keys_bottom __global_state)))
    (ite
      (= (select (state-Left-keys_bottom-aflag __self_state) h) (mk-some true))
      (ite
        (or
          (= (select (state-Left-keys_bottom-aflag __self_state) h) (mk-some true))
          (= (select (state-Left-keys_bottom-bflag __self_state) h) (mk-some true)))
        (let
          ((unwrap-1 (maybe-get (select (state-Left-keys_bottom-T __self_state) h))))
          (let
            ((Z unwrap-1))
            (let
              ((unwrap-2 (maybe-get (select (state-Left-keys_bottom-z __self_state) h))))
              (let
                ((zz unwrap-2))
                (let
                  ((unwrap-3 (maybe-get (select Z zz))))
                  (let
                    ((k unwrap-3))
                    (let
                      (
                        (__global_state
                          (mk-composition-state-Left
                            (composition-pkgstate-Left-keys_top __global_state)
                            __self_state
                            (composition-pkgstate-Left-gate __global_state)
                            (composition-pkgstate-Left-enc __global_state)
                            (composition-param-Left-zerom __global_state)
                            (composition-param-Left-m __global_state)
                            (composition-param-Left-p __global_state)
                            (composition-param-Left-n __global_state)
                            (composition-param-Left-zeron __global_state)
                            (composition-rand-Left-0 __global_state)
                            (composition-rand-Left-1 __global_state)
                            (composition-rand-Left-2 __global_state)
                            (composition-rand-Left-3 __global_state)
                            (composition-rand-Left-4 __global_state)
                            (composition-rand-Left-5 __global_state)
                            (composition-rand-Left-6 __global_state))))
                      (mk-return-Left-keys_bottom-GETAIN __global_state k))))))))
        mk-abort-Left-keys_bottom-GETAIN)
      mk-abort-Left-keys_bottom-GETAIN)))
(define-fun
  oracle-Left-keys_bottom-GETINAIN
  ((__global_state CompositionState-Left) (h Int))
  Return_Left_keys_bottom_GETINAIN
  (let
    ((__self_state (composition-pkgstate-Left-keys_bottom __global_state)))
    (ite
      (= (select (state-Left-keys_bottom-aflag __self_state) h) (mk-some true))
      (ite
        (or
          (= (select (state-Left-keys_bottom-aflag __self_state) h) (mk-some true))
          (= (select (state-Left-keys_bottom-bflag __self_state) h) (mk-some true)))
        (let
          ((unwrap-1 (maybe-get (select (state-Left-keys_bottom-T __self_state) h))))
          (let
            ((Z unwrap-1))
            (let
              ((unwrap-2 (maybe-get (select (state-Left-keys_bottom-z __self_state) h))))
              (let
                ((zz unwrap-2))
                (let
                  ((unwrap-3 (maybe-get (select Z (not zz)))))
                  (let
                    ((k unwrap-3))
                    (let
                      (
                        (__global_state
                          (mk-composition-state-Left
                            (composition-pkgstate-Left-keys_top __global_state)
                            __self_state
                            (composition-pkgstate-Left-gate __global_state)
                            (composition-pkgstate-Left-enc __global_state)
                            (composition-param-Left-zerom __global_state)
                            (composition-param-Left-m __global_state)
                            (composition-param-Left-p __global_state)
                            (composition-param-Left-n __global_state)
                            (composition-param-Left-zeron __global_state)
                            (composition-rand-Left-0 __global_state)
                            (composition-rand-Left-1 __global_state)
                            (composition-rand-Left-2 __global_state)
                            (composition-rand-Left-3 __global_state)
                            (composition-rand-Left-4 __global_state)
                            (composition-rand-Left-5 __global_state)
                            (composition-rand-Left-6 __global_state))))
                      (mk-return-Left-keys_bottom-GETINAIN __global_state k))))))))
        mk-abort-Left-keys_bottom-GETINAIN)
      mk-abort-Left-keys_bottom-GETINAIN)))
(define-fun
  oracle-Left-keys_bottom-GETBIT
  ((__global_state CompositionState-Left) (h Int))
  Return_Left_keys_bottom_GETBIT
  (let
    ((__self_state (composition-pkgstate-Left-keys_bottom __global_state)))
    (ite
      (not
        (=
          (select (state-Left-keys_bottom-z __self_state) h)
          (as mk-none (Maybe Bool))))
      (let
        ((unwrap-1 (maybe-get (select (state-Left-keys_bottom-z __self_state) h))))
        (let
          ((zz unwrap-1))
          (let
            (
              (__global_state
                (mk-composition-state-Left
                  (composition-pkgstate-Left-keys_top __global_state)
                  __self_state
                  (composition-pkgstate-Left-gate __global_state)
                  (composition-pkgstate-Left-enc __global_state)
                  (composition-param-Left-zerom __global_state)
                  (composition-param-Left-m __global_state)
                  (composition-param-Left-p __global_state)
                  (composition-param-Left-n __global_state)
                  (composition-param-Left-zeron __global_state)
                  (composition-rand-Left-0 __global_state)
                  (composition-rand-Left-1 __global_state)
                  (composition-rand-Left-2 __global_state)
                  (composition-rand-Left-3 __global_state)
                  (composition-rand-Left-4 __global_state)
                  (composition-rand-Left-5 __global_state)
                  (composition-rand-Left-6 __global_state))))
            (mk-return-Left-keys_bottom-GETBIT __global_state zz))))
      mk-abort-Left-keys_bottom-GETBIT)))
(define-fun
  oracle-Left-keys_bottom-SETBIT
  ((__global_state CompositionState-Left) (h Int) (zz Bool))
  Return_Left_keys_bottom_SETBIT
  (let
    ((__self_state (composition-pkgstate-Left-keys_bottom __global_state)))
    (ite
      (=
        (select (state-Left-keys_bottom-z __self_state) h)
        (as mk-none (Maybe Bool)))
      (let
        (
          (__self_state
            (mk-state-Left-keys_bottom
              (state-Left-keys_bottom-T __self_state)
              (store (state-Left-keys_bottom-z __self_state) h (mk-some zz))
              (state-Left-keys_bottom-aflag __self_state)
              (state-Left-keys_bottom-bflag __self_state))))
        (mk-return-Left-keys_bottom-SETBIT __global_state))
      mk-abort-Left-keys_bottom-SETBIT)))
(define-fun
  oracle-Left-enc-ENCN
  (
    (__global_state CompositionState-Left)
    (j Int)
    (d Bool)
    (nzero Bits_n)
    (none Bits_n))
  Return_Left_enc_ENCN
  (let
    ((__self_state (composition-pkgstate-Left-enc __global_state)))
    (let
      ((__ret (oracle-Left-keys_top-GETKEYSIN __global_state j)))
      (ite
        (= __ret mk-abort-Left-keys_top-GETKEYSIN)
        mk-abort-Left-enc-ENCN
        (let
          (
            (__global_state (return-Left-keys_top-GETKEYSIN-state __ret))
            (K (return-Left-keys_top-GETKEYSIN-value __ret)))
          (let
            ((r (__sample-rand-Left-Bits_n 5 (composition-rand-Left-5 __global_state))))
            (let
              (
                (__global_state
                  (mk-composition-state-Left
                    (composition-pkgstate-Left-keys_top __global_state)
                    (composition-pkgstate-Left-keys_bottom __global_state)
                    (composition-pkgstate-Left-gate __global_state)
                    (composition-pkgstate-Left-enc __global_state)
                    (composition-param-Left-zerom __global_state)
                    (composition-param-Left-m __global_state)
                    (composition-param-Left-p __global_state)
                    (composition-param-Left-n __global_state)
                    (composition-param-Left-zeron __global_state)
                    (composition-rand-Left-0 __global_state)
                    (composition-rand-Left-1 __global_state)
                    (composition-rand-Left-2 __global_state)
                    (composition-rand-Left-3 __global_state)
                    (composition-rand-Left-4 __global_state)
                    (+ 1 (composition-rand-Left-5 __global_state))
                    (composition-rand-Left-6 __global_state))))
              (let
                ((unwrap-1 (maybe-get (select K d))))
                (let
                  ((c (__func-Left-encn unwrap-1 nzero r)))
                  (let
                    (
                      (__global_state
                        (mk-composition-state-Left
                          (composition-pkgstate-Left-keys_top __global_state)
                          (composition-pkgstate-Left-keys_bottom __global_state)
                          (composition-pkgstate-Left-gate __global_state)
                          __self_state
                          (composition-param-Left-zerom __global_state)
                          (composition-param-Left-m __global_state)
                          (composition-param-Left-p __global_state)
                          (composition-param-Left-n __global_state)
                          (composition-param-Left-zeron __global_state)
                          (composition-rand-Left-0 __global_state)
                          (composition-rand-Left-1 __global_state)
                          (composition-rand-Left-2 __global_state)
                          (composition-rand-Left-3 __global_state)
                          (composition-rand-Left-4 __global_state)
                          (composition-rand-Left-5 __global_state)
                          (composition-rand-Left-6 __global_state))))
                    (mk-return-Left-enc-ENCN __global_state c)))))))))))
(define-fun
  oracle-Left-enc-ENCM
  (
    (__global_state CompositionState-Left)
    (j Int)
    (d Bool)
    (mzero Bits_m)
    (mone Bits_m))
  Return_Left_enc_ENCM
  (let
    ((__self_state (composition-pkgstate-Left-enc __global_state)))
    (let
      ((__ret (oracle-Left-keys_top-GETKEYSIN __global_state j)))
      (ite
        (= __ret mk-abort-Left-keys_top-GETKEYSIN)
        mk-abort-Left-enc-ENCM
        (let
          (
            (__global_state (return-Left-keys_top-GETKEYSIN-state __ret))
            (K (return-Left-keys_top-GETKEYSIN-value __ret)))
          (let
            ((r (__sample-rand-Left-Bits_n 6 (composition-rand-Left-6 __global_state))))
            (let
              (
                (__global_state
                  (mk-composition-state-Left
                    (composition-pkgstate-Left-keys_top __global_state)
                    (composition-pkgstate-Left-keys_bottom __global_state)
                    (composition-pkgstate-Left-gate __global_state)
                    (composition-pkgstate-Left-enc __global_state)
                    (composition-param-Left-zerom __global_state)
                    (composition-param-Left-m __global_state)
                    (composition-param-Left-p __global_state)
                    (composition-param-Left-n __global_state)
                    (composition-param-Left-zeron __global_state)
                    (composition-rand-Left-0 __global_state)
                    (composition-rand-Left-1 __global_state)
                    (composition-rand-Left-2 __global_state)
                    (composition-rand-Left-3 __global_state)
                    (composition-rand-Left-4 __global_state)
                    (composition-rand-Left-5 __global_state)
                    (+ 1 (composition-rand-Left-6 __global_state)))))
              (let
                ((unwrap-1 (maybe-get (select K d))))
                (let
                  ((c (__func-Left-encm unwrap-1 mzero r)))
                  (let
                    (
                      (__global_state
                        (mk-composition-state-Left
                          (composition-pkgstate-Left-keys_top __global_state)
                          (composition-pkgstate-Left-keys_bottom __global_state)
                          (composition-pkgstate-Left-gate __global_state)
                          __self_state
                          (composition-param-Left-zerom __global_state)
                          (composition-param-Left-m __global_state)
                          (composition-param-Left-p __global_state)
                          (composition-param-Left-n __global_state)
                          (composition-param-Left-zeron __global_state)
                          (composition-rand-Left-0 __global_state)
                          (composition-rand-Left-1 __global_state)
                          (composition-rand-Left-2 __global_state)
                          (composition-rand-Left-3 __global_state)
                          (composition-rand-Left-4 __global_state)
                          (composition-rand-Left-5 __global_state)
                          (composition-rand-Left-6 __global_state))))
                    (mk-return-Left-enc-ENCM __global_state c)))))))))))
(define-fun
  oracle-Left-gate-GBLG
  (
    (__global_state CompositionState-Left)
    (h Int)
    (l Int)
    (r Int)
    (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
    (j Int))
  Return_Left_gate_GBLG
  (let
    ((__self_state (composition-pkgstate-Left-gate __global_state)))
    (let
      ((C ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))))
      (let
        ((__ret (oracle-Left-keys_bottom-GETKEYSOUT __global_state j)))
        (ite
          (= __ret mk-abort-Left-keys_bottom-GETKEYSOUT)
          mk-abort-Left-gate-GBLG
          (let
            (
              (__global_state (return-Left-keys_bottom-GETKEYSOUT-state __ret))
              (Z (return-Left-keys_bottom-GETKEYSOUT-value __ret)))
            (let
              ((bl false))
              (let
                ((br false))
                (let
                  ((unwrap-1 (maybe-get (select op (mk-tuple2 bl br)))))
                  (let
                    ((bj unwrap-1))
                    (let
                      ((unwrap-2 (maybe-get (select Z bj))))
                      (let
                        ((kzero unwrap-2))
                        (let
                          (
                            (__ret
                              (oracle-Left-enc-ENCN
                                __global_state
                                l
                                bl
                                kzero
                                (composition-param-Left-zeron __global_state))))
                          (ite
                            (= __ret mk-abort-Left-enc-ENCN)
                            mk-abort-Left-gate-GBLG
                            (let
                              (
                                (__global_state (return-Left-enc-ENCN-state __ret))
                                (czeroin (return-Left-enc-ENCN-value __ret)))
                              (let
                                (
                                  (__ret
                                    (oracle-Left-enc-ENCN
                                      __global_state
                                      l
                                      bl
                                      (composition-param-Left-zeron __global_state)
                                      (composition-param-Left-zeron __global_state))))
                                (ite
                                  (= __ret mk-abort-Left-enc-ENCN)
                                  mk-abort-Left-gate-GBLG
                                  (let
                                    (
                                      (__global_state (return-Left-enc-ENCN-state __ret))
                                      (conein (return-Left-enc-ENCN-value __ret)))
                                    (let
                                      ((__ret (oracle-Left-enc-ENCM __global_state r br conein czeroin)))
                                      (ite
                                        (= __ret mk-abort-Left-enc-ENCM)
                                        mk-abort-Left-gate-GBLG
                                        (let
                                          (
                                            (__global_state (return-Left-enc-ENCM-state __ret))
                                            (cout (return-Left-enc-ENCM-value __ret)))
                                          (let
                                            ((C ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))))
                                            (let
                                              ((C (store C cout (mk-some true))))
                                              (let
                                                ((bl true))
                                                (let
                                                  ((br false))
                                                  (let
                                                    ((unwrap-3 (maybe-get (select op (mk-tuple2 bl br)))))
                                                    (let
                                                      ((bj unwrap-3))
                                                      (let
                                                        ((unwrap-4 (maybe-get (select Z bj))))
                                                        (let
                                                          ((kzero unwrap-4))
                                                          (let
                                                            (
                                                              (__ret
                                                                (oracle-Left-enc-ENCN
                                                                  __global_state
                                                                  l
                                                                  bl
                                                                  kzero
                                                                  (composition-param-Left-zeron __global_state))))
                                                            (ite
                                                              (= __ret mk-abort-Left-enc-ENCN)
                                                              mk-abort-Left-gate-GBLG
                                                              (let
                                                                (
                                                                  (__global_state (return-Left-enc-ENCN-state __ret))
                                                                  (czeroin (return-Left-enc-ENCN-value __ret)))
                                                                (let
                                                                  (
                                                                    (__ret
                                                                      (oracle-Left-enc-ENCN
                                                                        __global_state
                                                                        l
                                                                        bl
                                                                        (composition-param-Left-zeron __global_state)
                                                                        (composition-param-Left-zeron __global_state))))
                                                                  (ite
                                                                    (= __ret mk-abort-Left-enc-ENCN)
                                                                    mk-abort-Left-gate-GBLG
                                                                    (let
                                                                      (
                                                                        (__global_state (return-Left-enc-ENCN-state __ret))
                                                                        (conein (return-Left-enc-ENCN-value __ret)))
                                                                      (let
                                                                        ((__ret (oracle-Left-enc-ENCM __global_state r br conein czeroin)))
                                                                        (ite
                                                                          (= __ret mk-abort-Left-enc-ENCM)
                                                                          mk-abort-Left-gate-GBLG
                                                                          (let
                                                                            (
                                                                              (__global_state (return-Left-enc-ENCM-state __ret))
                                                                              (cout (return-Left-enc-ENCM-value __ret)))
                                                                            (let
                                                                              ((C ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))))
                                                                              (let
                                                                                ((C (store C cout (mk-some true))))
                                                                                (let
                                                                                  ((bl false))
                                                                                  (let
                                                                                    ((br true))
                                                                                    (let
                                                                                      ((unwrap-5 (maybe-get (select op (mk-tuple2 bl br)))))
                                                                                      (let
                                                                                        ((bj unwrap-5))
                                                                                        (let
                                                                                          ((unwrap-6 (maybe-get (select Z bj))))
                                                                                          (let
                                                                                            ((kzero unwrap-6))
                                                                                            (let
                                                                                              (
                                                                                                (__ret
                                                                                                  (oracle-Left-enc-ENCN
                                                                                                    __global_state
                                                                                                    l
                                                                                                    bl
                                                                                                    kzero
                                                                                                    (composition-param-Left-zeron __global_state))))
                                                                                              (ite
                                                                                                (= __ret mk-abort-Left-enc-ENCN)
                                                                                                mk-abort-Left-gate-GBLG
                                                                                                (let
                                                                                                  (
                                                                                                    (__global_state (return-Left-enc-ENCN-state __ret))
                                                                                                    (czeroin (return-Left-enc-ENCN-value __ret)))
                                                                                                  (let
                                                                                                    (
                                                                                                      (__ret
                                                                                                        (oracle-Left-enc-ENCN
                                                                                                          __global_state
                                                                                                          l
                                                                                                          bl
                                                                                                          (composition-param-Left-zeron __global_state)
                                                                                                          (composition-param-Left-zeron __global_state))))
                                                                                                    (ite
                                                                                                      (= __ret mk-abort-Left-enc-ENCN)
                                                                                                      mk-abort-Left-gate-GBLG
                                                                                                      (let
                                                                                                        (
                                                                                                          (__global_state (return-Left-enc-ENCN-state __ret))
                                                                                                          (conein (return-Left-enc-ENCN-value __ret)))
                                                                                                        (let
                                                                                                          ((__ret (oracle-Left-enc-ENCM __global_state r br conein czeroin)))
                                                                                                          (ite
                                                                                                            (= __ret mk-abort-Left-enc-ENCM)
                                                                                                            mk-abort-Left-gate-GBLG
                                                                                                            (let
                                                                                                              (
                                                                                                                (__global_state (return-Left-enc-ENCM-state __ret))
                                                                                                                (cout (return-Left-enc-ENCM-value __ret)))
                                                                                                              (let
                                                                                                                ((C ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))))
                                                                                                                (let
                                                                                                                  ((C (store C cout (mk-some true))))
                                                                                                                  (let
                                                                                                                    ((bl true))
                                                                                                                    (let
                                                                                                                      ((br true))
                                                                                                                      (let
                                                                                                                        ((unwrap-7 (maybe-get (select op (mk-tuple2 bl br)))))
                                                                                                                        (let
                                                                                                                          ((bj unwrap-7))
                                                                                                                          (let
                                                                                                                            ((unwrap-8 (maybe-get (select Z bj))))
                                                                                                                            (let
                                                                                                                              ((kzero unwrap-8))
                                                                                                                              (let
                                                                                                                                (
                                                                                                                                  (__ret
                                                                                                                                    (oracle-Left-enc-ENCN
                                                                                                                                      __global_state
                                                                                                                                      l
                                                                                                                                      bl
                                                                                                                                      kzero
                                                                                                                                      (composition-param-Left-zeron __global_state))))
                                                                                                                                (ite
                                                                                                                                  (= __ret mk-abort-Left-enc-ENCN)
                                                                                                                                  mk-abort-Left-gate-GBLG
                                                                                                                                  (let
                                                                                                                                    (
                                                                                                                                      (__global_state (return-Left-enc-ENCN-state __ret))
                                                                                                                                      (czeroin (return-Left-enc-ENCN-value __ret)))
                                                                                                                                    (let
                                                                                                                                      (
                                                                                                                                        (__ret
                                                                                                                                          (oracle-Left-enc-ENCN
                                                                                                                                            __global_state
                                                                                                                                            l
                                                                                                                                            bl
                                                                                                                                            (composition-param-Left-zeron __global_state)
                                                                                                                                            (composition-param-Left-zeron __global_state))))
                                                                                                                                      (ite
                                                                                                                                        (= __ret mk-abort-Left-enc-ENCN)
                                                                                                                                        mk-abort-Left-gate-GBLG
                                                                                                                                        (let
                                                                                                                                          (
                                                                                                                                            (__global_state (return-Left-enc-ENCN-state __ret))
                                                                                                                                            (conein (return-Left-enc-ENCN-value __ret)))
                                                                                                                                          (let
                                                                                                                                            ((__ret (oracle-Left-enc-ENCM __global_state r br conein czeroin)))
                                                                                                                                            (ite
                                                                                                                                              (= __ret mk-abort-Left-enc-ENCM)
                                                                                                                                              mk-abort-Left-gate-GBLG
                                                                                                                                              (let
                                                                                                                                                (
                                                                                                                                                  (__global_state (return-Left-enc-ENCM-state __ret))
                                                                                                                                                  (cout (return-Left-enc-ENCM-value __ret)))
                                                                                                                                                (let
                                                                                                                                                  ((C ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))))
                                                                                                                                                  (let
                                                                                                                                                    ((C (store C cout (mk-some true))))
                                                                                                                                                    (let
                                                                                                                                                      (
                                                                                                                                                        (__global_state
                                                                                                                                                          (mk-composition-state-Left
                                                                                                                                                            (composition-pkgstate-Left-keys_top __global_state)
                                                                                                                                                            (composition-pkgstate-Left-keys_bottom __global_state)
                                                                                                                                                            __self_state
                                                                                                                                                            (composition-pkgstate-Left-enc __global_state)
                                                                                                                                                            (composition-param-Left-zerom __global_state)
                                                                                                                                                            (composition-param-Left-m __global_state)
                                                                                                                                                            (composition-param-Left-p __global_state)
                                                                                                                                                            (composition-param-Left-n __global_state)
                                                                                                                                                            (composition-param-Left-zeron __global_state)
                                                                                                                                                            (composition-rand-Left-0 __global_state)
                                                                                                                                                            (composition-rand-Left-1 __global_state)
                                                                                                                                                            (composition-rand-Left-2 __global_state)
                                                                                                                                                            (composition-rand-Left-3 __global_state)
                                                                                                                                                            (composition-rand-Left-4 __global_state)
                                                                                                                                                            (composition-rand-Left-5 __global_state)
                                                                                                                                                            (composition-rand-Left-6 __global_state))))
                                                                                                                                                      (mk-return-Left-gate-GBLG __global_state C)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))); Right
(declare-fun __sample-rand-Right-Bits_n (Int Int) Bits_n)
(declare-fun __func-Right-encm (Bits_n Bits_m Bits_n) Bits_p)
(declare-fun __func-Right-encn (Bits_n Bits_n Bits_n) Bits_m)
(declare-datatype
  State_Right_keys_top
  (
    (mk-state-Right-keys_top
      (state-Right-keys_top-T (Array Int (Maybe (Array Bool (Maybe Bits_n)))))
      (state-Right-keys_top-z (Array Int (Maybe Bool)))
      (state-Right-keys_top-aflag (Array Int (Maybe Bool)))
      (state-Right-keys_top-bflag (Array Int (Maybe Bool))))))
(declare-datatype
  State_Right_keys_bottom
  (
    (mk-state-Right-keys_bottom
      (state-Right-keys_bottom-T (Array Int (Maybe (Array Bool (Maybe Bits_n)))))
      (state-Right-keys_bottom-z (Array Int (Maybe Bool)))
      (state-Right-keys_bottom-aflag (Array Int (Maybe Bool)))
      (state-Right-keys_bottom-bflag (Array Int (Maybe Bool))))))
(declare-datatype State_Right_simgate ((mk-state-Right-simgate)))
(declare-datatype State_Right_ev ((mk-state-Right-ev)))
(declare-datatype
  CompositionState-Right
  (
    (mk-composition-state-Right
      (composition-pkgstate-Right-keys_top State_Right_keys_top)
      (composition-pkgstate-Right-keys_bottom State_Right_keys_bottom)
      (composition-pkgstate-Right-simgate State_Right_simgate)
      (composition-pkgstate-Right-ev State_Right_ev)
      (composition-param-Right-zeron Bits_n)
      (composition-param-Right-zerom Bits_m)
      (composition-param-Right-n Int)
      (composition-param-Right-p Int)
      (composition-param-Right-m Int)
      (composition-rand-Right-0 Int)
      (composition-rand-Right-1 Int)
      (composition-rand-Right-2 Int)
      (composition-rand-Right-3 Int)
      (composition-rand-Right-4 Int)
      (composition-rand-Right-5 Int)
      (composition-rand-Right-6 Int)
      (composition-rand-Right-7 Int)
      (composition-rand-Right-8 Int)
      (composition-rand-Right-9 Int)
      (composition-rand-Right-10 Int)
      (composition-rand-Right-11 Int)
      (composition-rand-Right-12 Int))))
(declare-datatype
  Return_Right_keys_top_GETKEYSIN
  (
    (mk-abort-Right-keys_top-GETKEYSIN)
    (mk-return-Right-keys_top-GETKEYSIN
      (return-Right-keys_top-GETKEYSIN-state CompositionState-Right)
      (return-Right-keys_top-GETKEYSIN-value (Array Bool (Maybe Bits_n))))))
(declare-datatype
  Return_Right_keys_top_GETKEYSOUT
  (
    (mk-abort-Right-keys_top-GETKEYSOUT)
    (mk-return-Right-keys_top-GETKEYSOUT
      (return-Right-keys_top-GETKEYSOUT-state CompositionState-Right)
      (return-Right-keys_top-GETKEYSOUT-value (Array Bool (Maybe Bits_n))))))
(declare-datatype
  Return_Right_keys_top_GETAOUT
  (
    (mk-abort-Right-keys_top-GETAOUT)
    (mk-return-Right-keys_top-GETAOUT
      (return-Right-keys_top-GETAOUT-state CompositionState-Right)
      (return-Right-keys_top-GETAOUT-value Bits_n))))
(declare-datatype
  Return_Right_keys_top_GETINAOUT
  (
    (mk-abort-Right-keys_top-GETINAOUT)
    (mk-return-Right-keys_top-GETINAOUT
      (return-Right-keys_top-GETINAOUT-state CompositionState-Right)
      (return-Right-keys_top-GETINAOUT-value Bits_n))))
(declare-datatype
  Return_Right_keys_top_GETAIN
  (
    (mk-abort-Right-keys_top-GETAIN)
    (mk-return-Right-keys_top-GETAIN
      (return-Right-keys_top-GETAIN-state CompositionState-Right)
      (return-Right-keys_top-GETAIN-value Bits_n))))
(declare-datatype
  Return_Right_keys_top_GETINAIN
  (
    (mk-abort-Right-keys_top-GETINAIN)
    (mk-return-Right-keys_top-GETINAIN
      (return-Right-keys_top-GETINAIN-state CompositionState-Right)
      (return-Right-keys_top-GETINAIN-value Bits_n))))
(declare-datatype
  Return_Right_keys_top_GETBIT
  (
    (mk-abort-Right-keys_top-GETBIT)
    (mk-return-Right-keys_top-GETBIT
      (return-Right-keys_top-GETBIT-state CompositionState-Right)
      (return-Right-keys_top-GETBIT-value Bool))))
(declare-datatype
  Return_Right_keys_top_SETBIT
  (
    (mk-abort-Right-keys_top-SETBIT)
    (mk-return-Right-keys_top-SETBIT
      (return-Right-keys_top-SETBIT-state CompositionState-Right))))
(declare-datatype
  Return_Right_keys_bottom_GETKEYSIN
  (
    (mk-abort-Right-keys_bottom-GETKEYSIN)
    (mk-return-Right-keys_bottom-GETKEYSIN
      (return-Right-keys_bottom-GETKEYSIN-state CompositionState-Right)
      (return-Right-keys_bottom-GETKEYSIN-value (Array Bool (Maybe Bits_n))))))
(declare-datatype
  Return_Right_keys_bottom_GETKEYSOUT
  (
    (mk-abort-Right-keys_bottom-GETKEYSOUT)
    (mk-return-Right-keys_bottom-GETKEYSOUT
      (return-Right-keys_bottom-GETKEYSOUT-state CompositionState-Right)
      (return-Right-keys_bottom-GETKEYSOUT-value (Array Bool (Maybe Bits_n))))))
(declare-datatype
  Return_Right_keys_bottom_GETAOUT
  (
    (mk-abort-Right-keys_bottom-GETAOUT)
    (mk-return-Right-keys_bottom-GETAOUT
      (return-Right-keys_bottom-GETAOUT-state CompositionState-Right)
      (return-Right-keys_bottom-GETAOUT-value Bits_n))))
(declare-datatype
  Return_Right_keys_bottom_GETINAOUT
  (
    (mk-abort-Right-keys_bottom-GETINAOUT)
    (mk-return-Right-keys_bottom-GETINAOUT
      (return-Right-keys_bottom-GETINAOUT-state CompositionState-Right)
      (return-Right-keys_bottom-GETINAOUT-value Bits_n))))
(declare-datatype
  Return_Right_keys_bottom_GETAIN
  (
    (mk-abort-Right-keys_bottom-GETAIN)
    (mk-return-Right-keys_bottom-GETAIN
      (return-Right-keys_bottom-GETAIN-state CompositionState-Right)
      (return-Right-keys_bottom-GETAIN-value Bits_n))))
(declare-datatype
  Return_Right_keys_bottom_GETINAIN
  (
    (mk-abort-Right-keys_bottom-GETINAIN)
    (mk-return-Right-keys_bottom-GETINAIN
      (return-Right-keys_bottom-GETINAIN-state CompositionState-Right)
      (return-Right-keys_bottom-GETINAIN-value Bits_n))))
(declare-datatype
  Return_Right_keys_bottom_GETBIT
  (
    (mk-abort-Right-keys_bottom-GETBIT)
    (mk-return-Right-keys_bottom-GETBIT
      (return-Right-keys_bottom-GETBIT-state CompositionState-Right)
      (return-Right-keys_bottom-GETBIT-value Bool))))
(declare-datatype
  Return_Right_keys_bottom_SETBIT
  (
    (mk-abort-Right-keys_bottom-SETBIT)
    (mk-return-Right-keys_bottom-SETBIT
      (return-Right-keys_bottom-SETBIT-state CompositionState-Right))))
(declare-datatype
  Return_Right_simgate_GBLG
  (
    (mk-abort-Right-simgate-GBLG)
    (mk-return-Right-simgate-GBLG
      (return-Right-simgate-GBLG-state CompositionState-Right)
      (return-Right-simgate-GBLG-value (Array Bits_p (Maybe Bool))))))
(declare-datatype
  Return_Right_ev_EVAL
  (
    (mk-abort-Right-ev-EVAL)
    (mk-return-Right-ev-EVAL (return-Right-ev-EVAL-state CompositionState-Right)))); Composition of Right
(define-fun
  oracle-Right-keys_top-GETKEYSIN
  ((__global_state CompositionState-Right) (h Int))
  Return_Right_keys_top_GETKEYSIN
  (let
    ((__self_state (composition-pkgstate-Right-keys_top __global_state)))
    (ite
      (not
        (= (select (state-Right-keys_top-z __self_state) h) (as mk-none (Maybe Bool))))
      (ite
        (or
          (= (select (state-Right-keys_top-aflag __self_state) h) (mk-some true))
          (= (select (state-Right-keys_top-bflag __self_state) h) (mk-some true)))
        (let
          ((unwrap-1 (maybe-get (select (state-Right-keys_top-T __self_state) h))))
          (let
            ((Z unwrap-1))
            (let
              (
                (__global_state
                  (mk-composition-state-Right
                    __self_state
                    (composition-pkgstate-Right-keys_bottom __global_state)
                    (composition-pkgstate-Right-simgate __global_state)
                    (composition-pkgstate-Right-ev __global_state)
                    (composition-param-Right-zeron __global_state)
                    (composition-param-Right-zerom __global_state)
                    (composition-param-Right-n __global_state)
                    (composition-param-Right-p __global_state)
                    (composition-param-Right-m __global_state)
                    (composition-rand-Right-0 __global_state)
                    (composition-rand-Right-1 __global_state)
                    (composition-rand-Right-2 __global_state)
                    (composition-rand-Right-3 __global_state)
                    (composition-rand-Right-4 __global_state)
                    (composition-rand-Right-5 __global_state)
                    (composition-rand-Right-6 __global_state)
                    (composition-rand-Right-7 __global_state)
                    (composition-rand-Right-8 __global_state)
                    (composition-rand-Right-9 __global_state)
                    (composition-rand-Right-10 __global_state)
                    (composition-rand-Right-11 __global_state)
                    (composition-rand-Right-12 __global_state))))
              (mk-return-Right-keys_top-GETKEYSIN __global_state Z))))
        mk-abort-Right-keys_top-GETKEYSIN)
      mk-abort-Right-keys_top-GETKEYSIN)))
(define-fun
  oracle-Right-keys_top-GETKEYSOUT
  ((__global_state CompositionState-Right) (h Int))
  Return_Right_keys_top_GETKEYSOUT
  (let
    ((__self_state (composition-pkgstate-Right-keys_top __global_state)))
    (let
      (
        (__self_state
          (mk-state-Right-keys_top
            (state-Right-keys_top-T __self_state)
            (state-Right-keys_top-z __self_state)
            (store (state-Right-keys_top-aflag __self_state) h (mk-some true))
            (state-Right-keys_top-bflag __self_state))))
      (let
        ((Z ((as const (Array Bool (Maybe Bits_n))) (as mk-none (Maybe Bits_n)))))
        (ite
          (=
            (select (state-Right-keys_top-T __self_state) h)
            (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
          (let
            ((r (__sample-rand-Right-Bits_n 1 (composition-rand-Right-1 __global_state))))
            (let
              (
                (__global_state
                  (mk-composition-state-Right
                    (composition-pkgstate-Right-keys_top __global_state)
                    (composition-pkgstate-Right-keys_bottom __global_state)
                    (composition-pkgstate-Right-simgate __global_state)
                    (composition-pkgstate-Right-ev __global_state)
                    (composition-param-Right-zeron __global_state)
                    (composition-param-Right-zerom __global_state)
                    (composition-param-Right-n __global_state)
                    (composition-param-Right-p __global_state)
                    (composition-param-Right-m __global_state)
                    (composition-rand-Right-0 __global_state)
                    (+ 1 (composition-rand-Right-1 __global_state))
                    (composition-rand-Right-2 __global_state)
                    (composition-rand-Right-3 __global_state)
                    (composition-rand-Right-4 __global_state)
                    (composition-rand-Right-5 __global_state)
                    (composition-rand-Right-6 __global_state)
                    (composition-rand-Right-7 __global_state)
                    (composition-rand-Right-8 __global_state)
                    (composition-rand-Right-9 __global_state)
                    (composition-rand-Right-10 __global_state)
                    (composition-rand-Right-11 __global_state)
                    (composition-rand-Right-12 __global_state))))
              (let
                ((Z ((as const (Array Bool (Maybe Bits_n))) (as mk-none (Maybe Bits_n)))))
                (let
                  ((Z (store Z true (mk-some r))))
                  (let
                    ((rr (__sample-rand-Right-Bits_n 2 (composition-rand-Right-2 __global_state))))
                    (let
                      (
                        (__global_state
                          (mk-composition-state-Right
                            (composition-pkgstate-Right-keys_top __global_state)
                            (composition-pkgstate-Right-keys_bottom __global_state)
                            (composition-pkgstate-Right-simgate __global_state)
                            (composition-pkgstate-Right-ev __global_state)
                            (composition-param-Right-zeron __global_state)
                            (composition-param-Right-zerom __global_state)
                            (composition-param-Right-n __global_state)
                            (composition-param-Right-p __global_state)
                            (composition-param-Right-m __global_state)
                            (composition-rand-Right-0 __global_state)
                            (composition-rand-Right-1 __global_state)
                            (+ 1 (composition-rand-Right-2 __global_state))
                            (composition-rand-Right-3 __global_state)
                            (composition-rand-Right-4 __global_state)
                            (composition-rand-Right-5 __global_state)
                            (composition-rand-Right-6 __global_state)
                            (composition-rand-Right-7 __global_state)
                            (composition-rand-Right-8 __global_state)
                            (composition-rand-Right-9 __global_state)
                            (composition-rand-Right-10 __global_state)
                            (composition-rand-Right-11 __global_state)
                            (composition-rand-Right-12 __global_state))))
                      (let
                        ((Z ((as const (Array Bool (Maybe Bits_n))) (as mk-none (Maybe Bits_n)))))
                        (let
                          ((Z (store Z false (mk-some rr))))
                          (let
                            (
                              (__self_state
                                (mk-state-Right-keys_top
                                  (store (state-Right-keys_top-T __self_state) h (mk-some Z))
                                  (state-Right-keys_top-z __self_state)
                                  (state-Right-keys_top-aflag __self_state)
                                  (state-Right-keys_top-bflag __self_state))))
                            (let
                              ((unwrap-1 (maybe-get (select (state-Right-keys_top-T __self_state) h))))
                              (let
                                ((Z unwrap-1))
                                (let
                                  (
                                    (__global_state
                                      (mk-composition-state-Right
                                        __self_state
                                        (composition-pkgstate-Right-keys_bottom __global_state)
                                        (composition-pkgstate-Right-simgate __global_state)
                                        (composition-pkgstate-Right-ev __global_state)
                                        (composition-param-Right-zeron __global_state)
                                        (composition-param-Right-zerom __global_state)
                                        (composition-param-Right-n __global_state)
                                        (composition-param-Right-p __global_state)
                                        (composition-param-Right-m __global_state)
                                        (composition-rand-Right-0 __global_state)
                                        (composition-rand-Right-1 __global_state)
                                        (composition-rand-Right-2 __global_state)
                                        (composition-rand-Right-3 __global_state)
                                        (composition-rand-Right-4 __global_state)
                                        (composition-rand-Right-5 __global_state)
                                        (composition-rand-Right-6 __global_state)
                                        (composition-rand-Right-7 __global_state)
                                        (composition-rand-Right-8 __global_state)
                                        (composition-rand-Right-9 __global_state)
                                        (composition-rand-Right-10 __global_state)
                                        (composition-rand-Right-11 __global_state)
                                        (composition-rand-Right-12 __global_state))))
                                  (mk-return-Right-keys_top-GETKEYSOUT __global_state Z)))))))))))))
          (let
            ((unwrap-1 (maybe-get (select (state-Right-keys_top-T __self_state) h))))
            (let
              ((Z unwrap-1))
              (let
                (
                  (__global_state
                    (mk-composition-state-Right
                      __self_state
                      (composition-pkgstate-Right-keys_bottom __global_state)
                      (composition-pkgstate-Right-simgate __global_state)
                      (composition-pkgstate-Right-ev __global_state)
                      (composition-param-Right-zeron __global_state)
                      (composition-param-Right-zerom __global_state)
                      (composition-param-Right-n __global_state)
                      (composition-param-Right-p __global_state)
                      (composition-param-Right-m __global_state)
                      (composition-rand-Right-0 __global_state)
                      (composition-rand-Right-1 __global_state)
                      (composition-rand-Right-2 __global_state)
                      (composition-rand-Right-3 __global_state)
                      (composition-rand-Right-4 __global_state)
                      (composition-rand-Right-5 __global_state)
                      (composition-rand-Right-6 __global_state)
                      (composition-rand-Right-7 __global_state)
                      (composition-rand-Right-8 __global_state)
                      (composition-rand-Right-9 __global_state)
                      (composition-rand-Right-10 __global_state)
                      (composition-rand-Right-11 __global_state)
                      (composition-rand-Right-12 __global_state))))
                (mk-return-Right-keys_top-GETKEYSOUT __global_state Z)))))))))
(define-fun
  oracle-Right-keys_top-GETAOUT
  ((__global_state CompositionState-Right) (h Int))
  Return_Right_keys_top_GETAOUT
  (let
    ((__self_state (composition-pkgstate-Right-keys_top __global_state)))
    (let
      (
        (__self_state
          (mk-state-Right-keys_top
            (state-Right-keys_top-T __self_state)
            (state-Right-keys_top-z __self_state)
            (store (state-Right-keys_top-aflag __self_state) h (mk-some true))
            (state-Right-keys_top-bflag __self_state))))
      (ite
        (or
          (= (select (state-Right-keys_top-aflag __self_state) h) (mk-some true))
          (= (select (state-Right-keys_top-bflag __self_state) h) (mk-some true)))
        (let
          ((unwrap-1 (maybe-get (select (state-Right-keys_top-T __self_state) h))))
          (let
            ((Z unwrap-1))
            (let
              ((unwrap-2 (maybe-get (select (state-Right-keys_top-z __self_state) h))))
              (let
                ((zz unwrap-2))
                (let
                  ((unwrap-3 (maybe-get (select Z zz))))
                  (let
                    ((k unwrap-3))
                    (let
                      (
                        (__global_state
                          (mk-composition-state-Right
                            __self_state
                            (composition-pkgstate-Right-keys_bottom __global_state)
                            (composition-pkgstate-Right-simgate __global_state)
                            (composition-pkgstate-Right-ev __global_state)
                            (composition-param-Right-zeron __global_state)
                            (composition-param-Right-zerom __global_state)
                            (composition-param-Right-n __global_state)
                            (composition-param-Right-p __global_state)
                            (composition-param-Right-m __global_state)
                            (composition-rand-Right-0 __global_state)
                            (composition-rand-Right-1 __global_state)
                            (composition-rand-Right-2 __global_state)
                            (composition-rand-Right-3 __global_state)
                            (composition-rand-Right-4 __global_state)
                            (composition-rand-Right-5 __global_state)
                            (composition-rand-Right-6 __global_state)
                            (composition-rand-Right-7 __global_state)
                            (composition-rand-Right-8 __global_state)
                            (composition-rand-Right-9 __global_state)
                            (composition-rand-Right-10 __global_state)
                            (composition-rand-Right-11 __global_state)
                            (composition-rand-Right-12 __global_state))))
                      (mk-return-Right-keys_top-GETAOUT __global_state k))))))))
        mk-abort-Right-keys_top-GETAOUT))))
(define-fun
  oracle-Right-keys_top-GETINAOUT
  ((__global_state CompositionState-Right) (h Int))
  Return_Right_keys_top_GETINAOUT
  (let
    ((__self_state (composition-pkgstate-Right-keys_top __global_state)))
    (let
      (
        (__self_state
          (mk-state-Right-keys_top
            (state-Right-keys_top-T __self_state)
            (state-Right-keys_top-z __self_state)
            (store (state-Right-keys_top-aflag __self_state) h (mk-some true))
            (state-Right-keys_top-bflag __self_state))))
      (ite
        (or
          (= (select (state-Right-keys_top-aflag __self_state) h) (mk-some true))
          (= (select (state-Right-keys_top-bflag __self_state) h) (mk-some true)))
        (let
          ((unwrap-1 (maybe-get (select (state-Right-keys_top-T __self_state) h))))
          (let
            ((Z unwrap-1))
            (let
              ((unwrap-2 (maybe-get (select (state-Right-keys_top-z __self_state) h))))
              (let
                ((zz unwrap-2))
                (let
                  ((unwrap-3 (maybe-get (select Z (not zz)))))
                  (let
                    ((k unwrap-3))
                    (let
                      (
                        (__global_state
                          (mk-composition-state-Right
                            __self_state
                            (composition-pkgstate-Right-keys_bottom __global_state)
                            (composition-pkgstate-Right-simgate __global_state)
                            (composition-pkgstate-Right-ev __global_state)
                            (composition-param-Right-zeron __global_state)
                            (composition-param-Right-zerom __global_state)
                            (composition-param-Right-n __global_state)
                            (composition-param-Right-p __global_state)
                            (composition-param-Right-m __global_state)
                            (composition-rand-Right-0 __global_state)
                            (composition-rand-Right-1 __global_state)
                            (composition-rand-Right-2 __global_state)
                            (composition-rand-Right-3 __global_state)
                            (composition-rand-Right-4 __global_state)
                            (composition-rand-Right-5 __global_state)
                            (composition-rand-Right-6 __global_state)
                            (composition-rand-Right-7 __global_state)
                            (composition-rand-Right-8 __global_state)
                            (composition-rand-Right-9 __global_state)
                            (composition-rand-Right-10 __global_state)
                            (composition-rand-Right-11 __global_state)
                            (composition-rand-Right-12 __global_state))))
                      (mk-return-Right-keys_top-GETINAOUT __global_state k))))))))
        mk-abort-Right-keys_top-GETINAOUT))))
(define-fun
  oracle-Right-keys_top-GETAIN
  ((__global_state CompositionState-Right) (h Int))
  Return_Right_keys_top_GETAIN
  (let
    ((__self_state (composition-pkgstate-Right-keys_top __global_state)))
    (ite
      (= (select (state-Right-keys_top-aflag __self_state) h) (mk-some true))
      (ite
        (or
          (= (select (state-Right-keys_top-aflag __self_state) h) (mk-some true))
          (= (select (state-Right-keys_top-bflag __self_state) h) (mk-some true)))
        (let
          ((unwrap-1 (maybe-get (select (state-Right-keys_top-T __self_state) h))))
          (let
            ((Z unwrap-1))
            (let
              ((unwrap-2 (maybe-get (select (state-Right-keys_top-z __self_state) h))))
              (let
                ((zz unwrap-2))
                (let
                  ((unwrap-3 (maybe-get (select Z zz))))
                  (let
                    ((k unwrap-3))
                    (let
                      (
                        (__global_state
                          (mk-composition-state-Right
                            __self_state
                            (composition-pkgstate-Right-keys_bottom __global_state)
                            (composition-pkgstate-Right-simgate __global_state)
                            (composition-pkgstate-Right-ev __global_state)
                            (composition-param-Right-zeron __global_state)
                            (composition-param-Right-zerom __global_state)
                            (composition-param-Right-n __global_state)
                            (composition-param-Right-p __global_state)
                            (composition-param-Right-m __global_state)
                            (composition-rand-Right-0 __global_state)
                            (composition-rand-Right-1 __global_state)
                            (composition-rand-Right-2 __global_state)
                            (composition-rand-Right-3 __global_state)
                            (composition-rand-Right-4 __global_state)
                            (composition-rand-Right-5 __global_state)
                            (composition-rand-Right-6 __global_state)
                            (composition-rand-Right-7 __global_state)
                            (composition-rand-Right-8 __global_state)
                            (composition-rand-Right-9 __global_state)
                            (composition-rand-Right-10 __global_state)
                            (composition-rand-Right-11 __global_state)
                            (composition-rand-Right-12 __global_state))))
                      (mk-return-Right-keys_top-GETAIN __global_state k))))))))
        mk-abort-Right-keys_top-GETAIN)
      mk-abort-Right-keys_top-GETAIN)))
(define-fun
  oracle-Right-keys_top-GETINAIN
  ((__global_state CompositionState-Right) (h Int))
  Return_Right_keys_top_GETINAIN
  (let
    ((__self_state (composition-pkgstate-Right-keys_top __global_state)))
    (ite
      (= (select (state-Right-keys_top-aflag __self_state) h) (mk-some true))
      (ite
        (or
          (= (select (state-Right-keys_top-aflag __self_state) h) (mk-some true))
          (= (select (state-Right-keys_top-bflag __self_state) h) (mk-some true)))
        (let
          ((unwrap-1 (maybe-get (select (state-Right-keys_top-T __self_state) h))))
          (let
            ((Z unwrap-1))
            (let
              ((unwrap-2 (maybe-get (select (state-Right-keys_top-z __self_state) h))))
              (let
                ((zz unwrap-2))
                (let
                  ((unwrap-3 (maybe-get (select Z (not zz)))))
                  (let
                    ((k unwrap-3))
                    (let
                      (
                        (__global_state
                          (mk-composition-state-Right
                            __self_state
                            (composition-pkgstate-Right-keys_bottom __global_state)
                            (composition-pkgstate-Right-simgate __global_state)
                            (composition-pkgstate-Right-ev __global_state)
                            (composition-param-Right-zeron __global_state)
                            (composition-param-Right-zerom __global_state)
                            (composition-param-Right-n __global_state)
                            (composition-param-Right-p __global_state)
                            (composition-param-Right-m __global_state)
                            (composition-rand-Right-0 __global_state)
                            (composition-rand-Right-1 __global_state)
                            (composition-rand-Right-2 __global_state)
                            (composition-rand-Right-3 __global_state)
                            (composition-rand-Right-4 __global_state)
                            (composition-rand-Right-5 __global_state)
                            (composition-rand-Right-6 __global_state)
                            (composition-rand-Right-7 __global_state)
                            (composition-rand-Right-8 __global_state)
                            (composition-rand-Right-9 __global_state)
                            (composition-rand-Right-10 __global_state)
                            (composition-rand-Right-11 __global_state)
                            (composition-rand-Right-12 __global_state))))
                      (mk-return-Right-keys_top-GETINAIN __global_state k))))))))
        mk-abort-Right-keys_top-GETINAIN)
      mk-abort-Right-keys_top-GETINAIN)))
(define-fun
  oracle-Right-keys_top-GETBIT
  ((__global_state CompositionState-Right) (h Int))
  Return_Right_keys_top_GETBIT
  (let
    ((__self_state (composition-pkgstate-Right-keys_top __global_state)))
    (ite
      (not
        (= (select (state-Right-keys_top-z __self_state) h) (as mk-none (Maybe Bool))))
      (let
        ((unwrap-1 (maybe-get (select (state-Right-keys_top-z __self_state) h))))
        (let
          ((zz unwrap-1))
          (let
            (
              (__global_state
                (mk-composition-state-Right
                  __self_state
                  (composition-pkgstate-Right-keys_bottom __global_state)
                  (composition-pkgstate-Right-simgate __global_state)
                  (composition-pkgstate-Right-ev __global_state)
                  (composition-param-Right-zeron __global_state)
                  (composition-param-Right-zerom __global_state)
                  (composition-param-Right-n __global_state)
                  (composition-param-Right-p __global_state)
                  (composition-param-Right-m __global_state)
                  (composition-rand-Right-0 __global_state)
                  (composition-rand-Right-1 __global_state)
                  (composition-rand-Right-2 __global_state)
                  (composition-rand-Right-3 __global_state)
                  (composition-rand-Right-4 __global_state)
                  (composition-rand-Right-5 __global_state)
                  (composition-rand-Right-6 __global_state)
                  (composition-rand-Right-7 __global_state)
                  (composition-rand-Right-8 __global_state)
                  (composition-rand-Right-9 __global_state)
                  (composition-rand-Right-10 __global_state)
                  (composition-rand-Right-11 __global_state)
                  (composition-rand-Right-12 __global_state))))
            (mk-return-Right-keys_top-GETBIT __global_state zz))))
      mk-abort-Right-keys_top-GETBIT)))
(define-fun
  oracle-Right-keys_top-SETBIT
  ((__global_state CompositionState-Right) (h Int) (zz Bool))
  Return_Right_keys_top_SETBIT
  (let
    ((__self_state (composition-pkgstate-Right-keys_top __global_state)))
    (ite
      (= (select (state-Right-keys_top-z __self_state) h) (as mk-none (Maybe Bool)))
      (let
        (
          (__self_state
            (mk-state-Right-keys_top
              (state-Right-keys_top-T __self_state)
              (store (state-Right-keys_top-z __self_state) h (mk-some zz))
              (state-Right-keys_top-aflag __self_state)
              (state-Right-keys_top-bflag __self_state))))
        (mk-return-Right-keys_top-SETBIT __global_state))
      mk-abort-Right-keys_top-SETBIT)))
(define-fun
  oracle-Right-keys_bottom-GETKEYSIN
  ((__global_state CompositionState-Right) (h Int))
  Return_Right_keys_bottom_GETKEYSIN
  (let
    ((__self_state (composition-pkgstate-Right-keys_bottom __global_state)))
    (ite
      (not
        (=
          (select (state-Right-keys_bottom-z __self_state) h)
          (as mk-none (Maybe Bool))))
      (ite
        (or
          (= (select (state-Right-keys_bottom-aflag __self_state) h) (mk-some true))
          (= (select (state-Right-keys_bottom-bflag __self_state) h) (mk-some true)))
        (let
          ((unwrap-1 (maybe-get (select (state-Right-keys_bottom-T __self_state) h))))
          (let
            ((Z unwrap-1))
            (let
              (
                (__global_state
                  (mk-composition-state-Right
                    (composition-pkgstate-Right-keys_top __global_state)
                    __self_state
                    (composition-pkgstate-Right-simgate __global_state)
                    (composition-pkgstate-Right-ev __global_state)
                    (composition-param-Right-zeron __global_state)
                    (composition-param-Right-zerom __global_state)
                    (composition-param-Right-n __global_state)
                    (composition-param-Right-p __global_state)
                    (composition-param-Right-m __global_state)
                    (composition-rand-Right-0 __global_state)
                    (composition-rand-Right-1 __global_state)
                    (composition-rand-Right-2 __global_state)
                    (composition-rand-Right-3 __global_state)
                    (composition-rand-Right-4 __global_state)
                    (composition-rand-Right-5 __global_state)
                    (composition-rand-Right-6 __global_state)
                    (composition-rand-Right-7 __global_state)
                    (composition-rand-Right-8 __global_state)
                    (composition-rand-Right-9 __global_state)
                    (composition-rand-Right-10 __global_state)
                    (composition-rand-Right-11 __global_state)
                    (composition-rand-Right-12 __global_state))))
              (mk-return-Right-keys_bottom-GETKEYSIN __global_state Z))))
        mk-abort-Right-keys_bottom-GETKEYSIN)
      mk-abort-Right-keys_bottom-GETKEYSIN)))
(define-fun
  oracle-Right-keys_bottom-GETKEYSOUT
  ((__global_state CompositionState-Right) (h Int))
  Return_Right_keys_bottom_GETKEYSOUT
  (let
    ((__self_state (composition-pkgstate-Right-keys_bottom __global_state)))
    (let
      (
        (__self_state
          (mk-state-Right-keys_bottom
            (state-Right-keys_bottom-T __self_state)
            (state-Right-keys_bottom-z __self_state)
            (store (state-Right-keys_bottom-aflag __self_state) h (mk-some true))
            (state-Right-keys_bottom-bflag __self_state))))
      (let
        ((Z ((as const (Array Bool (Maybe Bits_n))) (as mk-none (Maybe Bits_n)))))
        (ite
          (=
            (select (state-Right-keys_bottom-T __self_state) h)
            (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
          (let
            ((r (__sample-rand-Right-Bits_n 3 (composition-rand-Right-3 __global_state))))
            (let
              (
                (__global_state
                  (mk-composition-state-Right
                    (composition-pkgstate-Right-keys_top __global_state)
                    (composition-pkgstate-Right-keys_bottom __global_state)
                    (composition-pkgstate-Right-simgate __global_state)
                    (composition-pkgstate-Right-ev __global_state)
                    (composition-param-Right-zeron __global_state)
                    (composition-param-Right-zerom __global_state)
                    (composition-param-Right-n __global_state)
                    (composition-param-Right-p __global_state)
                    (composition-param-Right-m __global_state)
                    (composition-rand-Right-0 __global_state)
                    (composition-rand-Right-1 __global_state)
                    (composition-rand-Right-2 __global_state)
                    (+ 1 (composition-rand-Right-3 __global_state))
                    (composition-rand-Right-4 __global_state)
                    (composition-rand-Right-5 __global_state)
                    (composition-rand-Right-6 __global_state)
                    (composition-rand-Right-7 __global_state)
                    (composition-rand-Right-8 __global_state)
                    (composition-rand-Right-9 __global_state)
                    (composition-rand-Right-10 __global_state)
                    (composition-rand-Right-11 __global_state)
                    (composition-rand-Right-12 __global_state))))
              (let
                ((Z ((as const (Array Bool (Maybe Bits_n))) (as mk-none (Maybe Bits_n)))))
                (let
                  ((Z (store Z true (mk-some r))))
                  (let
                    ((rr (__sample-rand-Right-Bits_n 4 (composition-rand-Right-4 __global_state))))
                    (let
                      (
                        (__global_state
                          (mk-composition-state-Right
                            (composition-pkgstate-Right-keys_top __global_state)
                            (composition-pkgstate-Right-keys_bottom __global_state)
                            (composition-pkgstate-Right-simgate __global_state)
                            (composition-pkgstate-Right-ev __global_state)
                            (composition-param-Right-zeron __global_state)
                            (composition-param-Right-zerom __global_state)
                            (composition-param-Right-n __global_state)
                            (composition-param-Right-p __global_state)
                            (composition-param-Right-m __global_state)
                            (composition-rand-Right-0 __global_state)
                            (composition-rand-Right-1 __global_state)
                            (composition-rand-Right-2 __global_state)
                            (composition-rand-Right-3 __global_state)
                            (+ 1 (composition-rand-Right-4 __global_state))
                            (composition-rand-Right-5 __global_state)
                            (composition-rand-Right-6 __global_state)
                            (composition-rand-Right-7 __global_state)
                            (composition-rand-Right-8 __global_state)
                            (composition-rand-Right-9 __global_state)
                            (composition-rand-Right-10 __global_state)
                            (composition-rand-Right-11 __global_state)
                            (composition-rand-Right-12 __global_state))))
                      (let
                        ((Z ((as const (Array Bool (Maybe Bits_n))) (as mk-none (Maybe Bits_n)))))
                        (let
                          ((Z (store Z false (mk-some rr))))
                          (let
                            (
                              (__self_state
                                (mk-state-Right-keys_bottom
                                  (store (state-Right-keys_bottom-T __self_state) h (mk-some Z))
                                  (state-Right-keys_bottom-z __self_state)
                                  (state-Right-keys_bottom-aflag __self_state)
                                  (state-Right-keys_bottom-bflag __self_state))))
                            (let
                              ((unwrap-1 (maybe-get (select (state-Right-keys_bottom-T __self_state) h))))
                              (let
                                ((Z unwrap-1))
                                (let
                                  (
                                    (__global_state
                                      (mk-composition-state-Right
                                        (composition-pkgstate-Right-keys_top __global_state)
                                        __self_state
                                        (composition-pkgstate-Right-simgate __global_state)
                                        (composition-pkgstate-Right-ev __global_state)
                                        (composition-param-Right-zeron __global_state)
                                        (composition-param-Right-zerom __global_state)
                                        (composition-param-Right-n __global_state)
                                        (composition-param-Right-p __global_state)
                                        (composition-param-Right-m __global_state)
                                        (composition-rand-Right-0 __global_state)
                                        (composition-rand-Right-1 __global_state)
                                        (composition-rand-Right-2 __global_state)
                                        (composition-rand-Right-3 __global_state)
                                        (composition-rand-Right-4 __global_state)
                                        (composition-rand-Right-5 __global_state)
                                        (composition-rand-Right-6 __global_state)
                                        (composition-rand-Right-7 __global_state)
                                        (composition-rand-Right-8 __global_state)
                                        (composition-rand-Right-9 __global_state)
                                        (composition-rand-Right-10 __global_state)
                                        (composition-rand-Right-11 __global_state)
                                        (composition-rand-Right-12 __global_state))))
                                  (mk-return-Right-keys_bottom-GETKEYSOUT __global_state Z)))))))))))))
          (let
            ((unwrap-1 (maybe-get (select (state-Right-keys_bottom-T __self_state) h))))
            (let
              ((Z unwrap-1))
              (let
                (
                  (__global_state
                    (mk-composition-state-Right
                      (composition-pkgstate-Right-keys_top __global_state)
                      __self_state
                      (composition-pkgstate-Right-simgate __global_state)
                      (composition-pkgstate-Right-ev __global_state)
                      (composition-param-Right-zeron __global_state)
                      (composition-param-Right-zerom __global_state)
                      (composition-param-Right-n __global_state)
                      (composition-param-Right-p __global_state)
                      (composition-param-Right-m __global_state)
                      (composition-rand-Right-0 __global_state)
                      (composition-rand-Right-1 __global_state)
                      (composition-rand-Right-2 __global_state)
                      (composition-rand-Right-3 __global_state)
                      (composition-rand-Right-4 __global_state)
                      (composition-rand-Right-5 __global_state)
                      (composition-rand-Right-6 __global_state)
                      (composition-rand-Right-7 __global_state)
                      (composition-rand-Right-8 __global_state)
                      (composition-rand-Right-9 __global_state)
                      (composition-rand-Right-10 __global_state)
                      (composition-rand-Right-11 __global_state)
                      (composition-rand-Right-12 __global_state))))
                (mk-return-Right-keys_bottom-GETKEYSOUT __global_state Z)))))))))
(define-fun
  oracle-Right-keys_bottom-GETAOUT
  ((__global_state CompositionState-Right) (h Int))
  Return_Right_keys_bottom_GETAOUT
  (let
    ((__self_state (composition-pkgstate-Right-keys_bottom __global_state)))
    (let
      (
        (__self_state
          (mk-state-Right-keys_bottom
            (state-Right-keys_bottom-T __self_state)
            (state-Right-keys_bottom-z __self_state)
            (store (state-Right-keys_bottom-aflag __self_state) h (mk-some true))
            (state-Right-keys_bottom-bflag __self_state))))
      (ite
        (or
          (= (select (state-Right-keys_bottom-aflag __self_state) h) (mk-some true))
          (= (select (state-Right-keys_bottom-bflag __self_state) h) (mk-some true)))
        (let
          ((unwrap-1 (maybe-get (select (state-Right-keys_bottom-T __self_state) h))))
          (let
            ((Z unwrap-1))
            (let
              ((unwrap-2 (maybe-get (select (state-Right-keys_bottom-z __self_state) h))))
              (let
                ((zz unwrap-2))
                (let
                  ((unwrap-3 (maybe-get (select Z zz))))
                  (let
                    ((k unwrap-3))
                    (let
                      (
                        (__global_state
                          (mk-composition-state-Right
                            (composition-pkgstate-Right-keys_top __global_state)
                            __self_state
                            (composition-pkgstate-Right-simgate __global_state)
                            (composition-pkgstate-Right-ev __global_state)
                            (composition-param-Right-zeron __global_state)
                            (composition-param-Right-zerom __global_state)
                            (composition-param-Right-n __global_state)
                            (composition-param-Right-p __global_state)
                            (composition-param-Right-m __global_state)
                            (composition-rand-Right-0 __global_state)
                            (composition-rand-Right-1 __global_state)
                            (composition-rand-Right-2 __global_state)
                            (composition-rand-Right-3 __global_state)
                            (composition-rand-Right-4 __global_state)
                            (composition-rand-Right-5 __global_state)
                            (composition-rand-Right-6 __global_state)
                            (composition-rand-Right-7 __global_state)
                            (composition-rand-Right-8 __global_state)
                            (composition-rand-Right-9 __global_state)
                            (composition-rand-Right-10 __global_state)
                            (composition-rand-Right-11 __global_state)
                            (composition-rand-Right-12 __global_state))))
                      (mk-return-Right-keys_bottom-GETAOUT __global_state k))))))))
        mk-abort-Right-keys_bottom-GETAOUT))))
(define-fun
  oracle-Right-keys_bottom-GETINAOUT
  ((__global_state CompositionState-Right) (h Int))
  Return_Right_keys_bottom_GETINAOUT
  (let
    ((__self_state (composition-pkgstate-Right-keys_bottom __global_state)))
    (let
      (
        (__self_state
          (mk-state-Right-keys_bottom
            (state-Right-keys_bottom-T __self_state)
            (state-Right-keys_bottom-z __self_state)
            (store (state-Right-keys_bottom-aflag __self_state) h (mk-some true))
            (state-Right-keys_bottom-bflag __self_state))))
      (ite
        (or
          (= (select (state-Right-keys_bottom-aflag __self_state) h) (mk-some true))
          (= (select (state-Right-keys_bottom-bflag __self_state) h) (mk-some true)))
        (let
          ((unwrap-1 (maybe-get (select (state-Right-keys_bottom-T __self_state) h))))
          (let
            ((Z unwrap-1))
            (let
              ((unwrap-2 (maybe-get (select (state-Right-keys_bottom-z __self_state) h))))
              (let
                ((zz unwrap-2))
                (let
                  ((unwrap-3 (maybe-get (select Z (not zz)))))
                  (let
                    ((k unwrap-3))
                    (let
                      (
                        (__global_state
                          (mk-composition-state-Right
                            (composition-pkgstate-Right-keys_top __global_state)
                            __self_state
                            (composition-pkgstate-Right-simgate __global_state)
                            (composition-pkgstate-Right-ev __global_state)
                            (composition-param-Right-zeron __global_state)
                            (composition-param-Right-zerom __global_state)
                            (composition-param-Right-n __global_state)
                            (composition-param-Right-p __global_state)
                            (composition-param-Right-m __global_state)
                            (composition-rand-Right-0 __global_state)
                            (composition-rand-Right-1 __global_state)
                            (composition-rand-Right-2 __global_state)
                            (composition-rand-Right-3 __global_state)
                            (composition-rand-Right-4 __global_state)
                            (composition-rand-Right-5 __global_state)
                            (composition-rand-Right-6 __global_state)
                            (composition-rand-Right-7 __global_state)
                            (composition-rand-Right-8 __global_state)
                            (composition-rand-Right-9 __global_state)
                            (composition-rand-Right-10 __global_state)
                            (composition-rand-Right-11 __global_state)
                            (composition-rand-Right-12 __global_state))))
                      (mk-return-Right-keys_bottom-GETINAOUT __global_state k))))))))
        mk-abort-Right-keys_bottom-GETINAOUT))))
(define-fun
  oracle-Right-keys_bottom-GETAIN
  ((__global_state CompositionState-Right) (h Int))
  Return_Right_keys_bottom_GETAIN
  (let
    ((__self_state (composition-pkgstate-Right-keys_bottom __global_state)))
    (ite
      (= (select (state-Right-keys_bottom-aflag __self_state) h) (mk-some true))
      (ite
        (or
          (= (select (state-Right-keys_bottom-aflag __self_state) h) (mk-some true))
          (= (select (state-Right-keys_bottom-bflag __self_state) h) (mk-some true)))
        (let
          ((unwrap-1 (maybe-get (select (state-Right-keys_bottom-T __self_state) h))))
          (let
            ((Z unwrap-1))
            (let
              ((unwrap-2 (maybe-get (select (state-Right-keys_bottom-z __self_state) h))))
              (let
                ((zz unwrap-2))
                (let
                  ((unwrap-3 (maybe-get (select Z zz))))
                  (let
                    ((k unwrap-3))
                    (let
                      (
                        (__global_state
                          (mk-composition-state-Right
                            (composition-pkgstate-Right-keys_top __global_state)
                            __self_state
                            (composition-pkgstate-Right-simgate __global_state)
                            (composition-pkgstate-Right-ev __global_state)
                            (composition-param-Right-zeron __global_state)
                            (composition-param-Right-zerom __global_state)
                            (composition-param-Right-n __global_state)
                            (composition-param-Right-p __global_state)
                            (composition-param-Right-m __global_state)
                            (composition-rand-Right-0 __global_state)
                            (composition-rand-Right-1 __global_state)
                            (composition-rand-Right-2 __global_state)
                            (composition-rand-Right-3 __global_state)
                            (composition-rand-Right-4 __global_state)
                            (composition-rand-Right-5 __global_state)
                            (composition-rand-Right-6 __global_state)
                            (composition-rand-Right-7 __global_state)
                            (composition-rand-Right-8 __global_state)
                            (composition-rand-Right-9 __global_state)
                            (composition-rand-Right-10 __global_state)
                            (composition-rand-Right-11 __global_state)
                            (composition-rand-Right-12 __global_state))))
                      (mk-return-Right-keys_bottom-GETAIN __global_state k))))))))
        mk-abort-Right-keys_bottom-GETAIN)
      mk-abort-Right-keys_bottom-GETAIN)))
(define-fun
  oracle-Right-keys_bottom-GETINAIN
  ((__global_state CompositionState-Right) (h Int))
  Return_Right_keys_bottom_GETINAIN
  (let
    ((__self_state (composition-pkgstate-Right-keys_bottom __global_state)))
    (ite
      (= (select (state-Right-keys_bottom-aflag __self_state) h) (mk-some true))
      (ite
        (or
          (= (select (state-Right-keys_bottom-aflag __self_state) h) (mk-some true))
          (= (select (state-Right-keys_bottom-bflag __self_state) h) (mk-some true)))
        (let
          ((unwrap-1 (maybe-get (select (state-Right-keys_bottom-T __self_state) h))))
          (let
            ((Z unwrap-1))
            (let
              ((unwrap-2 (maybe-get (select (state-Right-keys_bottom-z __self_state) h))))
              (let
                ((zz unwrap-2))
                (let
                  ((unwrap-3 (maybe-get (select Z (not zz)))))
                  (let
                    ((k unwrap-3))
                    (let
                      (
                        (__global_state
                          (mk-composition-state-Right
                            (composition-pkgstate-Right-keys_top __global_state)
                            __self_state
                            (composition-pkgstate-Right-simgate __global_state)
                            (composition-pkgstate-Right-ev __global_state)
                            (composition-param-Right-zeron __global_state)
                            (composition-param-Right-zerom __global_state)
                            (composition-param-Right-n __global_state)
                            (composition-param-Right-p __global_state)
                            (composition-param-Right-m __global_state)
                            (composition-rand-Right-0 __global_state)
                            (composition-rand-Right-1 __global_state)
                            (composition-rand-Right-2 __global_state)
                            (composition-rand-Right-3 __global_state)
                            (composition-rand-Right-4 __global_state)
                            (composition-rand-Right-5 __global_state)
                            (composition-rand-Right-6 __global_state)
                            (composition-rand-Right-7 __global_state)
                            (composition-rand-Right-8 __global_state)
                            (composition-rand-Right-9 __global_state)
                            (composition-rand-Right-10 __global_state)
                            (composition-rand-Right-11 __global_state)
                            (composition-rand-Right-12 __global_state))))
                      (mk-return-Right-keys_bottom-GETINAIN __global_state k))))))))
        mk-abort-Right-keys_bottom-GETINAIN)
      mk-abort-Right-keys_bottom-GETINAIN)))
(define-fun
  oracle-Right-keys_bottom-GETBIT
  ((__global_state CompositionState-Right) (h Int))
  Return_Right_keys_bottom_GETBIT
  (let
    ((__self_state (composition-pkgstate-Right-keys_bottom __global_state)))
    (ite
      (not
        (=
          (select (state-Right-keys_bottom-z __self_state) h)
          (as mk-none (Maybe Bool))))
      (let
        ((unwrap-1 (maybe-get (select (state-Right-keys_bottom-z __self_state) h))))
        (let
          ((zz unwrap-1))
          (let
            (
              (__global_state
                (mk-composition-state-Right
                  (composition-pkgstate-Right-keys_top __global_state)
                  __self_state
                  (composition-pkgstate-Right-simgate __global_state)
                  (composition-pkgstate-Right-ev __global_state)
                  (composition-param-Right-zeron __global_state)
                  (composition-param-Right-zerom __global_state)
                  (composition-param-Right-n __global_state)
                  (composition-param-Right-p __global_state)
                  (composition-param-Right-m __global_state)
                  (composition-rand-Right-0 __global_state)
                  (composition-rand-Right-1 __global_state)
                  (composition-rand-Right-2 __global_state)
                  (composition-rand-Right-3 __global_state)
                  (composition-rand-Right-4 __global_state)
                  (composition-rand-Right-5 __global_state)
                  (composition-rand-Right-6 __global_state)
                  (composition-rand-Right-7 __global_state)
                  (composition-rand-Right-8 __global_state)
                  (composition-rand-Right-9 __global_state)
                  (composition-rand-Right-10 __global_state)
                  (composition-rand-Right-11 __global_state)
                  (composition-rand-Right-12 __global_state))))
            (mk-return-Right-keys_bottom-GETBIT __global_state zz))))
      mk-abort-Right-keys_bottom-GETBIT)))
(define-fun
  oracle-Right-keys_bottom-SETBIT
  ((__global_state CompositionState-Right) (h Int) (zz Bool))
  Return_Right_keys_bottom_SETBIT
  (let
    ((__self_state (composition-pkgstate-Right-keys_bottom __global_state)))
    (ite
      (=
        (select (state-Right-keys_bottom-z __self_state) h)
        (as mk-none (Maybe Bool)))
      (let
        (
          (__self_state
            (mk-state-Right-keys_bottom
              (state-Right-keys_bottom-T __self_state)
              (store (state-Right-keys_bottom-z __self_state) h (mk-some zz))
              (state-Right-keys_bottom-aflag __self_state)
              (state-Right-keys_bottom-bflag __self_state))))
        (mk-return-Right-keys_bottom-SETBIT __global_state))
      mk-abort-Right-keys_bottom-SETBIT)))
(define-fun
  oracle-Right-ev-EVAL
  (
    (__global_state CompositionState-Right)
    (j Int)
    (l Int)
    (r Int)
    (op (Array (Tuple2 Bool Bool) (Maybe Bool))))
  Return_Right_ev_EVAL
  (let
    ((__self_state (composition-pkgstate-Right-ev __global_state)))
    (let
      ((__ret (oracle-Right-keys_top-GETBIT __global_state l)))
      (ite
        (= __ret mk-abort-Right-keys_top-GETBIT)
        mk-abort-Right-ev-EVAL
        (let
          (
            (__global_state (return-Right-keys_top-GETBIT-state __ret))
            (zl (return-Right-keys_top-GETBIT-value __ret)))
          (let
            ((__ret (oracle-Right-keys_top-GETBIT __global_state r)))
            (ite
              (= __ret mk-abort-Right-keys_top-GETBIT)
              mk-abort-Right-ev-EVAL
              (let
                (
                  (__global_state (return-Right-keys_top-GETBIT-state __ret))
                  (zr (return-Right-keys_top-GETBIT-value __ret)))
                (let
                  ((unwrap-1 (maybe-get (select op (mk-tuple2 zl zr)))))
                  (let
                    ((z unwrap-1))
                    (let
                      ((__ret (oracle-Right-keys_bottom-SETBIT __global_state j z)))
                      (ite
                        (= __ret mk-abort-Right-keys_bottom-SETBIT)
                        mk-abort-Right-ev-EVAL
                        (let
                          ((__global_state (return-Right-keys_bottom-SETBIT-state __ret)))
                          (mk-return-Right-ev-EVAL __global_state))))))))))))))
(define-fun
  oracle-Right-simgate-GBLG
  (
    (__global_state CompositionState-Right)
    (h Int)
    (l Int)
    (r Int)
    (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
    (j Int))
  Return_Right_simgate_GBLG
  (let
    ((__self_state (composition-pkgstate-Right-simgate __global_state)))
    (let
      ((C ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))))
      (let
        ((Sl ((as const (Array Bool (Maybe Bits_n))) (as mk-none (Maybe Bits_n)))))
        (let
          ((Sr ((as const (Array Bool (Maybe Bits_n))) (as mk-none (Maybe Bits_n)))))
          (let
            ((Sj ((as const (Array Bool (Maybe Bits_n))) (as mk-none (Maybe Bits_n)))))
            (let
              ((__ret (oracle-Right-ev-EVAL __global_state j l r op)))
              (ite
                (= __ret mk-abort-Right-ev-EVAL)
                mk-abort-Right-simgate-GBLG
                (let
                  ((__global_state (return-Right-ev-EVAL-state __ret)))
                  (let
                    ((__ret (oracle-Right-keys_top-GETAIN __global_state l)))
                    (ite
                      (= __ret mk-abort-Right-keys_top-GETAIN)
                      mk-abort-Right-simgate-GBLG
                      (let
                        (
                          (__global_state (return-Right-keys_top-GETAIN-state __ret))
                          (temp (return-Right-keys_top-GETAIN-value __ret)))
                        (let
                          ((Sl ((as const (Array Bool (Maybe Bits_n))) (as mk-none (Maybe Bits_n)))))
                          (let
                            ((Sl (store Sl true (mk-some temp))))
                            (let
                              ((__ret (oracle-Right-keys_top-GETINAIN __global_state l)))
                              (ite
                                (= __ret mk-abort-Right-keys_top-GETINAIN)
                                mk-abort-Right-simgate-GBLG
                                (let
                                  (
                                    (__global_state (return-Right-keys_top-GETINAIN-state __ret))
                                    (temp (return-Right-keys_top-GETINAIN-value __ret)))
                                  (let
                                    ((Sl ((as const (Array Bool (Maybe Bits_n))) (as mk-none (Maybe Bits_n)))))
                                    (let
                                      ((Sl (store Sl false (mk-some temp))))
                                      (let
                                        ((__ret (oracle-Right-keys_top-GETAIN __global_state r)))
                                        (ite
                                          (= __ret mk-abort-Right-keys_top-GETAIN)
                                          mk-abort-Right-simgate-GBLG
                                          (let
                                            (
                                              (__global_state (return-Right-keys_top-GETAIN-state __ret))
                                              (temp (return-Right-keys_top-GETAIN-value __ret)))
                                            (let
                                              ((Sr ((as const (Array Bool (Maybe Bits_n))) (as mk-none (Maybe Bits_n)))))
                                              (let
                                                ((Sr (store Sr true (mk-some temp))))
                                                (let
                                                  ((__ret (oracle-Right-keys_top-GETINAIN __global_state r)))
                                                  (ite
                                                    (= __ret mk-abort-Right-keys_top-GETINAIN)
                                                    mk-abort-Right-simgate-GBLG
                                                    (let
                                                      (
                                                        (__global_state (return-Right-keys_top-GETINAIN-state __ret))
                                                        (temp (return-Right-keys_top-GETINAIN-value __ret)))
                                                      (let
                                                        ((Sr ((as const (Array Bool (Maybe Bits_n))) (as mk-none (Maybe Bits_n)))))
                                                        (let
                                                          ((Sr (store Sr true (mk-some temp))))
                                                          (let
                                                            ((__ret (oracle-Right-keys_bottom-GETAOUT __global_state j)))
                                                            (ite
                                                              (= __ret mk-abort-Right-keys_bottom-GETAOUT)
                                                              mk-abort-Right-simgate-GBLG
                                                              (let
                                                                (
                                                                  (__global_state (return-Right-keys_bottom-GETAOUT-state __ret))
                                                                  (temp (return-Right-keys_bottom-GETAOUT-value __ret)))
                                                                (let
                                                                  ((Sj ((as const (Array Bool (Maybe Bits_n))) (as mk-none (Maybe Bits_n)))))
                                                                  (let
                                                                    ((Sj (store Sj false (mk-some temp))))
                                                                    (let
                                                                      ((dl false))
                                                                      (let
                                                                        ((dr false))
                                                                        (let
                                                                          ((unwrap-1 (maybe-get (select Sl dl))))
                                                                          (let
                                                                            ((kl unwrap-1))
                                                                            (let
                                                                              ((unwrap-2 (maybe-get (select Sr dr))))
                                                                              (let
                                                                                ((kr unwrap-2))
                                                                                (let
                                                                                  ((kj (composition-param-Right-zeron __global_state)))
                                                                                  (ite
                                                                                    (and (or (not dl)) (or (not dr)))
                                                                                    (let
                                                                                      ((unwrap-3 (maybe-get (select Sj false))))
                                                                                      (let
                                                                                        ((kj unwrap-3))
                                                                                        (let
                                                                                          (
                                                                                            (rin (__sample-rand-Right-Bits_n 5 (composition-rand-Right-5 __global_state))))
                                                                                          (let
                                                                                            (
                                                                                              (__global_state
                                                                                                (mk-composition-state-Right
                                                                                                  (composition-pkgstate-Right-keys_top __global_state)
                                                                                                  (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                  (composition-pkgstate-Right-simgate __global_state)
                                                                                                  (composition-pkgstate-Right-ev __global_state)
                                                                                                  (composition-param-Right-zeron __global_state)
                                                                                                  (composition-param-Right-zerom __global_state)
                                                                                                  (composition-param-Right-n __global_state)
                                                                                                  (composition-param-Right-p __global_state)
                                                                                                  (composition-param-Right-m __global_state)
                                                                                                  (composition-rand-Right-0 __global_state)
                                                                                                  (composition-rand-Right-1 __global_state)
                                                                                                  (composition-rand-Right-2 __global_state)
                                                                                                  (composition-rand-Right-3 __global_state)
                                                                                                  (composition-rand-Right-4 __global_state)
                                                                                                  (+ 1 (composition-rand-Right-5 __global_state))
                                                                                                  (composition-rand-Right-6 __global_state)
                                                                                                  (composition-rand-Right-7 __global_state)
                                                                                                  (composition-rand-Right-8 __global_state)
                                                                                                  (composition-rand-Right-9 __global_state)
                                                                                                  (composition-rand-Right-10 __global_state)
                                                                                                  (composition-rand-Right-11 __global_state)
                                                                                                  (composition-rand-Right-12 __global_state))))
                                                                                            (let
                                                                                              (
                                                                                                (rout (__sample-rand-Right-Bits_n 6 (composition-rand-Right-6 __global_state))))
                                                                                              (let
                                                                                                (
                                                                                                  (__global_state
                                                                                                    (mk-composition-state-Right
                                                                                                      (composition-pkgstate-Right-keys_top __global_state)
                                                                                                      (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                      (composition-pkgstate-Right-simgate __global_state)
                                                                                                      (composition-pkgstate-Right-ev __global_state)
                                                                                                      (composition-param-Right-zeron __global_state)
                                                                                                      (composition-param-Right-zerom __global_state)
                                                                                                      (composition-param-Right-n __global_state)
                                                                                                      (composition-param-Right-p __global_state)
                                                                                                      (composition-param-Right-m __global_state)
                                                                                                      (composition-rand-Right-0 __global_state)
                                                                                                      (composition-rand-Right-1 __global_state)
                                                                                                      (composition-rand-Right-2 __global_state)
                                                                                                      (composition-rand-Right-3 __global_state)
                                                                                                      (composition-rand-Right-4 __global_state)
                                                                                                      (composition-rand-Right-5 __global_state)
                                                                                                      (+ 1 (composition-rand-Right-6 __global_state))
                                                                                                      (composition-rand-Right-7 __global_state)
                                                                                                      (composition-rand-Right-8 __global_state)
                                                                                                      (composition-rand-Right-9 __global_state)
                                                                                                      (composition-rand-Right-10 __global_state)
                                                                                                      (composition-rand-Right-11 __global_state)
                                                                                                      (composition-rand-Right-12 __global_state))))
                                                                                                (let
                                                                                                  ((cin (__func-Right-encn kr kj rin)))
                                                                                                  (let
                                                                                                    ((cout (__func-Right-encm kl cin rout)))
                                                                                                    (let
                                                                                                      ((C ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))))
                                                                                                      (let
                                                                                                        ((C (store C cout (mk-some true))))
                                                                                                        (let
                                                                                                          ((dl true))
                                                                                                          (let
                                                                                                            ((dr false))
                                                                                                            (let
                                                                                                              ((unwrap-4 (maybe-get (select Sl dl))))
                                                                                                              (let
                                                                                                                ((kl unwrap-4))
                                                                                                                (let
                                                                                                                  ((unwrap-5 (maybe-get (select Sr dr))))
                                                                                                                  (let
                                                                                                                    ((kr unwrap-5))
                                                                                                                    (let
                                                                                                                      ((kj (composition-param-Right-zeron __global_state)))
                                                                                                                      (ite
                                                                                                                        (and (or (not dl)) (or (not dr)))
                                                                                                                        (let
                                                                                                                          ((unwrap-6 (maybe-get (select Sj false))))
                                                                                                                          (let
                                                                                                                            ((kj unwrap-6))
                                                                                                                            (let
                                                                                                                              (
                                                                                                                                (rin (__sample-rand-Right-Bits_n 7 (composition-rand-Right-7 __global_state))))
                                                                                                                              (let
                                                                                                                                (
                                                                                                                                  (__global_state
                                                                                                                                    (mk-composition-state-Right
                                                                                                                                      (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                      (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                      (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                      (composition-pkgstate-Right-ev __global_state)
                                                                                                                                      (composition-param-Right-zeron __global_state)
                                                                                                                                      (composition-param-Right-zerom __global_state)
                                                                                                                                      (composition-param-Right-n __global_state)
                                                                                                                                      (composition-param-Right-p __global_state)
                                                                                                                                      (composition-param-Right-m __global_state)
                                                                                                                                      (composition-rand-Right-0 __global_state)
                                                                                                                                      (composition-rand-Right-1 __global_state)
                                                                                                                                      (composition-rand-Right-2 __global_state)
                                                                                                                                      (composition-rand-Right-3 __global_state)
                                                                                                                                      (composition-rand-Right-4 __global_state)
                                                                                                                                      (composition-rand-Right-5 __global_state)
                                                                                                                                      (composition-rand-Right-6 __global_state)
                                                                                                                                      (+ 1 (composition-rand-Right-7 __global_state))
                                                                                                                                      (composition-rand-Right-8 __global_state)
                                                                                                                                      (composition-rand-Right-9 __global_state)
                                                                                                                                      (composition-rand-Right-10 __global_state)
                                                                                                                                      (composition-rand-Right-11 __global_state)
                                                                                                                                      (composition-rand-Right-12 __global_state))))
                                                                                                                                (let
                                                                                                                                  (
                                                                                                                                    (rout (__sample-rand-Right-Bits_n 8 (composition-rand-Right-8 __global_state))))
                                                                                                                                  (let
                                                                                                                                    (
                                                                                                                                      (__global_state
                                                                                                                                        (mk-composition-state-Right
                                                                                                                                          (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                          (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                          (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                          (composition-pkgstate-Right-ev __global_state)
                                                                                                                                          (composition-param-Right-zeron __global_state)
                                                                                                                                          (composition-param-Right-zerom __global_state)
                                                                                                                                          (composition-param-Right-n __global_state)
                                                                                                                                          (composition-param-Right-p __global_state)
                                                                                                                                          (composition-param-Right-m __global_state)
                                                                                                                                          (composition-rand-Right-0 __global_state)
                                                                                                                                          (composition-rand-Right-1 __global_state)
                                                                                                                                          (composition-rand-Right-2 __global_state)
                                                                                                                                          (composition-rand-Right-3 __global_state)
                                                                                                                                          (composition-rand-Right-4 __global_state)
                                                                                                                                          (composition-rand-Right-5 __global_state)
                                                                                                                                          (composition-rand-Right-6 __global_state)
                                                                                                                                          (composition-rand-Right-7 __global_state)
                                                                                                                                          (+ 1 (composition-rand-Right-8 __global_state))
                                                                                                                                          (composition-rand-Right-9 __global_state)
                                                                                                                                          (composition-rand-Right-10 __global_state)
                                                                                                                                          (composition-rand-Right-11 __global_state)
                                                                                                                                          (composition-rand-Right-12 __global_state))))
                                                                                                                                    (let
                                                                                                                                      ((cin (__func-Right-encn kr kj rin)))
                                                                                                                                      (let
                                                                                                                                        ((cout (__func-Right-encm kl cin rout)))
                                                                                                                                        (let
                                                                                                                                          ((C ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))))
                                                                                                                                          (let
                                                                                                                                            ((C (store C cout (mk-some true))))
                                                                                                                                            (let
                                                                                                                                              ((dl false))
                                                                                                                                              (let
                                                                                                                                                ((dr true))
                                                                                                                                                (let
                                                                                                                                                  ((unwrap-7 (maybe-get (select Sl dl))))
                                                                                                                                                  (let
                                                                                                                                                    ((kl unwrap-7))
                                                                                                                                                    (let
                                                                                                                                                      ((unwrap-8 (maybe-get (select Sr dr))))
                                                                                                                                                      (let
                                                                                                                                                        ((kr unwrap-8))
                                                                                                                                                        (let
                                                                                                                                                          ((kj (composition-param-Right-zeron __global_state)))
                                                                                                                                                          (ite
                                                                                                                                                            (and (or (not dl)) (or (not dr)))
                                                                                                                                                            (let
                                                                                                                                                              ((unwrap-9 (maybe-get (select Sj false))))
                                                                                                                                                              (let
                                                                                                                                                                ((kj unwrap-9))
                                                                                                                                                                (let
                                                                                                                                                                  (
                                                                                                                                                                    (rin (__sample-rand-Right-Bits_n 9 (composition-rand-Right-9 __global_state))))
                                                                                                                                                                  (let
                                                                                                                                                                    (
                                                                                                                                                                      (__global_state
                                                                                                                                                                        (mk-composition-state-Right
                                                                                                                                                                          (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                          (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                          (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                          (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                          (composition-param-Right-zeron __global_state)
                                                                                                                                                                          (composition-param-Right-zerom __global_state)
                                                                                                                                                                          (composition-param-Right-n __global_state)
                                                                                                                                                                          (composition-param-Right-p __global_state)
                                                                                                                                                                          (composition-param-Right-m __global_state)
                                                                                                                                                                          (composition-rand-Right-0 __global_state)
                                                                                                                                                                          (composition-rand-Right-1 __global_state)
                                                                                                                                                                          (composition-rand-Right-2 __global_state)
                                                                                                                                                                          (composition-rand-Right-3 __global_state)
                                                                                                                                                                          (composition-rand-Right-4 __global_state)
                                                                                                                                                                          (composition-rand-Right-5 __global_state)
                                                                                                                                                                          (composition-rand-Right-6 __global_state)
                                                                                                                                                                          (composition-rand-Right-7 __global_state)
                                                                                                                                                                          (composition-rand-Right-8 __global_state)
                                                                                                                                                                          (+ 1 (composition-rand-Right-9 __global_state))
                                                                                                                                                                          (composition-rand-Right-10 __global_state)
                                                                                                                                                                          (composition-rand-Right-11 __global_state)
                                                                                                                                                                          (composition-rand-Right-12 __global_state))))
                                                                                                                                                                    (let
                                                                                                                                                                      (
                                                                                                                                                                        (rout
                                                                                                                                                                          (__sample-rand-Right-Bits_n 10 (composition-rand-Right-10 __global_state))))
                                                                                                                                                                      (let
                                                                                                                                                                        (
                                                                                                                                                                          (__global_state
                                                                                                                                                                            (mk-composition-state-Right
                                                                                                                                                                              (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                              (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                              (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                              (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                              (composition-param-Right-zeron __global_state)
                                                                                                                                                                              (composition-param-Right-zerom __global_state)
                                                                                                                                                                              (composition-param-Right-n __global_state)
                                                                                                                                                                              (composition-param-Right-p __global_state)
                                                                                                                                                                              (composition-param-Right-m __global_state)
                                                                                                                                                                              (composition-rand-Right-0 __global_state)
                                                                                                                                                                              (composition-rand-Right-1 __global_state)
                                                                                                                                                                              (composition-rand-Right-2 __global_state)
                                                                                                                                                                              (composition-rand-Right-3 __global_state)
                                                                                                                                                                              (composition-rand-Right-4 __global_state)
                                                                                                                                                                              (composition-rand-Right-5 __global_state)
                                                                                                                                                                              (composition-rand-Right-6 __global_state)
                                                                                                                                                                              (composition-rand-Right-7 __global_state)
                                                                                                                                                                              (composition-rand-Right-8 __global_state)
                                                                                                                                                                              (composition-rand-Right-9 __global_state)
                                                                                                                                                                              (+ 1 (composition-rand-Right-10 __global_state))
                                                                                                                                                                              (composition-rand-Right-11 __global_state)
                                                                                                                                                                              (composition-rand-Right-12 __global_state))))
                                                                                                                                                                        (let
                                                                                                                                                                          ((cin (__func-Right-encn kr kj rin)))
                                                                                                                                                                          (let
                                                                                                                                                                            ((cout (__func-Right-encm kl cin rout)))
                                                                                                                                                                            (let
                                                                                                                                                                              ((C ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))))
                                                                                                                                                                              (let
                                                                                                                                                                                ((C (store C cout (mk-some true))))
                                                                                                                                                                                (let
                                                                                                                                                                                  ((dl true))
                                                                                                                                                                                  (let
                                                                                                                                                                                    ((dr true))
                                                                                                                                                                                    (let
                                                                                                                                                                                      ((unwrap-10 (maybe-get (select Sl dl))))
                                                                                                                                                                                      (let
                                                                                                                                                                                        ((kl unwrap-10))
                                                                                                                                                                                        (let
                                                                                                                                                                                          ((unwrap-11 (maybe-get (select Sr dr))))
                                                                                                                                                                                          (let
                                                                                                                                                                                            ((kr unwrap-11))
                                                                                                                                                                                            (let
                                                                                                                                                                                              ((kj (composition-param-Right-zeron __global_state)))
                                                                                                                                                                                              (ite
                                                                                                                                                                                                (and (or (not dl)) (or (not dr)))
                                                                                                                                                                                                (let
                                                                                                                                                                                                  ((unwrap-12 (maybe-get (select Sj false))))
                                                                                                                                                                                                  (let
                                                                                                                                                                                                    ((kj unwrap-12))
                                                                                                                                                                                                    (let
                                                                                                                                                                                                      (
                                                                                                                                                                                                        (rin
                                                                                                                                                                                                          (__sample-rand-Right-Bits_n 11 (composition-rand-Right-11 __global_state))))
                                                                                                                                                                                                      (let
                                                                                                                                                                                                        (
                                                                                                                                                                                                          (__global_state
                                                                                                                                                                                                            (mk-composition-state-Right
                                                                                                                                                                                                              (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                              (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                              (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                                                              (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                              (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                              (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                              (composition-param-Right-n __global_state)
                                                                                                                                                                                                              (composition-param-Right-p __global_state)
                                                                                                                                                                                                              (composition-param-Right-m __global_state)
                                                                                                                                                                                                              (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                              (+ 1 (composition-rand-Right-11 __global_state))
                                                                                                                                                                                                              (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                                        (let
                                                                                                                                                                                                          (
                                                                                                                                                                                                            (rout
                                                                                                                                                                                                              (__sample-rand-Right-Bits_n 12 (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                                          (let
                                                                                                                                                                                                            (
                                                                                                                                                                                                              (__global_state
                                                                                                                                                                                                                (mk-composition-state-Right
                                                                                                                                                                                                                  (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                                  (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                                  (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                                                                  (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                                  (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                                  (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                                  (composition-param-Right-n __global_state)
                                                                                                                                                                                                                  (composition-param-Right-p __global_state)
                                                                                                                                                                                                                  (composition-param-Right-m __global_state)
                                                                                                                                                                                                                  (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                                  (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                                  (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                                  (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                                  (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                                  (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                                  (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                                  (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                                  (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                                  (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                                  (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                                  (composition-rand-Right-11 __global_state)
                                                                                                                                                                                                                  (+ 1 (composition-rand-Right-12 __global_state)))))
                                                                                                                                                                                                            (let
                                                                                                                                                                                                              ((cin (__func-Right-encn kr kj rin)))
                                                                                                                                                                                                              (let
                                                                                                                                                                                                                ((cout (__func-Right-encm kl cin rout)))
                                                                                                                                                                                                                (let
                                                                                                                                                                                                                  ((C ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))))
                                                                                                                                                                                                                  (let
                                                                                                                                                                                                                    ((C (store C cout (mk-some true))))
                                                                                                                                                                                                                    (let
                                                                                                                                                                                                                      (
                                                                                                                                                                                                                        (__global_state
                                                                                                                                                                                                                          (mk-composition-state-Right
                                                                                                                                                                                                                            (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                                            (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                                            __self_state
                                                                                                                                                                                                                            (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                                            (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                                            (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                                            (composition-param-Right-n __global_state)
                                                                                                                                                                                                                            (composition-param-Right-p __global_state)
                                                                                                                                                                                                                            (composition-param-Right-m __global_state)
                                                                                                                                                                                                                            (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                                            (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                                            (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                                            (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                                            (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                                            (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                                            (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                                            (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                                            (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                                            (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                                            (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                                            (composition-rand-Right-11 __global_state)
                                                                                                                                                                                                                            (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                                                      (mk-return-Right-simgate-GBLG __global_state C))))))))))))
                                                                                                                                                                                                (let
                                                                                                                                                                                                  (
                                                                                                                                                                                                    (rin
                                                                                                                                                                                                      (__sample-rand-Right-Bits_n 11 (composition-rand-Right-11 __global_state))))
                                                                                                                                                                                                  (let
                                                                                                                                                                                                    (
                                                                                                                                                                                                      (__global_state
                                                                                                                                                                                                        (mk-composition-state-Right
                                                                                                                                                                                                          (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                          (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                          (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                                                          (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                          (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                          (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                          (composition-param-Right-n __global_state)
                                                                                                                                                                                                          (composition-param-Right-p __global_state)
                                                                                                                                                                                                          (composition-param-Right-m __global_state)
                                                                                                                                                                                                          (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                          (+ 1 (composition-rand-Right-11 __global_state))
                                                                                                                                                                                                          (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                                    (let
                                                                                                                                                                                                      (
                                                                                                                                                                                                        (rout
                                                                                                                                                                                                          (__sample-rand-Right-Bits_n 12 (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                                      (let
                                                                                                                                                                                                        (
                                                                                                                                                                                                          (__global_state
                                                                                                                                                                                                            (mk-composition-state-Right
                                                                                                                                                                                                              (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                              (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                              (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                                                              (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                              (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                              (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                              (composition-param-Right-n __global_state)
                                                                                                                                                                                                              (composition-param-Right-p __global_state)
                                                                                                                                                                                                              (composition-param-Right-m __global_state)
                                                                                                                                                                                                              (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-11 __global_state)
                                                                                                                                                                                                              (+ 1 (composition-rand-Right-12 __global_state)))))
                                                                                                                                                                                                        (let
                                                                                                                                                                                                          ((cin (__func-Right-encn kr kj rin)))
                                                                                                                                                                                                          (let
                                                                                                                                                                                                            ((cout (__func-Right-encm kl cin rout)))
                                                                                                                                                                                                            (let
                                                                                                                                                                                                              ((C ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))))
                                                                                                                                                                                                              (let
                                                                                                                                                                                                                ((C (store C cout (mk-some true))))
                                                                                                                                                                                                                (let
                                                                                                                                                                                                                  (
                                                                                                                                                                                                                    (__global_state
                                                                                                                                                                                                                      (mk-composition-state-Right
                                                                                                                                                                                                                        (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                                        (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                                        __self_state
                                                                                                                                                                                                                        (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                                        (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                                        (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                                        (composition-param-Right-n __global_state)
                                                                                                                                                                                                                        (composition-param-Right-p __global_state)
                                                                                                                                                                                                                        (composition-param-Right-m __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-11 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                                                  (mk-return-Right-simgate-GBLG __global_state C))))))))))))))))))))))))))))
                                                                                                                                                            (let
                                                                                                                                                              (
                                                                                                                                                                (rin (__sample-rand-Right-Bits_n 9 (composition-rand-Right-9 __global_state))))
                                                                                                                                                              (let
                                                                                                                                                                (
                                                                                                                                                                  (__global_state
                                                                                                                                                                    (mk-composition-state-Right
                                                                                                                                                                      (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                      (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                      (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                      (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                      (composition-param-Right-zeron __global_state)
                                                                                                                                                                      (composition-param-Right-zerom __global_state)
                                                                                                                                                                      (composition-param-Right-n __global_state)
                                                                                                                                                                      (composition-param-Right-p __global_state)
                                                                                                                                                                      (composition-param-Right-m __global_state)
                                                                                                                                                                      (composition-rand-Right-0 __global_state)
                                                                                                                                                                      (composition-rand-Right-1 __global_state)
                                                                                                                                                                      (composition-rand-Right-2 __global_state)
                                                                                                                                                                      (composition-rand-Right-3 __global_state)
                                                                                                                                                                      (composition-rand-Right-4 __global_state)
                                                                                                                                                                      (composition-rand-Right-5 __global_state)
                                                                                                                                                                      (composition-rand-Right-6 __global_state)
                                                                                                                                                                      (composition-rand-Right-7 __global_state)
                                                                                                                                                                      (composition-rand-Right-8 __global_state)
                                                                                                                                                                      (+ 1 (composition-rand-Right-9 __global_state))
                                                                                                                                                                      (composition-rand-Right-10 __global_state)
                                                                                                                                                                      (composition-rand-Right-11 __global_state)
                                                                                                                                                                      (composition-rand-Right-12 __global_state))))
                                                                                                                                                                (let
                                                                                                                                                                  (
                                                                                                                                                                    (rout
                                                                                                                                                                      (__sample-rand-Right-Bits_n 10 (composition-rand-Right-10 __global_state))))
                                                                                                                                                                  (let
                                                                                                                                                                    (
                                                                                                                                                                      (__global_state
                                                                                                                                                                        (mk-composition-state-Right
                                                                                                                                                                          (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                          (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                          (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                          (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                          (composition-param-Right-zeron __global_state)
                                                                                                                                                                          (composition-param-Right-zerom __global_state)
                                                                                                                                                                          (composition-param-Right-n __global_state)
                                                                                                                                                                          (composition-param-Right-p __global_state)
                                                                                                                                                                          (composition-param-Right-m __global_state)
                                                                                                                                                                          (composition-rand-Right-0 __global_state)
                                                                                                                                                                          (composition-rand-Right-1 __global_state)
                                                                                                                                                                          (composition-rand-Right-2 __global_state)
                                                                                                                                                                          (composition-rand-Right-3 __global_state)
                                                                                                                                                                          (composition-rand-Right-4 __global_state)
                                                                                                                                                                          (composition-rand-Right-5 __global_state)
                                                                                                                                                                          (composition-rand-Right-6 __global_state)
                                                                                                                                                                          (composition-rand-Right-7 __global_state)
                                                                                                                                                                          (composition-rand-Right-8 __global_state)
                                                                                                                                                                          (composition-rand-Right-9 __global_state)
                                                                                                                                                                          (+ 1 (composition-rand-Right-10 __global_state))
                                                                                                                                                                          (composition-rand-Right-11 __global_state)
                                                                                                                                                                          (composition-rand-Right-12 __global_state))))
                                                                                                                                                                    (let
                                                                                                                                                                      ((cin (__func-Right-encn kr kj rin)))
                                                                                                                                                                      (let
                                                                                                                                                                        ((cout (__func-Right-encm kl cin rout)))
                                                                                                                                                                        (let
                                                                                                                                                                          ((C ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))))
                                                                                                                                                                          (let
                                                                                                                                                                            ((C (store C cout (mk-some true))))
                                                                                                                                                                            (let
                                                                                                                                                                              ((dl true))
                                                                                                                                                                              (let
                                                                                                                                                                                ((dr true))
                                                                                                                                                                                (let
                                                                                                                                                                                  ((unwrap-10 (maybe-get (select Sl dl))))
                                                                                                                                                                                  (let
                                                                                                                                                                                    ((kl unwrap-10))
                                                                                                                                                                                    (let
                                                                                                                                                                                      ((unwrap-11 (maybe-get (select Sr dr))))
                                                                                                                                                                                      (let
                                                                                                                                                                                        ((kr unwrap-11))
                                                                                                                                                                                        (let
                                                                                                                                                                                          ((kj (composition-param-Right-zeron __global_state)))
                                                                                                                                                                                          (ite
                                                                                                                                                                                            (and (or (not dl)) (or (not dr)))
                                                                                                                                                                                            (let
                                                                                                                                                                                              ((unwrap-12 (maybe-get (select Sj false))))
                                                                                                                                                                                              (let
                                                                                                                                                                                                ((kj unwrap-12))
                                                                                                                                                                                                (let
                                                                                                                                                                                                  (
                                                                                                                                                                                                    (rin
                                                                                                                                                                                                      (__sample-rand-Right-Bits_n 11 (composition-rand-Right-11 __global_state))))
                                                                                                                                                                                                  (let
                                                                                                                                                                                                    (
                                                                                                                                                                                                      (__global_state
                                                                                                                                                                                                        (mk-composition-state-Right
                                                                                                                                                                                                          (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                          (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                          (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                                                          (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                          (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                          (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                          (composition-param-Right-n __global_state)
                                                                                                                                                                                                          (composition-param-Right-p __global_state)
                                                                                                                                                                                                          (composition-param-Right-m __global_state)
                                                                                                                                                                                                          (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                          (+ 1 (composition-rand-Right-11 __global_state))
                                                                                                                                                                                                          (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                                    (let
                                                                                                                                                                                                      (
                                                                                                                                                                                                        (rout
                                                                                                                                                                                                          (__sample-rand-Right-Bits_n 12 (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                                      (let
                                                                                                                                                                                                        (
                                                                                                                                                                                                          (__global_state
                                                                                                                                                                                                            (mk-composition-state-Right
                                                                                                                                                                                                              (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                              (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                              (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                                                              (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                              (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                              (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                              (composition-param-Right-n __global_state)
                                                                                                                                                                                                              (composition-param-Right-p __global_state)
                                                                                                                                                                                                              (composition-param-Right-m __global_state)
                                                                                                                                                                                                              (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-11 __global_state)
                                                                                                                                                                                                              (+ 1 (composition-rand-Right-12 __global_state)))))
                                                                                                                                                                                                        (let
                                                                                                                                                                                                          ((cin (__func-Right-encn kr kj rin)))
                                                                                                                                                                                                          (let
                                                                                                                                                                                                            ((cout (__func-Right-encm kl cin rout)))
                                                                                                                                                                                                            (let
                                                                                                                                                                                                              ((C ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))))
                                                                                                                                                                                                              (let
                                                                                                                                                                                                                ((C (store C cout (mk-some true))))
                                                                                                                                                                                                                (let
                                                                                                                                                                                                                  (
                                                                                                                                                                                                                    (__global_state
                                                                                                                                                                                                                      (mk-composition-state-Right
                                                                                                                                                                                                                        (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                                        (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                                        __self_state
                                                                                                                                                                                                                        (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                                        (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                                        (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                                        (composition-param-Right-n __global_state)
                                                                                                                                                                                                                        (composition-param-Right-p __global_state)
                                                                                                                                                                                                                        (composition-param-Right-m __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-11 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                                                  (mk-return-Right-simgate-GBLG __global_state C))))))))))))
                                                                                                                                                                                            (let
                                                                                                                                                                                              (
                                                                                                                                                                                                (rin
                                                                                                                                                                                                  (__sample-rand-Right-Bits_n 11 (composition-rand-Right-11 __global_state))))
                                                                                                                                                                                              (let
                                                                                                                                                                                                (
                                                                                                                                                                                                  (__global_state
                                                                                                                                                                                                    (mk-composition-state-Right
                                                                                                                                                                                                      (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                      (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                      (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                                                      (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                      (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                      (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                      (composition-param-Right-n __global_state)
                                                                                                                                                                                                      (composition-param-Right-p __global_state)
                                                                                                                                                                                                      (composition-param-Right-m __global_state)
                                                                                                                                                                                                      (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                      (+ 1 (composition-rand-Right-11 __global_state))
                                                                                                                                                                                                      (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                                (let
                                                                                                                                                                                                  (
                                                                                                                                                                                                    (rout
                                                                                                                                                                                                      (__sample-rand-Right-Bits_n 12 (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                                  (let
                                                                                                                                                                                                    (
                                                                                                                                                                                                      (__global_state
                                                                                                                                                                                                        (mk-composition-state-Right
                                                                                                                                                                                                          (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                          (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                          (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                                                          (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                          (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                          (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                          (composition-param-Right-n __global_state)
                                                                                                                                                                                                          (composition-param-Right-p __global_state)
                                                                                                                                                                                                          (composition-param-Right-m __global_state)
                                                                                                                                                                                                          (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-11 __global_state)
                                                                                                                                                                                                          (+ 1 (composition-rand-Right-12 __global_state)))))
                                                                                                                                                                                                    (let
                                                                                                                                                                                                      ((cin (__func-Right-encn kr kj rin)))
                                                                                                                                                                                                      (let
                                                                                                                                                                                                        ((cout (__func-Right-encm kl cin rout)))
                                                                                                                                                                                                        (let
                                                                                                                                                                                                          ((C ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))))
                                                                                                                                                                                                          (let
                                                                                                                                                                                                            ((C (store C cout (mk-some true))))
                                                                                                                                                                                                            (let
                                                                                                                                                                                                              (
                                                                                                                                                                                                                (__global_state
                                                                                                                                                                                                                  (mk-composition-state-Right
                                                                                                                                                                                                                    (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                                    (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                                    __self_state
                                                                                                                                                                                                                    (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                                    (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                                    (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                                    (composition-param-Right-n __global_state)
                                                                                                                                                                                                                    (composition-param-Right-p __global_state)
                                                                                                                                                                                                                    (composition-param-Right-m __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-11 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                                              (mk-return-Right-simgate-GBLG __global_state C))))))))))))))))))))))))))))))))))))))))))))
                                                                                                                        (let
                                                                                                                          (
                                                                                                                            (rin (__sample-rand-Right-Bits_n 7 (composition-rand-Right-7 __global_state))))
                                                                                                                          (let
                                                                                                                            (
                                                                                                                              (__global_state
                                                                                                                                (mk-composition-state-Right
                                                                                                                                  (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                  (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                  (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                  (composition-pkgstate-Right-ev __global_state)
                                                                                                                                  (composition-param-Right-zeron __global_state)
                                                                                                                                  (composition-param-Right-zerom __global_state)
                                                                                                                                  (composition-param-Right-n __global_state)
                                                                                                                                  (composition-param-Right-p __global_state)
                                                                                                                                  (composition-param-Right-m __global_state)
                                                                                                                                  (composition-rand-Right-0 __global_state)
                                                                                                                                  (composition-rand-Right-1 __global_state)
                                                                                                                                  (composition-rand-Right-2 __global_state)
                                                                                                                                  (composition-rand-Right-3 __global_state)
                                                                                                                                  (composition-rand-Right-4 __global_state)
                                                                                                                                  (composition-rand-Right-5 __global_state)
                                                                                                                                  (composition-rand-Right-6 __global_state)
                                                                                                                                  (+ 1 (composition-rand-Right-7 __global_state))
                                                                                                                                  (composition-rand-Right-8 __global_state)
                                                                                                                                  (composition-rand-Right-9 __global_state)
                                                                                                                                  (composition-rand-Right-10 __global_state)
                                                                                                                                  (composition-rand-Right-11 __global_state)
                                                                                                                                  (composition-rand-Right-12 __global_state))))
                                                                                                                            (let
                                                                                                                              (
                                                                                                                                (rout (__sample-rand-Right-Bits_n 8 (composition-rand-Right-8 __global_state))))
                                                                                                                              (let
                                                                                                                                (
                                                                                                                                  (__global_state
                                                                                                                                    (mk-composition-state-Right
                                                                                                                                      (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                      (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                      (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                      (composition-pkgstate-Right-ev __global_state)
                                                                                                                                      (composition-param-Right-zeron __global_state)
                                                                                                                                      (composition-param-Right-zerom __global_state)
                                                                                                                                      (composition-param-Right-n __global_state)
                                                                                                                                      (composition-param-Right-p __global_state)
                                                                                                                                      (composition-param-Right-m __global_state)
                                                                                                                                      (composition-rand-Right-0 __global_state)
                                                                                                                                      (composition-rand-Right-1 __global_state)
                                                                                                                                      (composition-rand-Right-2 __global_state)
                                                                                                                                      (composition-rand-Right-3 __global_state)
                                                                                                                                      (composition-rand-Right-4 __global_state)
                                                                                                                                      (composition-rand-Right-5 __global_state)
                                                                                                                                      (composition-rand-Right-6 __global_state)
                                                                                                                                      (composition-rand-Right-7 __global_state)
                                                                                                                                      (+ 1 (composition-rand-Right-8 __global_state))
                                                                                                                                      (composition-rand-Right-9 __global_state)
                                                                                                                                      (composition-rand-Right-10 __global_state)
                                                                                                                                      (composition-rand-Right-11 __global_state)
                                                                                                                                      (composition-rand-Right-12 __global_state))))
                                                                                                                                (let
                                                                                                                                  ((cin (__func-Right-encn kr kj rin)))
                                                                                                                                  (let
                                                                                                                                    ((cout (__func-Right-encm kl cin rout)))
                                                                                                                                    (let
                                                                                                                                      ((C ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))))
                                                                                                                                      (let
                                                                                                                                        ((C (store C cout (mk-some true))))
                                                                                                                                        (let
                                                                                                                                          ((dl false))
                                                                                                                                          (let
                                                                                                                                            ((dr true))
                                                                                                                                            (let
                                                                                                                                              ((unwrap-7 (maybe-get (select Sl dl))))
                                                                                                                                              (let
                                                                                                                                                ((kl unwrap-7))
                                                                                                                                                (let
                                                                                                                                                  ((unwrap-8 (maybe-get (select Sr dr))))
                                                                                                                                                  (let
                                                                                                                                                    ((kr unwrap-8))
                                                                                                                                                    (let
                                                                                                                                                      ((kj (composition-param-Right-zeron __global_state)))
                                                                                                                                                      (ite
                                                                                                                                                        (and (or (not dl)) (or (not dr)))
                                                                                                                                                        (let
                                                                                                                                                          ((unwrap-9 (maybe-get (select Sj false))))
                                                                                                                                                          (let
                                                                                                                                                            ((kj unwrap-9))
                                                                                                                                                            (let
                                                                                                                                                              (
                                                                                                                                                                (rin (__sample-rand-Right-Bits_n 9 (composition-rand-Right-9 __global_state))))
                                                                                                                                                              (let
                                                                                                                                                                (
                                                                                                                                                                  (__global_state
                                                                                                                                                                    (mk-composition-state-Right
                                                                                                                                                                      (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                      (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                      (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                      (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                      (composition-param-Right-zeron __global_state)
                                                                                                                                                                      (composition-param-Right-zerom __global_state)
                                                                                                                                                                      (composition-param-Right-n __global_state)
                                                                                                                                                                      (composition-param-Right-p __global_state)
                                                                                                                                                                      (composition-param-Right-m __global_state)
                                                                                                                                                                      (composition-rand-Right-0 __global_state)
                                                                                                                                                                      (composition-rand-Right-1 __global_state)
                                                                                                                                                                      (composition-rand-Right-2 __global_state)
                                                                                                                                                                      (composition-rand-Right-3 __global_state)
                                                                                                                                                                      (composition-rand-Right-4 __global_state)
                                                                                                                                                                      (composition-rand-Right-5 __global_state)
                                                                                                                                                                      (composition-rand-Right-6 __global_state)
                                                                                                                                                                      (composition-rand-Right-7 __global_state)
                                                                                                                                                                      (composition-rand-Right-8 __global_state)
                                                                                                                                                                      (+ 1 (composition-rand-Right-9 __global_state))
                                                                                                                                                                      (composition-rand-Right-10 __global_state)
                                                                                                                                                                      (composition-rand-Right-11 __global_state)
                                                                                                                                                                      (composition-rand-Right-12 __global_state))))
                                                                                                                                                                (let
                                                                                                                                                                  (
                                                                                                                                                                    (rout
                                                                                                                                                                      (__sample-rand-Right-Bits_n 10 (composition-rand-Right-10 __global_state))))
                                                                                                                                                                  (let
                                                                                                                                                                    (
                                                                                                                                                                      (__global_state
                                                                                                                                                                        (mk-composition-state-Right
                                                                                                                                                                          (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                          (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                          (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                          (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                          (composition-param-Right-zeron __global_state)
                                                                                                                                                                          (composition-param-Right-zerom __global_state)
                                                                                                                                                                          (composition-param-Right-n __global_state)
                                                                                                                                                                          (composition-param-Right-p __global_state)
                                                                                                                                                                          (composition-param-Right-m __global_state)
                                                                                                                                                                          (composition-rand-Right-0 __global_state)
                                                                                                                                                                          (composition-rand-Right-1 __global_state)
                                                                                                                                                                          (composition-rand-Right-2 __global_state)
                                                                                                                                                                          (composition-rand-Right-3 __global_state)
                                                                                                                                                                          (composition-rand-Right-4 __global_state)
                                                                                                                                                                          (composition-rand-Right-5 __global_state)
                                                                                                                                                                          (composition-rand-Right-6 __global_state)
                                                                                                                                                                          (composition-rand-Right-7 __global_state)
                                                                                                                                                                          (composition-rand-Right-8 __global_state)
                                                                                                                                                                          (composition-rand-Right-9 __global_state)
                                                                                                                                                                          (+ 1 (composition-rand-Right-10 __global_state))
                                                                                                                                                                          (composition-rand-Right-11 __global_state)
                                                                                                                                                                          (composition-rand-Right-12 __global_state))))
                                                                                                                                                                    (let
                                                                                                                                                                      ((cin (__func-Right-encn kr kj rin)))
                                                                                                                                                                      (let
                                                                                                                                                                        ((cout (__func-Right-encm kl cin rout)))
                                                                                                                                                                        (let
                                                                                                                                                                          ((C ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))))
                                                                                                                                                                          (let
                                                                                                                                                                            ((C (store C cout (mk-some true))))
                                                                                                                                                                            (let
                                                                                                                                                                              ((dl true))
                                                                                                                                                                              (let
                                                                                                                                                                                ((dr true))
                                                                                                                                                                                (let
                                                                                                                                                                                  ((unwrap-10 (maybe-get (select Sl dl))))
                                                                                                                                                                                  (let
                                                                                                                                                                                    ((kl unwrap-10))
                                                                                                                                                                                    (let
                                                                                                                                                                                      ((unwrap-11 (maybe-get (select Sr dr))))
                                                                                                                                                                                      (let
                                                                                                                                                                                        ((kr unwrap-11))
                                                                                                                                                                                        (let
                                                                                                                                                                                          ((kj (composition-param-Right-zeron __global_state)))
                                                                                                                                                                                          (ite
                                                                                                                                                                                            (and (or (not dl)) (or (not dr)))
                                                                                                                                                                                            (let
                                                                                                                                                                                              ((unwrap-12 (maybe-get (select Sj false))))
                                                                                                                                                                                              (let
                                                                                                                                                                                                ((kj unwrap-12))
                                                                                                                                                                                                (let
                                                                                                                                                                                                  (
                                                                                                                                                                                                    (rin
                                                                                                                                                                                                      (__sample-rand-Right-Bits_n 11 (composition-rand-Right-11 __global_state))))
                                                                                                                                                                                                  (let
                                                                                                                                                                                                    (
                                                                                                                                                                                                      (__global_state
                                                                                                                                                                                                        (mk-composition-state-Right
                                                                                                                                                                                                          (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                          (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                          (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                                                          (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                          (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                          (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                          (composition-param-Right-n __global_state)
                                                                                                                                                                                                          (composition-param-Right-p __global_state)
                                                                                                                                                                                                          (composition-param-Right-m __global_state)
                                                                                                                                                                                                          (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                          (+ 1 (composition-rand-Right-11 __global_state))
                                                                                                                                                                                                          (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                                    (let
                                                                                                                                                                                                      (
                                                                                                                                                                                                        (rout
                                                                                                                                                                                                          (__sample-rand-Right-Bits_n 12 (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                                      (let
                                                                                                                                                                                                        (
                                                                                                                                                                                                          (__global_state
                                                                                                                                                                                                            (mk-composition-state-Right
                                                                                                                                                                                                              (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                              (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                              (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                                                              (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                              (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                              (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                              (composition-param-Right-n __global_state)
                                                                                                                                                                                                              (composition-param-Right-p __global_state)
                                                                                                                                                                                                              (composition-param-Right-m __global_state)
                                                                                                                                                                                                              (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-11 __global_state)
                                                                                                                                                                                                              (+ 1 (composition-rand-Right-12 __global_state)))))
                                                                                                                                                                                                        (let
                                                                                                                                                                                                          ((cin (__func-Right-encn kr kj rin)))
                                                                                                                                                                                                          (let
                                                                                                                                                                                                            ((cout (__func-Right-encm kl cin rout)))
                                                                                                                                                                                                            (let
                                                                                                                                                                                                              ((C ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))))
                                                                                                                                                                                                              (let
                                                                                                                                                                                                                ((C (store C cout (mk-some true))))
                                                                                                                                                                                                                (let
                                                                                                                                                                                                                  (
                                                                                                                                                                                                                    (__global_state
                                                                                                                                                                                                                      (mk-composition-state-Right
                                                                                                                                                                                                                        (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                                        (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                                        __self_state
                                                                                                                                                                                                                        (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                                        (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                                        (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                                        (composition-param-Right-n __global_state)
                                                                                                                                                                                                                        (composition-param-Right-p __global_state)
                                                                                                                                                                                                                        (composition-param-Right-m __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-11 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                                                  (mk-return-Right-simgate-GBLG __global_state C))))))))))))
                                                                                                                                                                                            (let
                                                                                                                                                                                              (
                                                                                                                                                                                                (rin
                                                                                                                                                                                                  (__sample-rand-Right-Bits_n 11 (composition-rand-Right-11 __global_state))))
                                                                                                                                                                                              (let
                                                                                                                                                                                                (
                                                                                                                                                                                                  (__global_state
                                                                                                                                                                                                    (mk-composition-state-Right
                                                                                                                                                                                                      (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                      (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                      (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                                                      (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                      (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                      (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                      (composition-param-Right-n __global_state)
                                                                                                                                                                                                      (composition-param-Right-p __global_state)
                                                                                                                                                                                                      (composition-param-Right-m __global_state)
                                                                                                                                                                                                      (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                      (+ 1 (composition-rand-Right-11 __global_state))
                                                                                                                                                                                                      (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                                (let
                                                                                                                                                                                                  (
                                                                                                                                                                                                    (rout
                                                                                                                                                                                                      (__sample-rand-Right-Bits_n 12 (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                                  (let
                                                                                                                                                                                                    (
                                                                                                                                                                                                      (__global_state
                                                                                                                                                                                                        (mk-composition-state-Right
                                                                                                                                                                                                          (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                          (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                          (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                                                          (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                          (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                          (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                          (composition-param-Right-n __global_state)
                                                                                                                                                                                                          (composition-param-Right-p __global_state)
                                                                                                                                                                                                          (composition-param-Right-m __global_state)
                                                                                                                                                                                                          (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-11 __global_state)
                                                                                                                                                                                                          (+ 1 (composition-rand-Right-12 __global_state)))))
                                                                                                                                                                                                    (let
                                                                                                                                                                                                      ((cin (__func-Right-encn kr kj rin)))
                                                                                                                                                                                                      (let
                                                                                                                                                                                                        ((cout (__func-Right-encm kl cin rout)))
                                                                                                                                                                                                        (let
                                                                                                                                                                                                          ((C ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))))
                                                                                                                                                                                                          (let
                                                                                                                                                                                                            ((C (store C cout (mk-some true))))
                                                                                                                                                                                                            (let
                                                                                                                                                                                                              (
                                                                                                                                                                                                                (__global_state
                                                                                                                                                                                                                  (mk-composition-state-Right
                                                                                                                                                                                                                    (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                                    (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                                    __self_state
                                                                                                                                                                                                                    (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                                    (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                                    (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                                    (composition-param-Right-n __global_state)
                                                                                                                                                                                                                    (composition-param-Right-p __global_state)
                                                                                                                                                                                                                    (composition-param-Right-m __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-11 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                                              (mk-return-Right-simgate-GBLG __global_state C))))))))))))))))))))))))))))
                                                                                                                                                        (let
                                                                                                                                                          (
                                                                                                                                                            (rin (__sample-rand-Right-Bits_n 9 (composition-rand-Right-9 __global_state))))
                                                                                                                                                          (let
                                                                                                                                                            (
                                                                                                                                                              (__global_state
                                                                                                                                                                (mk-composition-state-Right
                                                                                                                                                                  (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                  (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                  (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                  (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                  (composition-param-Right-zeron __global_state)
                                                                                                                                                                  (composition-param-Right-zerom __global_state)
                                                                                                                                                                  (composition-param-Right-n __global_state)
                                                                                                                                                                  (composition-param-Right-p __global_state)
                                                                                                                                                                  (composition-param-Right-m __global_state)
                                                                                                                                                                  (composition-rand-Right-0 __global_state)
                                                                                                                                                                  (composition-rand-Right-1 __global_state)
                                                                                                                                                                  (composition-rand-Right-2 __global_state)
                                                                                                                                                                  (composition-rand-Right-3 __global_state)
                                                                                                                                                                  (composition-rand-Right-4 __global_state)
                                                                                                                                                                  (composition-rand-Right-5 __global_state)
                                                                                                                                                                  (composition-rand-Right-6 __global_state)
                                                                                                                                                                  (composition-rand-Right-7 __global_state)
                                                                                                                                                                  (composition-rand-Right-8 __global_state)
                                                                                                                                                                  (+ 1 (composition-rand-Right-9 __global_state))
                                                                                                                                                                  (composition-rand-Right-10 __global_state)
                                                                                                                                                                  (composition-rand-Right-11 __global_state)
                                                                                                                                                                  (composition-rand-Right-12 __global_state))))
                                                                                                                                                            (let
                                                                                                                                                              (
                                                                                                                                                                (rout
                                                                                                                                                                  (__sample-rand-Right-Bits_n 10 (composition-rand-Right-10 __global_state))))
                                                                                                                                                              (let
                                                                                                                                                                (
                                                                                                                                                                  (__global_state
                                                                                                                                                                    (mk-composition-state-Right
                                                                                                                                                                      (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                      (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                      (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                      (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                      (composition-param-Right-zeron __global_state)
                                                                                                                                                                      (composition-param-Right-zerom __global_state)
                                                                                                                                                                      (composition-param-Right-n __global_state)
                                                                                                                                                                      (composition-param-Right-p __global_state)
                                                                                                                                                                      (composition-param-Right-m __global_state)
                                                                                                                                                                      (composition-rand-Right-0 __global_state)
                                                                                                                                                                      (composition-rand-Right-1 __global_state)
                                                                                                                                                                      (composition-rand-Right-2 __global_state)
                                                                                                                                                                      (composition-rand-Right-3 __global_state)
                                                                                                                                                                      (composition-rand-Right-4 __global_state)
                                                                                                                                                                      (composition-rand-Right-5 __global_state)
                                                                                                                                                                      (composition-rand-Right-6 __global_state)
                                                                                                                                                                      (composition-rand-Right-7 __global_state)
                                                                                                                                                                      (composition-rand-Right-8 __global_state)
                                                                                                                                                                      (composition-rand-Right-9 __global_state)
                                                                                                                                                                      (+ 1 (composition-rand-Right-10 __global_state))
                                                                                                                                                                      (composition-rand-Right-11 __global_state)
                                                                                                                                                                      (composition-rand-Right-12 __global_state))))
                                                                                                                                                                (let
                                                                                                                                                                  ((cin (__func-Right-encn kr kj rin)))
                                                                                                                                                                  (let
                                                                                                                                                                    ((cout (__func-Right-encm kl cin rout)))
                                                                                                                                                                    (let
                                                                                                                                                                      ((C ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))))
                                                                                                                                                                      (let
                                                                                                                                                                        ((C (store C cout (mk-some true))))
                                                                                                                                                                        (let
                                                                                                                                                                          ((dl true))
                                                                                                                                                                          (let
                                                                                                                                                                            ((dr true))
                                                                                                                                                                            (let
                                                                                                                                                                              ((unwrap-10 (maybe-get (select Sl dl))))
                                                                                                                                                                              (let
                                                                                                                                                                                ((kl unwrap-10))
                                                                                                                                                                                (let
                                                                                                                                                                                  ((unwrap-11 (maybe-get (select Sr dr))))
                                                                                                                                                                                  (let
                                                                                                                                                                                    ((kr unwrap-11))
                                                                                                                                                                                    (let
                                                                                                                                                                                      ((kj (composition-param-Right-zeron __global_state)))
                                                                                                                                                                                      (ite
                                                                                                                                                                                        (and (or (not dl)) (or (not dr)))
                                                                                                                                                                                        (let
                                                                                                                                                                                          ((unwrap-12 (maybe-get (select Sj false))))
                                                                                                                                                                                          (let
                                                                                                                                                                                            ((kj unwrap-12))
                                                                                                                                                                                            (let
                                                                                                                                                                                              (
                                                                                                                                                                                                (rin
                                                                                                                                                                                                  (__sample-rand-Right-Bits_n 11 (composition-rand-Right-11 __global_state))))
                                                                                                                                                                                              (let
                                                                                                                                                                                                (
                                                                                                                                                                                                  (__global_state
                                                                                                                                                                                                    (mk-composition-state-Right
                                                                                                                                                                                                      (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                      (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                      (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                                                      (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                      (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                      (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                      (composition-param-Right-n __global_state)
                                                                                                                                                                                                      (composition-param-Right-p __global_state)
                                                                                                                                                                                                      (composition-param-Right-m __global_state)
                                                                                                                                                                                                      (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                      (+ 1 (composition-rand-Right-11 __global_state))
                                                                                                                                                                                                      (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                                (let
                                                                                                                                                                                                  (
                                                                                                                                                                                                    (rout
                                                                                                                                                                                                      (__sample-rand-Right-Bits_n 12 (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                                  (let
                                                                                                                                                                                                    (
                                                                                                                                                                                                      (__global_state
                                                                                                                                                                                                        (mk-composition-state-Right
                                                                                                                                                                                                          (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                          (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                          (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                                                          (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                          (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                          (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                          (composition-param-Right-n __global_state)
                                                                                                                                                                                                          (composition-param-Right-p __global_state)
                                                                                                                                                                                                          (composition-param-Right-m __global_state)
                                                                                                                                                                                                          (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-11 __global_state)
                                                                                                                                                                                                          (+ 1 (composition-rand-Right-12 __global_state)))))
                                                                                                                                                                                                    (let
                                                                                                                                                                                                      ((cin (__func-Right-encn kr kj rin)))
                                                                                                                                                                                                      (let
                                                                                                                                                                                                        ((cout (__func-Right-encm kl cin rout)))
                                                                                                                                                                                                        (let
                                                                                                                                                                                                          ((C ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))))
                                                                                                                                                                                                          (let
                                                                                                                                                                                                            ((C (store C cout (mk-some true))))
                                                                                                                                                                                                            (let
                                                                                                                                                                                                              (
                                                                                                                                                                                                                (__global_state
                                                                                                                                                                                                                  (mk-composition-state-Right
                                                                                                                                                                                                                    (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                                    (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                                    __self_state
                                                                                                                                                                                                                    (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                                    (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                                    (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                                    (composition-param-Right-n __global_state)
                                                                                                                                                                                                                    (composition-param-Right-p __global_state)
                                                                                                                                                                                                                    (composition-param-Right-m __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-11 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                                              (mk-return-Right-simgate-GBLG __global_state C))))))))))))
                                                                                                                                                                                        (let
                                                                                                                                                                                          (
                                                                                                                                                                                            (rin
                                                                                                                                                                                              (__sample-rand-Right-Bits_n 11 (composition-rand-Right-11 __global_state))))
                                                                                                                                                                                          (let
                                                                                                                                                                                            (
                                                                                                                                                                                              (__global_state
                                                                                                                                                                                                (mk-composition-state-Right
                                                                                                                                                                                                  (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                  (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                  (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                                                  (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                  (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                  (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                  (composition-param-Right-n __global_state)
                                                                                                                                                                                                  (composition-param-Right-p __global_state)
                                                                                                                                                                                                  (composition-param-Right-m __global_state)
                                                                                                                                                                                                  (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                  (+ 1 (composition-rand-Right-11 __global_state))
                                                                                                                                                                                                  (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                            (let
                                                                                                                                                                                              (
                                                                                                                                                                                                (rout
                                                                                                                                                                                                  (__sample-rand-Right-Bits_n 12 (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                              (let
                                                                                                                                                                                                (
                                                                                                                                                                                                  (__global_state
                                                                                                                                                                                                    (mk-composition-state-Right
                                                                                                                                                                                                      (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                      (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                      (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                                                      (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                      (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                      (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                      (composition-param-Right-n __global_state)
                                                                                                                                                                                                      (composition-param-Right-p __global_state)
                                                                                                                                                                                                      (composition-param-Right-m __global_state)
                                                                                                                                                                                                      (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-11 __global_state)
                                                                                                                                                                                                      (+ 1 (composition-rand-Right-12 __global_state)))))
                                                                                                                                                                                                (let
                                                                                                                                                                                                  ((cin (__func-Right-encn kr kj rin)))
                                                                                                                                                                                                  (let
                                                                                                                                                                                                    ((cout (__func-Right-encm kl cin rout)))
                                                                                                                                                                                                    (let
                                                                                                                                                                                                      ((C ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))))
                                                                                                                                                                                                      (let
                                                                                                                                                                                                        ((C (store C cout (mk-some true))))
                                                                                                                                                                                                        (let
                                                                                                                                                                                                          (
                                                                                                                                                                                                            (__global_state
                                                                                                                                                                                                              (mk-composition-state-Right
                                                                                                                                                                                                                (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                                (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                                __self_state
                                                                                                                                                                                                                (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                                (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                                (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                                (composition-param-Right-n __global_state)
                                                                                                                                                                                                                (composition-param-Right-p __global_state)
                                                                                                                                                                                                                (composition-param-Right-m __global_state)
                                                                                                                                                                                                                (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-11 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                                          (mk-return-Right-simgate-GBLG __global_state C))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                                    (let
                                                                                      (
                                                                                        (rin (__sample-rand-Right-Bits_n 5 (composition-rand-Right-5 __global_state))))
                                                                                      (let
                                                                                        (
                                                                                          (__global_state
                                                                                            (mk-composition-state-Right
                                                                                              (composition-pkgstate-Right-keys_top __global_state)
                                                                                              (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                              (composition-pkgstate-Right-simgate __global_state)
                                                                                              (composition-pkgstate-Right-ev __global_state)
                                                                                              (composition-param-Right-zeron __global_state)
                                                                                              (composition-param-Right-zerom __global_state)
                                                                                              (composition-param-Right-n __global_state)
                                                                                              (composition-param-Right-p __global_state)
                                                                                              (composition-param-Right-m __global_state)
                                                                                              (composition-rand-Right-0 __global_state)
                                                                                              (composition-rand-Right-1 __global_state)
                                                                                              (composition-rand-Right-2 __global_state)
                                                                                              (composition-rand-Right-3 __global_state)
                                                                                              (composition-rand-Right-4 __global_state)
                                                                                              (+ 1 (composition-rand-Right-5 __global_state))
                                                                                              (composition-rand-Right-6 __global_state)
                                                                                              (composition-rand-Right-7 __global_state)
                                                                                              (composition-rand-Right-8 __global_state)
                                                                                              (composition-rand-Right-9 __global_state)
                                                                                              (composition-rand-Right-10 __global_state)
                                                                                              (composition-rand-Right-11 __global_state)
                                                                                              (composition-rand-Right-12 __global_state))))
                                                                                        (let
                                                                                          (
                                                                                            (rout (__sample-rand-Right-Bits_n 6 (composition-rand-Right-6 __global_state))))
                                                                                          (let
                                                                                            (
                                                                                              (__global_state
                                                                                                (mk-composition-state-Right
                                                                                                  (composition-pkgstate-Right-keys_top __global_state)
                                                                                                  (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                  (composition-pkgstate-Right-simgate __global_state)
                                                                                                  (composition-pkgstate-Right-ev __global_state)
                                                                                                  (composition-param-Right-zeron __global_state)
                                                                                                  (composition-param-Right-zerom __global_state)
                                                                                                  (composition-param-Right-n __global_state)
                                                                                                  (composition-param-Right-p __global_state)
                                                                                                  (composition-param-Right-m __global_state)
                                                                                                  (composition-rand-Right-0 __global_state)
                                                                                                  (composition-rand-Right-1 __global_state)
                                                                                                  (composition-rand-Right-2 __global_state)
                                                                                                  (composition-rand-Right-3 __global_state)
                                                                                                  (composition-rand-Right-4 __global_state)
                                                                                                  (composition-rand-Right-5 __global_state)
                                                                                                  (+ 1 (composition-rand-Right-6 __global_state))
                                                                                                  (composition-rand-Right-7 __global_state)
                                                                                                  (composition-rand-Right-8 __global_state)
                                                                                                  (composition-rand-Right-9 __global_state)
                                                                                                  (composition-rand-Right-10 __global_state)
                                                                                                  (composition-rand-Right-11 __global_state)
                                                                                                  (composition-rand-Right-12 __global_state))))
                                                                                            (let
                                                                                              ((cin (__func-Right-encn kr kj rin)))
                                                                                              (let
                                                                                                ((cout (__func-Right-encm kl cin rout)))
                                                                                                (let
                                                                                                  ((C ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))))
                                                                                                  (let
                                                                                                    ((C (store C cout (mk-some true))))
                                                                                                    (let
                                                                                                      ((dl true))
                                                                                                      (let
                                                                                                        ((dr false))
                                                                                                        (let
                                                                                                          ((unwrap-4 (maybe-get (select Sl dl))))
                                                                                                          (let
                                                                                                            ((kl unwrap-4))
                                                                                                            (let
                                                                                                              ((unwrap-5 (maybe-get (select Sr dr))))
                                                                                                              (let
                                                                                                                ((kr unwrap-5))
                                                                                                                (let
                                                                                                                  ((kj (composition-param-Right-zeron __global_state)))
                                                                                                                  (ite
                                                                                                                    (and (or (not dl)) (or (not dr)))
                                                                                                                    (let
                                                                                                                      ((unwrap-6 (maybe-get (select Sj false))))
                                                                                                                      (let
                                                                                                                        ((kj unwrap-6))
                                                                                                                        (let
                                                                                                                          (
                                                                                                                            (rin (__sample-rand-Right-Bits_n 7 (composition-rand-Right-7 __global_state))))
                                                                                                                          (let
                                                                                                                            (
                                                                                                                              (__global_state
                                                                                                                                (mk-composition-state-Right
                                                                                                                                  (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                  (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                  (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                  (composition-pkgstate-Right-ev __global_state)
                                                                                                                                  (composition-param-Right-zeron __global_state)
                                                                                                                                  (composition-param-Right-zerom __global_state)
                                                                                                                                  (composition-param-Right-n __global_state)
                                                                                                                                  (composition-param-Right-p __global_state)
                                                                                                                                  (composition-param-Right-m __global_state)
                                                                                                                                  (composition-rand-Right-0 __global_state)
                                                                                                                                  (composition-rand-Right-1 __global_state)
                                                                                                                                  (composition-rand-Right-2 __global_state)
                                                                                                                                  (composition-rand-Right-3 __global_state)
                                                                                                                                  (composition-rand-Right-4 __global_state)
                                                                                                                                  (composition-rand-Right-5 __global_state)
                                                                                                                                  (composition-rand-Right-6 __global_state)
                                                                                                                                  (+ 1 (composition-rand-Right-7 __global_state))
                                                                                                                                  (composition-rand-Right-8 __global_state)
                                                                                                                                  (composition-rand-Right-9 __global_state)
                                                                                                                                  (composition-rand-Right-10 __global_state)
                                                                                                                                  (composition-rand-Right-11 __global_state)
                                                                                                                                  (composition-rand-Right-12 __global_state))))
                                                                                                                            (let
                                                                                                                              (
                                                                                                                                (rout (__sample-rand-Right-Bits_n 8 (composition-rand-Right-8 __global_state))))
                                                                                                                              (let
                                                                                                                                (
                                                                                                                                  (__global_state
                                                                                                                                    (mk-composition-state-Right
                                                                                                                                      (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                      (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                      (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                      (composition-pkgstate-Right-ev __global_state)
                                                                                                                                      (composition-param-Right-zeron __global_state)
                                                                                                                                      (composition-param-Right-zerom __global_state)
                                                                                                                                      (composition-param-Right-n __global_state)
                                                                                                                                      (composition-param-Right-p __global_state)
                                                                                                                                      (composition-param-Right-m __global_state)
                                                                                                                                      (composition-rand-Right-0 __global_state)
                                                                                                                                      (composition-rand-Right-1 __global_state)
                                                                                                                                      (composition-rand-Right-2 __global_state)
                                                                                                                                      (composition-rand-Right-3 __global_state)
                                                                                                                                      (composition-rand-Right-4 __global_state)
                                                                                                                                      (composition-rand-Right-5 __global_state)
                                                                                                                                      (composition-rand-Right-6 __global_state)
                                                                                                                                      (composition-rand-Right-7 __global_state)
                                                                                                                                      (+ 1 (composition-rand-Right-8 __global_state))
                                                                                                                                      (composition-rand-Right-9 __global_state)
                                                                                                                                      (composition-rand-Right-10 __global_state)
                                                                                                                                      (composition-rand-Right-11 __global_state)
                                                                                                                                      (composition-rand-Right-12 __global_state))))
                                                                                                                                (let
                                                                                                                                  ((cin (__func-Right-encn kr kj rin)))
                                                                                                                                  (let
                                                                                                                                    ((cout (__func-Right-encm kl cin rout)))
                                                                                                                                    (let
                                                                                                                                      ((C ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))))
                                                                                                                                      (let
                                                                                                                                        ((C (store C cout (mk-some true))))
                                                                                                                                        (let
                                                                                                                                          ((dl false))
                                                                                                                                          (let
                                                                                                                                            ((dr true))
                                                                                                                                            (let
                                                                                                                                              ((unwrap-7 (maybe-get (select Sl dl))))
                                                                                                                                              (let
                                                                                                                                                ((kl unwrap-7))
                                                                                                                                                (let
                                                                                                                                                  ((unwrap-8 (maybe-get (select Sr dr))))
                                                                                                                                                  (let
                                                                                                                                                    ((kr unwrap-8))
                                                                                                                                                    (let
                                                                                                                                                      ((kj (composition-param-Right-zeron __global_state)))
                                                                                                                                                      (ite
                                                                                                                                                        (and (or (not dl)) (or (not dr)))
                                                                                                                                                        (let
                                                                                                                                                          ((unwrap-9 (maybe-get (select Sj false))))
                                                                                                                                                          (let
                                                                                                                                                            ((kj unwrap-9))
                                                                                                                                                            (let
                                                                                                                                                              (
                                                                                                                                                                (rin (__sample-rand-Right-Bits_n 9 (composition-rand-Right-9 __global_state))))
                                                                                                                                                              (let
                                                                                                                                                                (
                                                                                                                                                                  (__global_state
                                                                                                                                                                    (mk-composition-state-Right
                                                                                                                                                                      (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                      (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                      (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                      (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                      (composition-param-Right-zeron __global_state)
                                                                                                                                                                      (composition-param-Right-zerom __global_state)
                                                                                                                                                                      (composition-param-Right-n __global_state)
                                                                                                                                                                      (composition-param-Right-p __global_state)
                                                                                                                                                                      (composition-param-Right-m __global_state)
                                                                                                                                                                      (composition-rand-Right-0 __global_state)
                                                                                                                                                                      (composition-rand-Right-1 __global_state)
                                                                                                                                                                      (composition-rand-Right-2 __global_state)
                                                                                                                                                                      (composition-rand-Right-3 __global_state)
                                                                                                                                                                      (composition-rand-Right-4 __global_state)
                                                                                                                                                                      (composition-rand-Right-5 __global_state)
                                                                                                                                                                      (composition-rand-Right-6 __global_state)
                                                                                                                                                                      (composition-rand-Right-7 __global_state)
                                                                                                                                                                      (composition-rand-Right-8 __global_state)
                                                                                                                                                                      (+ 1 (composition-rand-Right-9 __global_state))
                                                                                                                                                                      (composition-rand-Right-10 __global_state)
                                                                                                                                                                      (composition-rand-Right-11 __global_state)
                                                                                                                                                                      (composition-rand-Right-12 __global_state))))
                                                                                                                                                                (let
                                                                                                                                                                  (
                                                                                                                                                                    (rout
                                                                                                                                                                      (__sample-rand-Right-Bits_n 10 (composition-rand-Right-10 __global_state))))
                                                                                                                                                                  (let
                                                                                                                                                                    (
                                                                                                                                                                      (__global_state
                                                                                                                                                                        (mk-composition-state-Right
                                                                                                                                                                          (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                          (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                          (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                          (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                          (composition-param-Right-zeron __global_state)
                                                                                                                                                                          (composition-param-Right-zerom __global_state)
                                                                                                                                                                          (composition-param-Right-n __global_state)
                                                                                                                                                                          (composition-param-Right-p __global_state)
                                                                                                                                                                          (composition-param-Right-m __global_state)
                                                                                                                                                                          (composition-rand-Right-0 __global_state)
                                                                                                                                                                          (composition-rand-Right-1 __global_state)
                                                                                                                                                                          (composition-rand-Right-2 __global_state)
                                                                                                                                                                          (composition-rand-Right-3 __global_state)
                                                                                                                                                                          (composition-rand-Right-4 __global_state)
                                                                                                                                                                          (composition-rand-Right-5 __global_state)
                                                                                                                                                                          (composition-rand-Right-6 __global_state)
                                                                                                                                                                          (composition-rand-Right-7 __global_state)
                                                                                                                                                                          (composition-rand-Right-8 __global_state)
                                                                                                                                                                          (composition-rand-Right-9 __global_state)
                                                                                                                                                                          (+ 1 (composition-rand-Right-10 __global_state))
                                                                                                                                                                          (composition-rand-Right-11 __global_state)
                                                                                                                                                                          (composition-rand-Right-12 __global_state))))
                                                                                                                                                                    (let
                                                                                                                                                                      ((cin (__func-Right-encn kr kj rin)))
                                                                                                                                                                      (let
                                                                                                                                                                        ((cout (__func-Right-encm kl cin rout)))
                                                                                                                                                                        (let
                                                                                                                                                                          ((C ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))))
                                                                                                                                                                          (let
                                                                                                                                                                            ((C (store C cout (mk-some true))))
                                                                                                                                                                            (let
                                                                                                                                                                              ((dl true))
                                                                                                                                                                              (let
                                                                                                                                                                                ((dr true))
                                                                                                                                                                                (let
                                                                                                                                                                                  ((unwrap-10 (maybe-get (select Sl dl))))
                                                                                                                                                                                  (let
                                                                                                                                                                                    ((kl unwrap-10))
                                                                                                                                                                                    (let
                                                                                                                                                                                      ((unwrap-11 (maybe-get (select Sr dr))))
                                                                                                                                                                                      (let
                                                                                                                                                                                        ((kr unwrap-11))
                                                                                                                                                                                        (let
                                                                                                                                                                                          ((kj (composition-param-Right-zeron __global_state)))
                                                                                                                                                                                          (ite
                                                                                                                                                                                            (and (or (not dl)) (or (not dr)))
                                                                                                                                                                                            (let
                                                                                                                                                                                              ((unwrap-12 (maybe-get (select Sj false))))
                                                                                                                                                                                              (let
                                                                                                                                                                                                ((kj unwrap-12))
                                                                                                                                                                                                (let
                                                                                                                                                                                                  (
                                                                                                                                                                                                    (rin
                                                                                                                                                                                                      (__sample-rand-Right-Bits_n 11 (composition-rand-Right-11 __global_state))))
                                                                                                                                                                                                  (let
                                                                                                                                                                                                    (
                                                                                                                                                                                                      (__global_state
                                                                                                                                                                                                        (mk-composition-state-Right
                                                                                                                                                                                                          (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                          (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                          (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                                                          (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                          (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                          (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                          (composition-param-Right-n __global_state)
                                                                                                                                                                                                          (composition-param-Right-p __global_state)
                                                                                                                                                                                                          (composition-param-Right-m __global_state)
                                                                                                                                                                                                          (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                          (+ 1 (composition-rand-Right-11 __global_state))
                                                                                                                                                                                                          (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                                    (let
                                                                                                                                                                                                      (
                                                                                                                                                                                                        (rout
                                                                                                                                                                                                          (__sample-rand-Right-Bits_n 12 (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                                      (let
                                                                                                                                                                                                        (
                                                                                                                                                                                                          (__global_state
                                                                                                                                                                                                            (mk-composition-state-Right
                                                                                                                                                                                                              (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                              (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                              (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                                                              (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                              (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                              (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                              (composition-param-Right-n __global_state)
                                                                                                                                                                                                              (composition-param-Right-p __global_state)
                                                                                                                                                                                                              (composition-param-Right-m __global_state)
                                                                                                                                                                                                              (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                              (composition-rand-Right-11 __global_state)
                                                                                                                                                                                                              (+ 1 (composition-rand-Right-12 __global_state)))))
                                                                                                                                                                                                        (let
                                                                                                                                                                                                          ((cin (__func-Right-encn kr kj rin)))
                                                                                                                                                                                                          (let
                                                                                                                                                                                                            ((cout (__func-Right-encm kl cin rout)))
                                                                                                                                                                                                            (let
                                                                                                                                                                                                              ((C ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))))
                                                                                                                                                                                                              (let
                                                                                                                                                                                                                ((C (store C cout (mk-some true))))
                                                                                                                                                                                                                (let
                                                                                                                                                                                                                  (
                                                                                                                                                                                                                    (__global_state
                                                                                                                                                                                                                      (mk-composition-state-Right
                                                                                                                                                                                                                        (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                                        (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                                        __self_state
                                                                                                                                                                                                                        (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                                        (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                                        (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                                        (composition-param-Right-n __global_state)
                                                                                                                                                                                                                        (composition-param-Right-p __global_state)
                                                                                                                                                                                                                        (composition-param-Right-m __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-11 __global_state)
                                                                                                                                                                                                                        (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                                                  (mk-return-Right-simgate-GBLG __global_state C))))))))))))
                                                                                                                                                                                            (let
                                                                                                                                                                                              (
                                                                                                                                                                                                (rin
                                                                                                                                                                                                  (__sample-rand-Right-Bits_n 11 (composition-rand-Right-11 __global_state))))
                                                                                                                                                                                              (let
                                                                                                                                                                                                (
                                                                                                                                                                                                  (__global_state
                                                                                                                                                                                                    (mk-composition-state-Right
                                                                                                                                                                                                      (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                      (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                      (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                                                      (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                      (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                      (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                      (composition-param-Right-n __global_state)
                                                                                                                                                                                                      (composition-param-Right-p __global_state)
                                                                                                                                                                                                      (composition-param-Right-m __global_state)
                                                                                                                                                                                                      (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                      (+ 1 (composition-rand-Right-11 __global_state))
                                                                                                                                                                                                      (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                                (let
                                                                                                                                                                                                  (
                                                                                                                                                                                                    (rout
                                                                                                                                                                                                      (__sample-rand-Right-Bits_n 12 (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                                  (let
                                                                                                                                                                                                    (
                                                                                                                                                                                                      (__global_state
                                                                                                                                                                                                        (mk-composition-state-Right
                                                                                                                                                                                                          (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                          (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                          (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                                                          (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                          (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                          (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                          (composition-param-Right-n __global_state)
                                                                                                                                                                                                          (composition-param-Right-p __global_state)
                                                                                                                                                                                                          (composition-param-Right-m __global_state)
                                                                                                                                                                                                          (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-11 __global_state)
                                                                                                                                                                                                          (+ 1 (composition-rand-Right-12 __global_state)))))
                                                                                                                                                                                                    (let
                                                                                                                                                                                                      ((cin (__func-Right-encn kr kj rin)))
                                                                                                                                                                                                      (let
                                                                                                                                                                                                        ((cout (__func-Right-encm kl cin rout)))
                                                                                                                                                                                                        (let
                                                                                                                                                                                                          ((C ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))))
                                                                                                                                                                                                          (let
                                                                                                                                                                                                            ((C (store C cout (mk-some true))))
                                                                                                                                                                                                            (let
                                                                                                                                                                                                              (
                                                                                                                                                                                                                (__global_state
                                                                                                                                                                                                                  (mk-composition-state-Right
                                                                                                                                                                                                                    (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                                    (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                                    __self_state
                                                                                                                                                                                                                    (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                                    (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                                    (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                                    (composition-param-Right-n __global_state)
                                                                                                                                                                                                                    (composition-param-Right-p __global_state)
                                                                                                                                                                                                                    (composition-param-Right-m __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-11 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                                              (mk-return-Right-simgate-GBLG __global_state C))))))))))))))))))))))))))))
                                                                                                                                                        (let
                                                                                                                                                          (
                                                                                                                                                            (rin (__sample-rand-Right-Bits_n 9 (composition-rand-Right-9 __global_state))))
                                                                                                                                                          (let
                                                                                                                                                            (
                                                                                                                                                              (__global_state
                                                                                                                                                                (mk-composition-state-Right
                                                                                                                                                                  (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                  (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                  (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                  (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                  (composition-param-Right-zeron __global_state)
                                                                                                                                                                  (composition-param-Right-zerom __global_state)
                                                                                                                                                                  (composition-param-Right-n __global_state)
                                                                                                                                                                  (composition-param-Right-p __global_state)
                                                                                                                                                                  (composition-param-Right-m __global_state)
                                                                                                                                                                  (composition-rand-Right-0 __global_state)
                                                                                                                                                                  (composition-rand-Right-1 __global_state)
                                                                                                                                                                  (composition-rand-Right-2 __global_state)
                                                                                                                                                                  (composition-rand-Right-3 __global_state)
                                                                                                                                                                  (composition-rand-Right-4 __global_state)
                                                                                                                                                                  (composition-rand-Right-5 __global_state)
                                                                                                                                                                  (composition-rand-Right-6 __global_state)
                                                                                                                                                                  (composition-rand-Right-7 __global_state)
                                                                                                                                                                  (composition-rand-Right-8 __global_state)
                                                                                                                                                                  (+ 1 (composition-rand-Right-9 __global_state))
                                                                                                                                                                  (composition-rand-Right-10 __global_state)
                                                                                                                                                                  (composition-rand-Right-11 __global_state)
                                                                                                                                                                  (composition-rand-Right-12 __global_state))))
                                                                                                                                                            (let
                                                                                                                                                              (
                                                                                                                                                                (rout
                                                                                                                                                                  (__sample-rand-Right-Bits_n 10 (composition-rand-Right-10 __global_state))))
                                                                                                                                                              (let
                                                                                                                                                                (
                                                                                                                                                                  (__global_state
                                                                                                                                                                    (mk-composition-state-Right
                                                                                                                                                                      (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                      (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                      (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                      (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                      (composition-param-Right-zeron __global_state)
                                                                                                                                                                      (composition-param-Right-zerom __global_state)
                                                                                                                                                                      (composition-param-Right-n __global_state)
                                                                                                                                                                      (composition-param-Right-p __global_state)
                                                                                                                                                                      (composition-param-Right-m __global_state)
                                                                                                                                                                      (composition-rand-Right-0 __global_state)
                                                                                                                                                                      (composition-rand-Right-1 __global_state)
                                                                                                                                                                      (composition-rand-Right-2 __global_state)
                                                                                                                                                                      (composition-rand-Right-3 __global_state)
                                                                                                                                                                      (composition-rand-Right-4 __global_state)
                                                                                                                                                                      (composition-rand-Right-5 __global_state)
                                                                                                                                                                      (composition-rand-Right-6 __global_state)
                                                                                                                                                                      (composition-rand-Right-7 __global_state)
                                                                                                                                                                      (composition-rand-Right-8 __global_state)
                                                                                                                                                                      (composition-rand-Right-9 __global_state)
                                                                                                                                                                      (+ 1 (composition-rand-Right-10 __global_state))
                                                                                                                                                                      (composition-rand-Right-11 __global_state)
                                                                                                                                                                      (composition-rand-Right-12 __global_state))))
                                                                                                                                                                (let
                                                                                                                                                                  ((cin (__func-Right-encn kr kj rin)))
                                                                                                                                                                  (let
                                                                                                                                                                    ((cout (__func-Right-encm kl cin rout)))
                                                                                                                                                                    (let
                                                                                                                                                                      ((C ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))))
                                                                                                                                                                      (let
                                                                                                                                                                        ((C (store C cout (mk-some true))))
                                                                                                                                                                        (let
                                                                                                                                                                          ((dl true))
                                                                                                                                                                          (let
                                                                                                                                                                            ((dr true))
                                                                                                                                                                            (let
                                                                                                                                                                              ((unwrap-10 (maybe-get (select Sl dl))))
                                                                                                                                                                              (let
                                                                                                                                                                                ((kl unwrap-10))
                                                                                                                                                                                (let
                                                                                                                                                                                  ((unwrap-11 (maybe-get (select Sr dr))))
                                                                                                                                                                                  (let
                                                                                                                                                                                    ((kr unwrap-11))
                                                                                                                                                                                    (let
                                                                                                                                                                                      ((kj (composition-param-Right-zeron __global_state)))
                                                                                                                                                                                      (ite
                                                                                                                                                                                        (and (or (not dl)) (or (not dr)))
                                                                                                                                                                                        (let
                                                                                                                                                                                          ((unwrap-12 (maybe-get (select Sj false))))
                                                                                                                                                                                          (let
                                                                                                                                                                                            ((kj unwrap-12))
                                                                                                                                                                                            (let
                                                                                                                                                                                              (
                                                                                                                                                                                                (rin
                                                                                                                                                                                                  (__sample-rand-Right-Bits_n 11 (composition-rand-Right-11 __global_state))))
                                                                                                                                                                                              (let
                                                                                                                                                                                                (
                                                                                                                                                                                                  (__global_state
                                                                                                                                                                                                    (mk-composition-state-Right
                                                                                                                                                                                                      (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                      (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                      (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                                                      (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                      (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                      (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                      (composition-param-Right-n __global_state)
                                                                                                                                                                                                      (composition-param-Right-p __global_state)
                                                                                                                                                                                                      (composition-param-Right-m __global_state)
                                                                                                                                                                                                      (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                      (+ 1 (composition-rand-Right-11 __global_state))
                                                                                                                                                                                                      (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                                (let
                                                                                                                                                                                                  (
                                                                                                                                                                                                    (rout
                                                                                                                                                                                                      (__sample-rand-Right-Bits_n 12 (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                                  (let
                                                                                                                                                                                                    (
                                                                                                                                                                                                      (__global_state
                                                                                                                                                                                                        (mk-composition-state-Right
                                                                                                                                                                                                          (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                          (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                          (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                                                          (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                          (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                          (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                          (composition-param-Right-n __global_state)
                                                                                                                                                                                                          (composition-param-Right-p __global_state)
                                                                                                                                                                                                          (composition-param-Right-m __global_state)
                                                                                                                                                                                                          (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-11 __global_state)
                                                                                                                                                                                                          (+ 1 (composition-rand-Right-12 __global_state)))))
                                                                                                                                                                                                    (let
                                                                                                                                                                                                      ((cin (__func-Right-encn kr kj rin)))
                                                                                                                                                                                                      (let
                                                                                                                                                                                                        ((cout (__func-Right-encm kl cin rout)))
                                                                                                                                                                                                        (let
                                                                                                                                                                                                          ((C ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))))
                                                                                                                                                                                                          (let
                                                                                                                                                                                                            ((C (store C cout (mk-some true))))
                                                                                                                                                                                                            (let
                                                                                                                                                                                                              (
                                                                                                                                                                                                                (__global_state
                                                                                                                                                                                                                  (mk-composition-state-Right
                                                                                                                                                                                                                    (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                                    (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                                    __self_state
                                                                                                                                                                                                                    (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                                    (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                                    (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                                    (composition-param-Right-n __global_state)
                                                                                                                                                                                                                    (composition-param-Right-p __global_state)
                                                                                                                                                                                                                    (composition-param-Right-m __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-11 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                                              (mk-return-Right-simgate-GBLG __global_state C))))))))))))
                                                                                                                                                                                        (let
                                                                                                                                                                                          (
                                                                                                                                                                                            (rin
                                                                                                                                                                                              (__sample-rand-Right-Bits_n 11 (composition-rand-Right-11 __global_state))))
                                                                                                                                                                                          (let
                                                                                                                                                                                            (
                                                                                                                                                                                              (__global_state
                                                                                                                                                                                                (mk-composition-state-Right
                                                                                                                                                                                                  (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                  (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                  (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                                                  (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                  (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                  (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                  (composition-param-Right-n __global_state)
                                                                                                                                                                                                  (composition-param-Right-p __global_state)
                                                                                                                                                                                                  (composition-param-Right-m __global_state)
                                                                                                                                                                                                  (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                  (+ 1 (composition-rand-Right-11 __global_state))
                                                                                                                                                                                                  (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                            (let
                                                                                                                                                                                              (
                                                                                                                                                                                                (rout
                                                                                                                                                                                                  (__sample-rand-Right-Bits_n 12 (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                              (let
                                                                                                                                                                                                (
                                                                                                                                                                                                  (__global_state
                                                                                                                                                                                                    (mk-composition-state-Right
                                                                                                                                                                                                      (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                      (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                      (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                                                      (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                      (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                      (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                      (composition-param-Right-n __global_state)
                                                                                                                                                                                                      (composition-param-Right-p __global_state)
                                                                                                                                                                                                      (composition-param-Right-m __global_state)
                                                                                                                                                                                                      (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-11 __global_state)
                                                                                                                                                                                                      (+ 1 (composition-rand-Right-12 __global_state)))))
                                                                                                                                                                                                (let
                                                                                                                                                                                                  ((cin (__func-Right-encn kr kj rin)))
                                                                                                                                                                                                  (let
                                                                                                                                                                                                    ((cout (__func-Right-encm kl cin rout)))
                                                                                                                                                                                                    (let
                                                                                                                                                                                                      ((C ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))))
                                                                                                                                                                                                      (let
                                                                                                                                                                                                        ((C (store C cout (mk-some true))))
                                                                                                                                                                                                        (let
                                                                                                                                                                                                          (
                                                                                                                                                                                                            (__global_state
                                                                                                                                                                                                              (mk-composition-state-Right
                                                                                                                                                                                                                (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                                (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                                __self_state
                                                                                                                                                                                                                (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                                (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                                (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                                (composition-param-Right-n __global_state)
                                                                                                                                                                                                                (composition-param-Right-p __global_state)
                                                                                                                                                                                                                (composition-param-Right-m __global_state)
                                                                                                                                                                                                                (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-11 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                                          (mk-return-Right-simgate-GBLG __global_state C))))))))))))))))))))))))))))))))))))))))))))
                                                                                                                    (let
                                                                                                                      (
                                                                                                                        (rin (__sample-rand-Right-Bits_n 7 (composition-rand-Right-7 __global_state))))
                                                                                                                      (let
                                                                                                                        (
                                                                                                                          (__global_state
                                                                                                                            (mk-composition-state-Right
                                                                                                                              (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                              (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                              (composition-pkgstate-Right-simgate __global_state)
                                                                                                                              (composition-pkgstate-Right-ev __global_state)
                                                                                                                              (composition-param-Right-zeron __global_state)
                                                                                                                              (composition-param-Right-zerom __global_state)
                                                                                                                              (composition-param-Right-n __global_state)
                                                                                                                              (composition-param-Right-p __global_state)
                                                                                                                              (composition-param-Right-m __global_state)
                                                                                                                              (composition-rand-Right-0 __global_state)
                                                                                                                              (composition-rand-Right-1 __global_state)
                                                                                                                              (composition-rand-Right-2 __global_state)
                                                                                                                              (composition-rand-Right-3 __global_state)
                                                                                                                              (composition-rand-Right-4 __global_state)
                                                                                                                              (composition-rand-Right-5 __global_state)
                                                                                                                              (composition-rand-Right-6 __global_state)
                                                                                                                              (+ 1 (composition-rand-Right-7 __global_state))
                                                                                                                              (composition-rand-Right-8 __global_state)
                                                                                                                              (composition-rand-Right-9 __global_state)
                                                                                                                              (composition-rand-Right-10 __global_state)
                                                                                                                              (composition-rand-Right-11 __global_state)
                                                                                                                              (composition-rand-Right-12 __global_state))))
                                                                                                                        (let
                                                                                                                          (
                                                                                                                            (rout (__sample-rand-Right-Bits_n 8 (composition-rand-Right-8 __global_state))))
                                                                                                                          (let
                                                                                                                            (
                                                                                                                              (__global_state
                                                                                                                                (mk-composition-state-Right
                                                                                                                                  (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                  (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                  (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                  (composition-pkgstate-Right-ev __global_state)
                                                                                                                                  (composition-param-Right-zeron __global_state)
                                                                                                                                  (composition-param-Right-zerom __global_state)
                                                                                                                                  (composition-param-Right-n __global_state)
                                                                                                                                  (composition-param-Right-p __global_state)
                                                                                                                                  (composition-param-Right-m __global_state)
                                                                                                                                  (composition-rand-Right-0 __global_state)
                                                                                                                                  (composition-rand-Right-1 __global_state)
                                                                                                                                  (composition-rand-Right-2 __global_state)
                                                                                                                                  (composition-rand-Right-3 __global_state)
                                                                                                                                  (composition-rand-Right-4 __global_state)
                                                                                                                                  (composition-rand-Right-5 __global_state)
                                                                                                                                  (composition-rand-Right-6 __global_state)
                                                                                                                                  (composition-rand-Right-7 __global_state)
                                                                                                                                  (+ 1 (composition-rand-Right-8 __global_state))
                                                                                                                                  (composition-rand-Right-9 __global_state)
                                                                                                                                  (composition-rand-Right-10 __global_state)
                                                                                                                                  (composition-rand-Right-11 __global_state)
                                                                                                                                  (composition-rand-Right-12 __global_state))))
                                                                                                                            (let
                                                                                                                              ((cin (__func-Right-encn kr kj rin)))
                                                                                                                              (let
                                                                                                                                ((cout (__func-Right-encm kl cin rout)))
                                                                                                                                (let
                                                                                                                                  ((C ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))))
                                                                                                                                  (let
                                                                                                                                    ((C (store C cout (mk-some true))))
                                                                                                                                    (let
                                                                                                                                      ((dl false))
                                                                                                                                      (let
                                                                                                                                        ((dr true))
                                                                                                                                        (let
                                                                                                                                          ((unwrap-7 (maybe-get (select Sl dl))))
                                                                                                                                          (let
                                                                                                                                            ((kl unwrap-7))
                                                                                                                                            (let
                                                                                                                                              ((unwrap-8 (maybe-get (select Sr dr))))
                                                                                                                                              (let
                                                                                                                                                ((kr unwrap-8))
                                                                                                                                                (let
                                                                                                                                                  ((kj (composition-param-Right-zeron __global_state)))
                                                                                                                                                  (ite
                                                                                                                                                    (and (or (not dl)) (or (not dr)))
                                                                                                                                                    (let
                                                                                                                                                      ((unwrap-9 (maybe-get (select Sj false))))
                                                                                                                                                      (let
                                                                                                                                                        ((kj unwrap-9))
                                                                                                                                                        (let
                                                                                                                                                          (
                                                                                                                                                            (rin (__sample-rand-Right-Bits_n 9 (composition-rand-Right-9 __global_state))))
                                                                                                                                                          (let
                                                                                                                                                            (
                                                                                                                                                              (__global_state
                                                                                                                                                                (mk-composition-state-Right
                                                                                                                                                                  (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                  (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                  (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                  (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                  (composition-param-Right-zeron __global_state)
                                                                                                                                                                  (composition-param-Right-zerom __global_state)
                                                                                                                                                                  (composition-param-Right-n __global_state)
                                                                                                                                                                  (composition-param-Right-p __global_state)
                                                                                                                                                                  (composition-param-Right-m __global_state)
                                                                                                                                                                  (composition-rand-Right-0 __global_state)
                                                                                                                                                                  (composition-rand-Right-1 __global_state)
                                                                                                                                                                  (composition-rand-Right-2 __global_state)
                                                                                                                                                                  (composition-rand-Right-3 __global_state)
                                                                                                                                                                  (composition-rand-Right-4 __global_state)
                                                                                                                                                                  (composition-rand-Right-5 __global_state)
                                                                                                                                                                  (composition-rand-Right-6 __global_state)
                                                                                                                                                                  (composition-rand-Right-7 __global_state)
                                                                                                                                                                  (composition-rand-Right-8 __global_state)
                                                                                                                                                                  (+ 1 (composition-rand-Right-9 __global_state))
                                                                                                                                                                  (composition-rand-Right-10 __global_state)
                                                                                                                                                                  (composition-rand-Right-11 __global_state)
                                                                                                                                                                  (composition-rand-Right-12 __global_state))))
                                                                                                                                                            (let
                                                                                                                                                              (
                                                                                                                                                                (rout
                                                                                                                                                                  (__sample-rand-Right-Bits_n 10 (composition-rand-Right-10 __global_state))))
                                                                                                                                                              (let
                                                                                                                                                                (
                                                                                                                                                                  (__global_state
                                                                                                                                                                    (mk-composition-state-Right
                                                                                                                                                                      (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                      (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                      (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                      (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                      (composition-param-Right-zeron __global_state)
                                                                                                                                                                      (composition-param-Right-zerom __global_state)
                                                                                                                                                                      (composition-param-Right-n __global_state)
                                                                                                                                                                      (composition-param-Right-p __global_state)
                                                                                                                                                                      (composition-param-Right-m __global_state)
                                                                                                                                                                      (composition-rand-Right-0 __global_state)
                                                                                                                                                                      (composition-rand-Right-1 __global_state)
                                                                                                                                                                      (composition-rand-Right-2 __global_state)
                                                                                                                                                                      (composition-rand-Right-3 __global_state)
                                                                                                                                                                      (composition-rand-Right-4 __global_state)
                                                                                                                                                                      (composition-rand-Right-5 __global_state)
                                                                                                                                                                      (composition-rand-Right-6 __global_state)
                                                                                                                                                                      (composition-rand-Right-7 __global_state)
                                                                                                                                                                      (composition-rand-Right-8 __global_state)
                                                                                                                                                                      (composition-rand-Right-9 __global_state)
                                                                                                                                                                      (+ 1 (composition-rand-Right-10 __global_state))
                                                                                                                                                                      (composition-rand-Right-11 __global_state)
                                                                                                                                                                      (composition-rand-Right-12 __global_state))))
                                                                                                                                                                (let
                                                                                                                                                                  ((cin (__func-Right-encn kr kj rin)))
                                                                                                                                                                  (let
                                                                                                                                                                    ((cout (__func-Right-encm kl cin rout)))
                                                                                                                                                                    (let
                                                                                                                                                                      ((C ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))))
                                                                                                                                                                      (let
                                                                                                                                                                        ((C (store C cout (mk-some true))))
                                                                                                                                                                        (let
                                                                                                                                                                          ((dl true))
                                                                                                                                                                          (let
                                                                                                                                                                            ((dr true))
                                                                                                                                                                            (let
                                                                                                                                                                              ((unwrap-10 (maybe-get (select Sl dl))))
                                                                                                                                                                              (let
                                                                                                                                                                                ((kl unwrap-10))
                                                                                                                                                                                (let
                                                                                                                                                                                  ((unwrap-11 (maybe-get (select Sr dr))))
                                                                                                                                                                                  (let
                                                                                                                                                                                    ((kr unwrap-11))
                                                                                                                                                                                    (let
                                                                                                                                                                                      ((kj (composition-param-Right-zeron __global_state)))
                                                                                                                                                                                      (ite
                                                                                                                                                                                        (and (or (not dl)) (or (not dr)))
                                                                                                                                                                                        (let
                                                                                                                                                                                          ((unwrap-12 (maybe-get (select Sj false))))
                                                                                                                                                                                          (let
                                                                                                                                                                                            ((kj unwrap-12))
                                                                                                                                                                                            (let
                                                                                                                                                                                              (
                                                                                                                                                                                                (rin
                                                                                                                                                                                                  (__sample-rand-Right-Bits_n 11 (composition-rand-Right-11 __global_state))))
                                                                                                                                                                                              (let
                                                                                                                                                                                                (
                                                                                                                                                                                                  (__global_state
                                                                                                                                                                                                    (mk-composition-state-Right
                                                                                                                                                                                                      (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                      (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                      (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                                                      (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                      (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                      (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                      (composition-param-Right-n __global_state)
                                                                                                                                                                                                      (composition-param-Right-p __global_state)
                                                                                                                                                                                                      (composition-param-Right-m __global_state)
                                                                                                                                                                                                      (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                      (+ 1 (composition-rand-Right-11 __global_state))
                                                                                                                                                                                                      (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                                (let
                                                                                                                                                                                                  (
                                                                                                                                                                                                    (rout
                                                                                                                                                                                                      (__sample-rand-Right-Bits_n 12 (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                                  (let
                                                                                                                                                                                                    (
                                                                                                                                                                                                      (__global_state
                                                                                                                                                                                                        (mk-composition-state-Right
                                                                                                                                                                                                          (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                          (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                          (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                                                          (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                          (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                          (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                          (composition-param-Right-n __global_state)
                                                                                                                                                                                                          (composition-param-Right-p __global_state)
                                                                                                                                                                                                          (composition-param-Right-m __global_state)
                                                                                                                                                                                                          (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                          (composition-rand-Right-11 __global_state)
                                                                                                                                                                                                          (+ 1 (composition-rand-Right-12 __global_state)))))
                                                                                                                                                                                                    (let
                                                                                                                                                                                                      ((cin (__func-Right-encn kr kj rin)))
                                                                                                                                                                                                      (let
                                                                                                                                                                                                        ((cout (__func-Right-encm kl cin rout)))
                                                                                                                                                                                                        (let
                                                                                                                                                                                                          ((C ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))))
                                                                                                                                                                                                          (let
                                                                                                                                                                                                            ((C (store C cout (mk-some true))))
                                                                                                                                                                                                            (let
                                                                                                                                                                                                              (
                                                                                                                                                                                                                (__global_state
                                                                                                                                                                                                                  (mk-composition-state-Right
                                                                                                                                                                                                                    (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                                    (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                                    __self_state
                                                                                                                                                                                                                    (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                                    (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                                    (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                                    (composition-param-Right-n __global_state)
                                                                                                                                                                                                                    (composition-param-Right-p __global_state)
                                                                                                                                                                                                                    (composition-param-Right-m __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-11 __global_state)
                                                                                                                                                                                                                    (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                                              (mk-return-Right-simgate-GBLG __global_state C))))))))))))
                                                                                                                                                                                        (let
                                                                                                                                                                                          (
                                                                                                                                                                                            (rin
                                                                                                                                                                                              (__sample-rand-Right-Bits_n 11 (composition-rand-Right-11 __global_state))))
                                                                                                                                                                                          (let
                                                                                                                                                                                            (
                                                                                                                                                                                              (__global_state
                                                                                                                                                                                                (mk-composition-state-Right
                                                                                                                                                                                                  (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                  (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                  (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                                                  (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                  (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                  (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                  (composition-param-Right-n __global_state)
                                                                                                                                                                                                  (composition-param-Right-p __global_state)
                                                                                                                                                                                                  (composition-param-Right-m __global_state)
                                                                                                                                                                                                  (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                  (+ 1 (composition-rand-Right-11 __global_state))
                                                                                                                                                                                                  (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                            (let
                                                                                                                                                                                              (
                                                                                                                                                                                                (rout
                                                                                                                                                                                                  (__sample-rand-Right-Bits_n 12 (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                              (let
                                                                                                                                                                                                (
                                                                                                                                                                                                  (__global_state
                                                                                                                                                                                                    (mk-composition-state-Right
                                                                                                                                                                                                      (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                      (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                      (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                                                      (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                      (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                      (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                      (composition-param-Right-n __global_state)
                                                                                                                                                                                                      (composition-param-Right-p __global_state)
                                                                                                                                                                                                      (composition-param-Right-m __global_state)
                                                                                                                                                                                                      (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-11 __global_state)
                                                                                                                                                                                                      (+ 1 (composition-rand-Right-12 __global_state)))))
                                                                                                                                                                                                (let
                                                                                                                                                                                                  ((cin (__func-Right-encn kr kj rin)))
                                                                                                                                                                                                  (let
                                                                                                                                                                                                    ((cout (__func-Right-encm kl cin rout)))
                                                                                                                                                                                                    (let
                                                                                                                                                                                                      ((C ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))))
                                                                                                                                                                                                      (let
                                                                                                                                                                                                        ((C (store C cout (mk-some true))))
                                                                                                                                                                                                        (let
                                                                                                                                                                                                          (
                                                                                                                                                                                                            (__global_state
                                                                                                                                                                                                              (mk-composition-state-Right
                                                                                                                                                                                                                (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                                (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                                __self_state
                                                                                                                                                                                                                (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                                (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                                (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                                (composition-param-Right-n __global_state)
                                                                                                                                                                                                                (composition-param-Right-p __global_state)
                                                                                                                                                                                                                (composition-param-Right-m __global_state)
                                                                                                                                                                                                                (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-11 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                                          (mk-return-Right-simgate-GBLG __global_state C))))))))))))))))))))))))))))
                                                                                                                                                    (let
                                                                                                                                                      (
                                                                                                                                                        (rin (__sample-rand-Right-Bits_n 9 (composition-rand-Right-9 __global_state))))
                                                                                                                                                      (let
                                                                                                                                                        (
                                                                                                                                                          (__global_state
                                                                                                                                                            (mk-composition-state-Right
                                                                                                                                                              (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                              (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                              (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                              (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                              (composition-param-Right-zeron __global_state)
                                                                                                                                                              (composition-param-Right-zerom __global_state)
                                                                                                                                                              (composition-param-Right-n __global_state)
                                                                                                                                                              (composition-param-Right-p __global_state)
                                                                                                                                                              (composition-param-Right-m __global_state)
                                                                                                                                                              (composition-rand-Right-0 __global_state)
                                                                                                                                                              (composition-rand-Right-1 __global_state)
                                                                                                                                                              (composition-rand-Right-2 __global_state)
                                                                                                                                                              (composition-rand-Right-3 __global_state)
                                                                                                                                                              (composition-rand-Right-4 __global_state)
                                                                                                                                                              (composition-rand-Right-5 __global_state)
                                                                                                                                                              (composition-rand-Right-6 __global_state)
                                                                                                                                                              (composition-rand-Right-7 __global_state)
                                                                                                                                                              (composition-rand-Right-8 __global_state)
                                                                                                                                                              (+ 1 (composition-rand-Right-9 __global_state))
                                                                                                                                                              (composition-rand-Right-10 __global_state)
                                                                                                                                                              (composition-rand-Right-11 __global_state)
                                                                                                                                                              (composition-rand-Right-12 __global_state))))
                                                                                                                                                        (let
                                                                                                                                                          (
                                                                                                                                                            (rout
                                                                                                                                                              (__sample-rand-Right-Bits_n 10 (composition-rand-Right-10 __global_state))))
                                                                                                                                                          (let
                                                                                                                                                            (
                                                                                                                                                              (__global_state
                                                                                                                                                                (mk-composition-state-Right
                                                                                                                                                                  (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                  (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                  (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                  (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                  (composition-param-Right-zeron __global_state)
                                                                                                                                                                  (composition-param-Right-zerom __global_state)
                                                                                                                                                                  (composition-param-Right-n __global_state)
                                                                                                                                                                  (composition-param-Right-p __global_state)
                                                                                                                                                                  (composition-param-Right-m __global_state)
                                                                                                                                                                  (composition-rand-Right-0 __global_state)
                                                                                                                                                                  (composition-rand-Right-1 __global_state)
                                                                                                                                                                  (composition-rand-Right-2 __global_state)
                                                                                                                                                                  (composition-rand-Right-3 __global_state)
                                                                                                                                                                  (composition-rand-Right-4 __global_state)
                                                                                                                                                                  (composition-rand-Right-5 __global_state)
                                                                                                                                                                  (composition-rand-Right-6 __global_state)
                                                                                                                                                                  (composition-rand-Right-7 __global_state)
                                                                                                                                                                  (composition-rand-Right-8 __global_state)
                                                                                                                                                                  (composition-rand-Right-9 __global_state)
                                                                                                                                                                  (+ 1 (composition-rand-Right-10 __global_state))
                                                                                                                                                                  (composition-rand-Right-11 __global_state)
                                                                                                                                                                  (composition-rand-Right-12 __global_state))))
                                                                                                                                                            (let
                                                                                                                                                              ((cin (__func-Right-encn kr kj rin)))
                                                                                                                                                              (let
                                                                                                                                                                ((cout (__func-Right-encm kl cin rout)))
                                                                                                                                                                (let
                                                                                                                                                                  ((C ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))))
                                                                                                                                                                  (let
                                                                                                                                                                    ((C (store C cout (mk-some true))))
                                                                                                                                                                    (let
                                                                                                                                                                      ((dl true))
                                                                                                                                                                      (let
                                                                                                                                                                        ((dr true))
                                                                                                                                                                        (let
                                                                                                                                                                          ((unwrap-10 (maybe-get (select Sl dl))))
                                                                                                                                                                          (let
                                                                                                                                                                            ((kl unwrap-10))
                                                                                                                                                                            (let
                                                                                                                                                                              ((unwrap-11 (maybe-get (select Sr dr))))
                                                                                                                                                                              (let
                                                                                                                                                                                ((kr unwrap-11))
                                                                                                                                                                                (let
                                                                                                                                                                                  ((kj (composition-param-Right-zeron __global_state)))
                                                                                                                                                                                  (ite
                                                                                                                                                                                    (and (or (not dl)) (or (not dr)))
                                                                                                                                                                                    (let
                                                                                                                                                                                      ((unwrap-12 (maybe-get (select Sj false))))
                                                                                                                                                                                      (let
                                                                                                                                                                                        ((kj unwrap-12))
                                                                                                                                                                                        (let
                                                                                                                                                                                          (
                                                                                                                                                                                            (rin
                                                                                                                                                                                              (__sample-rand-Right-Bits_n 11 (composition-rand-Right-11 __global_state))))
                                                                                                                                                                                          (let
                                                                                                                                                                                            (
                                                                                                                                                                                              (__global_state
                                                                                                                                                                                                (mk-composition-state-Right
                                                                                                                                                                                                  (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                  (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                  (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                                                  (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                  (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                  (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                  (composition-param-Right-n __global_state)
                                                                                                                                                                                                  (composition-param-Right-p __global_state)
                                                                                                                                                                                                  (composition-param-Right-m __global_state)
                                                                                                                                                                                                  (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                  (+ 1 (composition-rand-Right-11 __global_state))
                                                                                                                                                                                                  (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                            (let
                                                                                                                                                                                              (
                                                                                                                                                                                                (rout
                                                                                                                                                                                                  (__sample-rand-Right-Bits_n 12 (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                              (let
                                                                                                                                                                                                (
                                                                                                                                                                                                  (__global_state
                                                                                                                                                                                                    (mk-composition-state-Right
                                                                                                                                                                                                      (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                      (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                      (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                                                      (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                      (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                      (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                      (composition-param-Right-n __global_state)
                                                                                                                                                                                                      (composition-param-Right-p __global_state)
                                                                                                                                                                                                      (composition-param-Right-m __global_state)
                                                                                                                                                                                                      (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                      (composition-rand-Right-11 __global_state)
                                                                                                                                                                                                      (+ 1 (composition-rand-Right-12 __global_state)))))
                                                                                                                                                                                                (let
                                                                                                                                                                                                  ((cin (__func-Right-encn kr kj rin)))
                                                                                                                                                                                                  (let
                                                                                                                                                                                                    ((cout (__func-Right-encm kl cin rout)))
                                                                                                                                                                                                    (let
                                                                                                                                                                                                      ((C ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))))
                                                                                                                                                                                                      (let
                                                                                                                                                                                                        ((C (store C cout (mk-some true))))
                                                                                                                                                                                                        (let
                                                                                                                                                                                                          (
                                                                                                                                                                                                            (__global_state
                                                                                                                                                                                                              (mk-composition-state-Right
                                                                                                                                                                                                                (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                                (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                                __self_state
                                                                                                                                                                                                                (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                                (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                                (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                                (composition-param-Right-n __global_state)
                                                                                                                                                                                                                (composition-param-Right-p __global_state)
                                                                                                                                                                                                                (composition-param-Right-m __global_state)
                                                                                                                                                                                                                (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-11 __global_state)
                                                                                                                                                                                                                (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                                          (mk-return-Right-simgate-GBLG __global_state C))))))))))))
                                                                                                                                                                                    (let
                                                                                                                                                                                      (
                                                                                                                                                                                        (rin
                                                                                                                                                                                          (__sample-rand-Right-Bits_n 11 (composition-rand-Right-11 __global_state))))
                                                                                                                                                                                      (let
                                                                                                                                                                                        (
                                                                                                                                                                                          (__global_state
                                                                                                                                                                                            (mk-composition-state-Right
                                                                                                                                                                                              (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                              (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                              (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                                              (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                              (composition-param-Right-zeron __global_state)
                                                                                                                                                                                              (composition-param-Right-zerom __global_state)
                                                                                                                                                                                              (composition-param-Right-n __global_state)
                                                                                                                                                                                              (composition-param-Right-p __global_state)
                                                                                                                                                                                              (composition-param-Right-m __global_state)
                                                                                                                                                                                              (composition-rand-Right-0 __global_state)
                                                                                                                                                                                              (composition-rand-Right-1 __global_state)
                                                                                                                                                                                              (composition-rand-Right-2 __global_state)
                                                                                                                                                                                              (composition-rand-Right-3 __global_state)
                                                                                                                                                                                              (composition-rand-Right-4 __global_state)
                                                                                                                                                                                              (composition-rand-Right-5 __global_state)
                                                                                                                                                                                              (composition-rand-Right-6 __global_state)
                                                                                                                                                                                              (composition-rand-Right-7 __global_state)
                                                                                                                                                                                              (composition-rand-Right-8 __global_state)
                                                                                                                                                                                              (composition-rand-Right-9 __global_state)
                                                                                                                                                                                              (composition-rand-Right-10 __global_state)
                                                                                                                                                                                              (+ 1 (composition-rand-Right-11 __global_state))
                                                                                                                                                                                              (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                        (let
                                                                                                                                                                                          (
                                                                                                                                                                                            (rout
                                                                                                                                                                                              (__sample-rand-Right-Bits_n 12 (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                          (let
                                                                                                                                                                                            (
                                                                                                                                                                                              (__global_state
                                                                                                                                                                                                (mk-composition-state-Right
                                                                                                                                                                                                  (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                  (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                  (composition-pkgstate-Right-simgate __global_state)
                                                                                                                                                                                                  (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                  (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                  (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                  (composition-param-Right-n __global_state)
                                                                                                                                                                                                  (composition-param-Right-p __global_state)
                                                                                                                                                                                                  (composition-param-Right-m __global_state)
                                                                                                                                                                                                  (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                  (composition-rand-Right-11 __global_state)
                                                                                                                                                                                                  (+ 1 (composition-rand-Right-12 __global_state)))))
                                                                                                                                                                                            (let
                                                                                                                                                                                              ((cin (__func-Right-encn kr kj rin)))
                                                                                                                                                                                              (let
                                                                                                                                                                                                ((cout (__func-Right-encm kl cin rout)))
                                                                                                                                                                                                (let
                                                                                                                                                                                                  ((C ((as const (Array Bits_p (Maybe Bool))) (as mk-none (Maybe Bool)))))
                                                                                                                                                                                                  (let
                                                                                                                                                                                                    ((C (store C cout (mk-some true))))
                                                                                                                                                                                                    (let
                                                                                                                                                                                                      (
                                                                                                                                                                                                        (__global_state
                                                                                                                                                                                                          (mk-composition-state-Right
                                                                                                                                                                                                            (composition-pkgstate-Right-keys_top __global_state)
                                                                                                                                                                                                            (composition-pkgstate-Right-keys_bottom __global_state)
                                                                                                                                                                                                            __self_state
                                                                                                                                                                                                            (composition-pkgstate-Right-ev __global_state)
                                                                                                                                                                                                            (composition-param-Right-zeron __global_state)
                                                                                                                                                                                                            (composition-param-Right-zerom __global_state)
                                                                                                                                                                                                            (composition-param-Right-n __global_state)
                                                                                                                                                                                                            (composition-param-Right-p __global_state)
                                                                                                                                                                                                            (composition-param-Right-m __global_state)
                                                                                                                                                                                                            (composition-rand-Right-0 __global_state)
                                                                                                                                                                                                            (composition-rand-Right-1 __global_state)
                                                                                                                                                                                                            (composition-rand-Right-2 __global_state)
                                                                                                                                                                                                            (composition-rand-Right-3 __global_state)
                                                                                                                                                                                                            (composition-rand-Right-4 __global_state)
                                                                                                                                                                                                            (composition-rand-Right-5 __global_state)
                                                                                                                                                                                                            (composition-rand-Right-6 __global_state)
                                                                                                                                                                                                            (composition-rand-Right-7 __global_state)
                                                                                                                                                                                                            (composition-rand-Right-8 __global_state)
                                                                                                                                                                                                            (composition-rand-Right-9 __global_state)
                                                                                                                                                                                                            (composition-rand-Right-10 __global_state)
                                                                                                                                                                                                            (composition-rand-Right-11 __global_state)
                                                                                                                                                                                                            (composition-rand-Right-12 __global_state))))
                                                                                                                                                                                                      (mk-return-Right-simgate-GBLG __global_state C))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
; Goal:
; Use equality on KEYS packages as invariant
; prove that on same inputs, all oracles give same output

; possible input for all (and sufficient for GETKEYSIN/GETKEYSOUT):
(declare-const handle Int)

; possible input for SETBIT
(declare-const bit Bool)

; possible input for GBLG     oracle GBLG(h: Integer, l: Integer, r: Integer, op: fn Bool,Bool -> Bool, j: Integer) -> Table(Bits(p),Bool) {
(declare-const l Int)
(declare-const r Int)
(declare-const op (Array (Tuple2 Bool Bool) (Maybe Bool)))
(declare-const j Int)


; possible state
(declare-const state-left-old CompositionState-Left)
(declare-const state-right-old CompositionState-Right)
(declare-const state-left-new CompositionState-Left)
(declare-const state-right-new CompositionState-Right)

; return value - type depends on oracle call; only GBLG is interesting, actually.
(declare-const return-left Return_Left_gate_GBLG)
(declare-const return-right Return_Right_simgate_GBLG)
(declare-const is-abort-left Bool)
(declare-const is-abort-right Bool)
(declare-const value-left (Array Bits_p (Maybe Bool)))
(declare-const value-right (Array Bits_p (Maybe Bool)))

; sampled value Z and associated values
(declare-const Z-left  (Array Bool (Maybe Bits_n)))
(declare-const Z-right (Array Bool (Maybe Bits_n)))
(declare-const ctr-r-left Int)
(declare-const ctr-r-right Int)
(declare-const ctr-rr-left Int)
(declare-const ctr-rr-right Int)
(declare-const r-left Bits_n)
(declare-const r-right Bits_n)
(declare-const rr-left Bits_n)
(declare-const rr-right Bits_n)



; composition-rand-Right-3 global-old-composition-state - this is the counter
; Die counter sind zufällig die gleichen
; pre-condition composition-rand-Left-3 old-state-l = composition-rand-Right-3 old-state-r 
; pre-condition composition-rand-Left-4 old-state-l = composition-rand-Right-4 old-state-r ;
;   __sample-rand-Left-Bits_n 3 composition-rand-Left-3 global-old-composition-state
; = __sample-rand-Right-Bits_n 3 composition-rand-Right-3 global-old-composition-state
;   __sample-rand-Left-Bits_n 3 composition-rand-Left-3 global-old-composition-state
; = __sample-rand-Right-Bits_n 3 composition-rand-Right-3 global-old-composition-state
;   __sample-rand-Right-Bits_n (composition-rand-Left-3 global-old-composition-state)



(assert (and  ;assignment of return (value,state)
              (= return-left      (oracle-Left-gate-GBLG state-left-old handle l r op j))
              (= return-right     (oracle-Right-simgate-GBLG state-right-old handle l r op j))

              ;assignment of return values
              (= value-left       (return-Left-gate-GBLG-value return-left))
              (= value-right      (return-Right-simgate-GBLG-value return-right))

              ;assignment of abort values
              (= is-abort-left    (= mk-abort-Left-gate-GBLG return-left))
              (= is-abort-right   (= mk-abort-Right-simgate-GBLG return-right))

              ;assignment of return state
              (= state-left-new   (return-Left-gate-GBLG-state return-left))
              (= state-right-new  (return-Right-simgate-GBLG-state return-right))

              ;assignment of the ctr of the sample instructions for the lower Key package
              (= ctr-r-left   (composition-rand-Left-3  state-left-old))
              (= ctr-r-right  (composition-rand-Right-3 state-right-old))
              (= ctr-rr-left  (composition-rand-Left-4  state-left-old))
              (= ctr-rr-right (composition-rand-Right-4 state-right-old))

              ;assignment of the sampled values for the lower Key package
              (= r-left   (__sample-rand-Left-Bits_n 3 ctr-r-left))
              (= r-right  (__sample-rand-Right-Bits_n 3 ctr-r-right))
              (= rr-left  (__sample-rand-Left-Bits_n 4 ctr-rr-left))
              (= rr-right (__sample-rand-Right-Bits_n 4 ctr-rr-left))

              ;assignment of the sampled values for the lower Key package as a table
              (=  r-left  (maybe-get (select Z-left    true)))
              (= rr-left  (maybe-get  (select Z-left  false)))
              (= r-right  (maybe-get  (select Z-right  true)))
              (= rr-right (maybe-get (select Z-right  false)))

              ;equality of ctr/values of the sample instructions for the lower Key package
              (= ctr-r-left ctr-r-right)
              (= ctr-rr-left ctr-rr-right)
              (= r-left r-right)
              (= rr-left rr-right)


))









; The 2 top key packages should have the same state on the left and the right.
(define-fun key-top-lr-eq ((left CompositionState-Left) (right CompositionState-Right)) Bool
  (forall ((h Int)) (=  (select (state-Left-keys_top-T (composition-pkgstate-Left-keys_top left))
                                h)
                        (select (state-Right-keys_top-T (composition-pkgstate-Right-keys_top right))
                                h))))

; Left: The state of the top key package does not change when GBLG is called
(define-fun key-top-ll-eq ((old CompositionState-Left) (new CompositionState-Left)) Bool
  (forall ((h Int)) (=  (select (state-Left-keys_top-T (composition-pkgstate-Left-keys_top old))
                                h)
                        (select (state-Left-keys_top-T (composition-pkgstate-Left-keys_top new))
                                h))))

; Right: The state of the top key package does not change when GBLG is called
(define-fun key-top-rr-eq ((old CompositionState-Right) (new CompositionState-Right)) Bool
  (forall ((h Int)) (=  (select (state-Right-keys_top-T (composition-pkgstate-Right-keys_top old))
                                h)
                        (select (state-Right-keys_top-T (composition-pkgstate-Right-keys_top new))
                                h))))

; Left: The state of the bottom key package is mostly the same as before except at the point h j r op that was written to
(define-fun key-bottom-l-mostly-eq ((old CompositionState-Left) (new CompositionState-Left) 
                                    (h Int) (l Int) (r Int) (op (Array (Tuple2 Bool Bool) (Maybe Bool)))) Bool
  (forall ((hh Int))  (or (= h hh)
                                      (=  (select (state-Left-keys_bottom-T (composition-pkgstate-Left-keys_bottom new))
                                                  hh)
                                          (select (state-Left-keys_bottom-T (composition-pkgstate-Left-keys_bottom old))
                                                  hh)))))


; The state of the bottom key package on the right is mostly the same as before except at the point h that was written to
(define-fun key-bottom-r-mostly-eq ((old CompositionState-Right) (new CompositionState-Right) 
                                    (h Int) (l Int) (r Int) (op (Array (Tuple2 Bool Bool) (Maybe Bool)))) Bool
  (forall ((hh Int))  (or (= h hh)
                                      (=  (select (state-Right-keys_bottom-T (composition-pkgstate-Right-keys_bottom new))
                                                  hh)
                                          (select (state-Right-keys_bottom-T (composition-pkgstate-Right-keys_bottom old))
                                                  hh)))))

; Right: The state of the bottom key package at position h is equal to what was sampled (or was defined before).
(define-fun key-bottom-r-ok-after-call ((old CompositionState-Right) (new CompositionState-Right) (h Int) (l Int) (r Int) (op (Array (Tuple2 Bool Bool) (Maybe Bool)))) Bool 
  (or
  (=  (select (state-Right-keys_bottom-T (composition-pkgstate-Right-keys_bottom new))
                                                  h)
                                          (select (state-Right-keys_bottom-T (composition-pkgstate-Right-keys_bottom old))
                                                  h))
  (=      (maybe-get (select  (state-Right-keys_bottom-T (composition-pkgstate-Right-keys_bottom new))
                              h))
                              ; put randomness sampling here XXX
                              ; if it was none before, then it is equal to sample now
          Z-right)))

; The state of the bottom key package on the left at position h is equal to what was sampled (or was defined before)).
(define-fun key-bottom-l-ok-after-call ((old CompositionState-Left) (new CompositionState-Left) (h Int) (l Int) (r Int) (op (Array (Tuple2 Bool Bool) (Maybe Bool)))) Bool 
  (or
  (=  (select (state-Left-keys_bottom-T (composition-pkgstate-Left-keys_bottom new))
                                                  h)
                                          (select (state-Left-keys_bottom-T (composition-pkgstate-Left-keys_bottom old))
                                                  h))                              ; put randomness sampling here
                              ; if it was none before, then it is equal to sample now
  (=  (maybe-get(select (state-Left-keys_bottom-T (composition-pkgstate-Left-keys_bottom new))
                                                  h))
                              
      Z-left)))

; should this really use the old state?? Not here
(define-fun post-condition ((left CompositionState-Left) (right CompositionState-Right) (h Int) (l Int) (r Int) (op (Array (Tuple2 Bool Bool) (Maybe Bool)))) Bool
  (forall ((h Int)) (=  (select (state-Left-keys_top-T (composition-pkgstate-Left-keys_top left))
                                h)
                        (select (state-Right-keys_top-T (composition-pkgstate-Right-keys_top  right))
                                h))))


(declare-const precondition-holds Bool)
(assert (= precondition-holds (and  (not is-abort-right)
                                    (not is-abort-left)
                                    ;(key-bottom-ok state-right-old)
                                    (key-top-lr-eq state-left-old state-right-old))))

;; This is just to verify that the current state is satisfiable. It definitely should be.
(check-sat)

(push 1)
;;; prove right bottom key mostly equal lemma
(assert (and  precondition-holds
              (not
                ;; proved statement starts here
                (key-bottom-r-mostly-eq state-right-old state-right-new handle l r op))))
(check-sat)
(pop 1)

(push 1)
;;; prove right bottom keys wellformed after call lemma
(assert (and  precondition-holds
              ;; lemmata start here
              (not (key-bottom-r-ok-after-call state-right-old state-right-new handle l r op))))
(check-sat)
(pop 1)

(push 1)
;;; prove right bottom key mostly equal lemma
(assert (and  precondition-holds
              (not
                ;; proved statement starts here
                (key-bottom-l-mostly-eq state-left-old state-left-new handle l r op))))
(check-sat)
(pop 1)

(push 1)
;;; prove right bottom keys wellformed after call lemma
(assert (and  precondition-holds
              ;; lemmata start here
              (not (key-bottom-l-ok-after-call state-left-old state-left-new handle l r op))))
(check-sat)
(pop 1)


(push 1)
;; prove left-left lemma
(assert (and  precondition-holds
              (not
                ;; proved statement starts here
                (key-top-ll-eq state-left-old state-left-new))))
(check-sat)
(pop 1)
;
;; prove right-right lemma
(push 1)
(assert (and  precondition-holds
              (not
                ;; proved statement starts here
                (key-top-rr-eq state-right-old state-right-new))))
(check-sat)
(pop 1)



(push 1)
; prove left-right lemma
(assert (and    precondition-holds
                ;; lemmata start here
                (key-top-rr-eq state-right-old state-right-new)
                (key-top-ll-eq state-left-old state-left-new)
                (not
                    ;; proved statement starts here
                    (key-top-lr-eq state-left-new state-right-new))))
(check-sat)
(pop 1)


;; check that the post-condition follows
(push 1)
(assert (and    ;precondition-holds
                ;;; lemmata start here
                (key-top-ll-eq state-left-old state-left-new)
                (key-top-rr-eq state-right-old state-right-new)
                (key-top-lr-eq state-left-new state-right-new)
                (key-bottom-l-mostly-eq state-left-old state-left-new handle l r op)
                (key-bottom-r-mostly-eq state-right-old state-right-new handle l r op)
                (key-bottom-l-ok-after-call state-left-old state-left-new handle l r op)
                (key-bottom-r-ok-after-call state-right-old state-right-new handle l r op)
                (or
                ;one of the post-conditions fail
                    (not (post-condition state-left-new state-right-new handle l r op))
                    (not (key-bottom-l-ok state-left-new))
                    (not (key-bottom-r-ok state-right-new))                    
                    )))
(check-sat)
(pop 1)

; this should not be a problem.
; the fact that this is a problem might be informative.
(push 1)
;(assert (key-tables-empty state-right-old))

;(assert (and  (right-key-bottom-set-implies-top-set state-right-old)))
              ;(right-key-top-set-implies-bottom-set state-right-old)))
      
(assert (key-bottom-r-ok state-right-old))
(check-sat)
;(get-model)
(pop 1)

(push 1)
(assert (key-bottom-l-ok state-left-old))
(check-sat)
;(get-model)
(pop 1)

;; this also shouldn't be a problem, but probably t his problem is just caused by the above problem.
(push 1)
;; check that there is a valid assignment for the precondition
(assert precondition-holds)
(check-sat)
;(get-model)
(pop 1)