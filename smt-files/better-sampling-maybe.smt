(declare-datatypes ((Maybe 1)) ((par (T) ((mk-some (maybe-get T)) (mk-none)))))
(declare-sort Bits_n 0)
(declare-fun f (Bits_n Bits_n) Bits_n)


; ModPRFTableGame
(declare-datatype
  State_ModPRFTableGame___randomness
  (
    (mk-state-ModPRFTableGame-__randomness
      (state-ModPRFTableGame-__randomness-ctr Int))))
(declare-fun __sample-rand-ModPRFTableGame (Int) Bits_n)
(declare-datatype State_ModPRFTableGame_prf ((mk-state-ModPRFTableGame-prf)))
(declare-datatype
  State_ModPRFTableGame_key_top
  (
    (mk-state-ModPRFTableGame-key_top
      (state-ModPRFTableGame-key_top-k (Array Int (Maybe Bits_n))))))
(declare-datatype
  State_ModPRFTableGame_key_bottom
  (
    (mk-state-ModPRFTableGame-key_bottom
      (state-ModPRFTableGame-key_bottom-k (Array Int (Maybe Bits_n))))))
(declare-datatype
  CompositionState-ModPRFTableGame
  (
    (mk-composition-state-ModPRFTableGame
      (composition-state-ModPRFTableGame-__randomness
        State_ModPRFTableGame___randomness)
      (composition-state-ModPRFTableGame-prf State_ModPRFTableGame_prf)
      (composition-state-ModPRFTableGame-key_top State_ModPRFTableGame_key_top)
      (composition-state-ModPRFTableGame-key_bottom State_ModPRFTableGame_key_bottom))))
(declare-datatype
  Return_ModPRFTableGame_prf_Eval
  (
    (mk-return-ModPRFTableGame-prf-Eval
      (return-ModPRFTableGame-prf-Eval-state CompositionState-ModPRFTableGame)
      (return-ModPRFTableGame-prf-Eval-value Bits_n))
    (mk-abort-ModPRFTableGame-prf-Eval)))
(declare-datatype
  Return_ModPRFTableGame_key_top_Get
  (
    (mk-return-ModPRFTableGame-key_top-Get
      (return-ModPRFTableGame-key_top-Get-state CompositionState-ModPRFTableGame)
      (return-ModPRFTableGame-key_top-Get-value Bits_n))
    (mk-abort-ModPRFTableGame-key_top-Get)))
(declare-datatype
  Return_ModPRFTableGame_key_top_Set
  (
    (mk-return-ModPRFTableGame-key_top-Set
      (return-ModPRFTableGame-key_top-Set-state CompositionState-ModPRFTableGame))
    (mk-abort-ModPRFTableGame-key_top-Set)))
(declare-datatype
  Return_ModPRFTableGame_key_bottom_Get
  (
    (mk-return-ModPRFTableGame-key_bottom-Get
      (return-ModPRFTableGame-key_bottom-Get-state CompositionState-ModPRFTableGame)
      (return-ModPRFTableGame-key_bottom-Get-value Bits_n))
    (mk-abort-ModPRFTableGame-key_bottom-Get)))
(declare-datatype
  Return_ModPRFTableGame_key_bottom_Set
  (
    (mk-return-ModPRFTableGame-key_bottom-Set
      (return-ModPRFTableGame-key_bottom-Set-state CompositionState-ModPRFTableGame))
    (mk-abort-ModPRFTableGame-key_bottom-Set))); Composition of ModPRFTableGame
(define-fun
  oracle-ModPRFTableGame-key_top-Get
  ((__global_state CompositionState-ModPRFTableGame) (i Int))
  Return_ModPRFTableGame_key_top_Get
  (let
    ((__self_state (composition-state-ModPRFTableGame-key_top __global_state)))
    (ite
      (=
        (select (state-ModPRFTableGame-key_top-k __self_state) i)
        (as mk-none (Maybe Bits_n)))
      (let
        (
          (k_new
            (__sample-rand-ModPRFTableGame
              (state-ModPRFTableGame-__randomness-ctr
                (composition-state-ModPRFTableGame-__randomness __global_state)))))
        (let
          (
            (__global_state
              (mk-composition-state-ModPRFTableGame
                (mk-state-ModPRFTableGame-__randomness
                  (+
                    1
                    (state-ModPRFTableGame-__randomness-ctr
                      (composition-state-ModPRFTableGame-__randomness __global_state))))
                (composition-state-ModPRFTableGame-prf __global_state)
                (composition-state-ModPRFTableGame-key_top __global_state)
                (composition-state-ModPRFTableGame-key_bottom __global_state))))
          (let
            (
              (__self_state
                (mk-state-ModPRFTableGame-key_top
                  (store (state-ModPRFTableGame-key_top-k __self_state) i (mk-some k_new)))))
            (ite
              (
                (_ is (mk-none () (Maybe Bits_n)))
                (select (state-ModPRFTableGame-key_top-k __self_state) i))
              mk-abort-ModPRFTableGame-key_top-Get
              (let
                ((k_ret (maybe-get (select (state-ModPRFTableGame-key_top-k __self_state) i))))
                (let
                  (
                    (__global_state
                      (mk-composition-state-ModPRFTableGame
                        (composition-state-ModPRFTableGame-__randomness __global_state)
                        (composition-state-ModPRFTableGame-prf __global_state)
                        __self_state
                        (composition-state-ModPRFTableGame-key_bottom __global_state))))
                  (mk-return-ModPRFTableGame-key_top-Get __global_state k_ret)))))))
      (ite
        (
          (_ is (mk-none () (Maybe Bits_n)))
          (select (state-ModPRFTableGame-key_top-k __self_state) i))
        mk-abort-ModPRFTableGame-key_top-Get
        (let
          ((k_ret (maybe-get (select (state-ModPRFTableGame-key_top-k __self_state) i))))
          (let
            (
              (__global_state
                (mk-composition-state-ModPRFTableGame
                  (composition-state-ModPRFTableGame-__randomness __global_state)
                  (composition-state-ModPRFTableGame-prf __global_state)
                  __self_state
                  (composition-state-ModPRFTableGame-key_bottom __global_state))))
            (mk-return-ModPRFTableGame-key_top-Get __global_state k_ret)))))))
(define-fun
  oracle-ModPRFTableGame-key_top-Set
  ((__global_state CompositionState-ModPRFTableGame) (i Int) (k_new Bits_n))
  Return_ModPRFTableGame_key_top_Set
  (let
    ((__self_state (composition-state-ModPRFTableGame-key_top __global_state)))
    (ite
      (not
        (=
          (select (state-ModPRFTableGame-key_top-k __self_state) i)
          (as mk-none (Maybe Bits_n))))
      (let
        (
          (__self_state
            (mk-state-ModPRFTableGame-key_top
              (store (state-ModPRFTableGame-key_top-k __self_state) i (mk-some k_new)))))
        (mk-return-ModPRFTableGame-key_top-Set __global_state))
      mk-abort-ModPRFTableGame-key_top-Set)))
(define-fun
  oracle-ModPRFTableGame-key_bottom-Get
  ((__global_state CompositionState-ModPRFTableGame) (i Int))
  Return_ModPRFTableGame_key_bottom_Get
  (let
    ((__self_state (composition-state-ModPRFTableGame-key_bottom __global_state)))
    (ite
      (=
        (select (state-ModPRFTableGame-key_bottom-k __self_state) i)
        (as mk-none (Maybe Bits_n)))
      (let
        (
          (k_new
            (__sample-rand-ModPRFTableGame
              (state-ModPRFTableGame-__randomness-ctr
                (composition-state-ModPRFTableGame-__randomness __global_state)))))
        (let
          (
            (__global_state
              (mk-composition-state-ModPRFTableGame
                (mk-state-ModPRFTableGame-__randomness
                  (+
                    1
                    (state-ModPRFTableGame-__randomness-ctr
                      (composition-state-ModPRFTableGame-__randomness __global_state))))
                (composition-state-ModPRFTableGame-prf __global_state)
                (composition-state-ModPRFTableGame-key_top __global_state)
                (composition-state-ModPRFTableGame-key_bottom __global_state))))
          (let
            (
              (__self_state
                (mk-state-ModPRFTableGame-key_bottom
                  (store (state-ModPRFTableGame-key_bottom-k __self_state) i (mk-some k_new)))))
            (ite
              (
                (_ is (mk-none () (Maybe Bits_n)))
                (select (state-ModPRFTableGame-key_bottom-k __self_state) i))
              mk-abort-ModPRFTableGame-key_bottom-Get
              (let
                (
                  (k_ret
                    (maybe-get (select (state-ModPRFTableGame-key_bottom-k __self_state) i))))
                (let
                  (
                    (__global_state
                      (mk-composition-state-ModPRFTableGame
                        (composition-state-ModPRFTableGame-__randomness __global_state)
                        (composition-state-ModPRFTableGame-prf __global_state)
                        (composition-state-ModPRFTableGame-key_top __global_state)
                        __self_state)))
                  (mk-return-ModPRFTableGame-key_bottom-Get __global_state k_ret)))))))
      (ite
        (
          (_ is (mk-none () (Maybe Bits_n)))
          (select (state-ModPRFTableGame-key_bottom-k __self_state) i))
        mk-abort-ModPRFTableGame-key_bottom-Get
        (let
          (
            (k_ret
              (maybe-get (select (state-ModPRFTableGame-key_bottom-k __self_state) i))))
          (let
            (
              (__global_state
                (mk-composition-state-ModPRFTableGame
                  (composition-state-ModPRFTableGame-__randomness __global_state)
                  (composition-state-ModPRFTableGame-prf __global_state)
                  (composition-state-ModPRFTableGame-key_top __global_state)
                  __self_state)))
            (mk-return-ModPRFTableGame-key_bottom-Get __global_state k_ret)))))))
(define-fun
  oracle-ModPRFTableGame-key_bottom-Set
  ((__global_state CompositionState-ModPRFTableGame) (i Int) (k_new Bits_n))
  Return_ModPRFTableGame_key_bottom_Set
  (let
    ((__self_state (composition-state-ModPRFTableGame-key_bottom __global_state)))
    (ite
      (not
        (=
          (select (state-ModPRFTableGame-key_bottom-k __self_state) i)
          (as mk-none (Maybe Bits_n))))
      (let
        (
          (__self_state
            (mk-state-ModPRFTableGame-key_bottom
              (store (state-ModPRFTableGame-key_bottom-k __self_state) i (mk-some k_new)))))
        (mk-return-ModPRFTableGame-key_bottom-Set __global_state))
      mk-abort-ModPRFTableGame-key_bottom-Set)))
(define-fun
  oracle-ModPRFTableGame-prf-Eval
  ((__global_state CompositionState-ModPRFTableGame) (i Int) (msg Bits_n))
  Return_ModPRFTableGame_prf_Eval
  (let
    ((__self_state (composition-state-ModPRFTableGame-prf __global_state)))
    (let
      ((__ret (oracle-ModPRFTableGame-key_top-Get __global_state i)))
      (ite
        ((_ is mk-abort-ModPRFTableGame-key_top-Get) __ret)
        mk-abort-ModPRFTableGame-prf-Eval
        (let
          (
            (__global_state (return-ModPRFTableGame-key_top-Get-state __ret))
            (k (return-ModPRFTableGame-key_top-Get-value __ret)))
          (let
            ((out (f k msg)))
            (let
              (
                (__global_state
                  (mk-composition-state-ModPRFTableGame
                    (composition-state-ModPRFTableGame-__randomness __global_state)
                    __self_state
                    (composition-state-ModPRFTableGame-key_top __global_state)
                    (composition-state-ModPRFTableGame-key_bottom __global_state))))
              (mk-return-ModPRFTableGame-prf-Eval __global_state out)))))))); ModPRFGame
(declare-datatype
  State_ModPRFGame___randomness
  ((mk-state-ModPRFGame-__randomness (state-ModPRFGame-__randomness-ctr Int))))
(declare-fun __sample-rand-ModPRFGame (Int) Bits_n)
(declare-datatype State_ModPRFGame_prf ((mk-state-ModPRFGame-prf)))
(declare-datatype
  State_ModPRFGame_key_top
  ((mk-state-ModPRFGame-key_top (state-ModPRFGame-key_top-k (Maybe Bits_n)))))
(declare-datatype
  State_ModPRFGame_key_bottom
  (
    (mk-state-ModPRFGame-key_bottom (state-ModPRFGame-key_bottom-k (Maybe Bits_n)))))
(declare-datatype
  CompositionState-ModPRFGame
  (
    (mk-composition-state-ModPRFGame
      (composition-state-ModPRFGame-__randomness State_ModPRFGame___randomness)
      (composition-state-ModPRFGame-prf State_ModPRFGame_prf)
      (composition-state-ModPRFGame-key_top State_ModPRFGame_key_top)
      (composition-state-ModPRFGame-key_bottom State_ModPRFGame_key_bottom))))
(declare-datatype
  Return_ModPRFGame_prf_Eval
  (
    (mk-return-ModPRFGame-prf-Eval
      (return-ModPRFGame-prf-Eval-state CompositionState-ModPRFGame)
      (return-ModPRFGame-prf-Eval-value Bits_n))
    (mk-abort-ModPRFGame-prf-Eval)))
(declare-datatype
  Return_ModPRFGame_key_top_Get
  (
    (mk-return-ModPRFGame-key_top-Get
      (return-ModPRFGame-key_top-Get-state CompositionState-ModPRFGame)
      (return-ModPRFGame-key_top-Get-value Bits_n))
    (mk-abort-ModPRFGame-key_top-Get)))
(declare-datatype
  Return_ModPRFGame_key_top_Set
  (
    (mk-return-ModPRFGame-key_top-Set
      (return-ModPRFGame-key_top-Set-state CompositionState-ModPRFGame))
    (mk-abort-ModPRFGame-key_top-Set)))
(declare-datatype
  Return_ModPRFGame_key_bottom_Get
  (
    (mk-return-ModPRFGame-key_bottom-Get
      (return-ModPRFGame-key_bottom-Get-state CompositionState-ModPRFGame)
      (return-ModPRFGame-key_bottom-Get-value Bits_n))
    (mk-abort-ModPRFGame-key_bottom-Get)))
(declare-datatype
  Return_ModPRFGame_key_bottom_Set
  (
    (mk-return-ModPRFGame-key_bottom-Set
      (return-ModPRFGame-key_bottom-Set-state CompositionState-ModPRFGame))
    (mk-abort-ModPRFGame-key_bottom-Set))); Composition of ModPRFGame
(define-fun
  oracle-ModPRFGame-key_top-Get
  ((__global_state CompositionState-ModPRFGame))
  Return_ModPRFGame_key_top_Get
  (let
    ((__self_state (composition-state-ModPRFGame-key_top __global_state)))
    (ite
      (= (state-ModPRFGame-key_top-k __self_state) (as mk-none (Maybe Bits_n)))
      (let
        (
          (k_new
            (__sample-rand-ModPRFGame
              (state-ModPRFGame-__randomness-ctr
                (composition-state-ModPRFGame-__randomness __global_state)))))
        (let
          (
            (__global_state
              (mk-composition-state-ModPRFGame
                (mk-state-ModPRFGame-__randomness
                  (+
                    1
                    (state-ModPRFGame-__randomness-ctr
                      (composition-state-ModPRFGame-__randomness __global_state))))
                (composition-state-ModPRFGame-prf __global_state)
                (composition-state-ModPRFGame-key_top __global_state)
                (composition-state-ModPRFGame-key_bottom __global_state))))
          (let
            ((__self_state (mk-state-ModPRFGame-key_top (mk-some k_new))))
            (ite
              ((_ is (mk-none () (Maybe Bits_n))) (state-ModPRFGame-key_top-k __self_state))
              mk-abort-ModPRFGame-key_top-Get
              (let
                ((k_ret (maybe-get (state-ModPRFGame-key_top-k __self_state))))
                (let
                  (
                    (__global_state
                      (mk-composition-state-ModPRFGame
                        (composition-state-ModPRFGame-__randomness __global_state)
                        (composition-state-ModPRFGame-prf __global_state)
                        __self_state
                        (composition-state-ModPRFGame-key_bottom __global_state))))
                  (mk-return-ModPRFGame-key_top-Get __global_state k_ret)))))))
      (ite
        ((_ is (mk-none () (Maybe Bits_n))) (state-ModPRFGame-key_top-k __self_state))
        mk-abort-ModPRFGame-key_top-Get
        (let
          ((k_ret (maybe-get (state-ModPRFGame-key_top-k __self_state))))
          (let
            (
              (__global_state
                (mk-composition-state-ModPRFGame
                  (composition-state-ModPRFGame-__randomness __global_state)
                  (composition-state-ModPRFGame-prf __global_state)
                  __self_state
                  (composition-state-ModPRFGame-key_bottom __global_state))))
            (mk-return-ModPRFGame-key_top-Get __global_state k_ret)))))))
(define-fun
  oracle-ModPRFGame-key_top-Set
  ((__global_state CompositionState-ModPRFGame) (k_new Bits_n))
  Return_ModPRFGame_key_top_Set
  (let
    ((__self_state (composition-state-ModPRFGame-key_top __global_state)))
    (ite
      (not (= (state-ModPRFGame-key_top-k __self_state) (as mk-none (Maybe Bits_n))))
      mk-abort-ModPRFGame-key_top-Set
      (let
        ((__self_state (mk-state-ModPRFGame-key_top (mk-some k_new))))
        (mk-return-ModPRFGame-key_top-Set __global_state)))))
(define-fun
  oracle-ModPRFGame-key_bottom-Get
  ((__global_state CompositionState-ModPRFGame))
  Return_ModPRFGame_key_bottom_Get
  (let
    ((__self_state (composition-state-ModPRFGame-key_bottom __global_state)))
    (ite
      (= (state-ModPRFGame-key_bottom-k __self_state) (as mk-none (Maybe Bits_n)))
      (let
        (
          (k_new
            (__sample-rand-ModPRFGame
              (state-ModPRFGame-__randomness-ctr
                (composition-state-ModPRFGame-__randomness __global_state)))))
        (let
          (
            (__global_state
              (mk-composition-state-ModPRFGame
                (mk-state-ModPRFGame-__randomness
                  (+
                    1
                    (state-ModPRFGame-__randomness-ctr
                      (composition-state-ModPRFGame-__randomness __global_state))))
                (composition-state-ModPRFGame-prf __global_state)
                (composition-state-ModPRFGame-key_top __global_state)
                (composition-state-ModPRFGame-key_bottom __global_state))))
          (let
            ((__self_state (mk-state-ModPRFGame-key_bottom (mk-some k_new))))
            (ite
              (
                (_ is (mk-none () (Maybe Bits_n)))
                (state-ModPRFGame-key_bottom-k __self_state))
              mk-abort-ModPRFGame-key_bottom-Get
              (let
                ((k_ret (maybe-get (state-ModPRFGame-key_bottom-k __self_state))))
                (let
                  (
                    (__global_state
                      (mk-composition-state-ModPRFGame
                        (composition-state-ModPRFGame-__randomness __global_state)
                        (composition-state-ModPRFGame-prf __global_state)
                        (composition-state-ModPRFGame-key_top __global_state)
                        __self_state)))
                  (mk-return-ModPRFGame-key_bottom-Get __global_state k_ret)))))))
      (ite
        (
          (_ is (mk-none () (Maybe Bits_n)))
          (state-ModPRFGame-key_bottom-k __self_state))
        mk-abort-ModPRFGame-key_bottom-Get
        (let
          ((k_ret (maybe-get (state-ModPRFGame-key_bottom-k __self_state))))
          (let
            (
              (__global_state
                (mk-composition-state-ModPRFGame
                  (composition-state-ModPRFGame-__randomness __global_state)
                  (composition-state-ModPRFGame-prf __global_state)
                  (composition-state-ModPRFGame-key_top __global_state)
                  __self_state)))
            (mk-return-ModPRFGame-key_bottom-Get __global_state k_ret)))))))
(define-fun
  oracle-ModPRFGame-key_bottom-Set
  ((__global_state CompositionState-ModPRFGame) (k_new Bits_n))
  Return_ModPRFGame_key_bottom_Set
  (let
    ((__self_state (composition-state-ModPRFGame-key_bottom __global_state)))
    (ite
      (not
        (= (state-ModPRFGame-key_bottom-k __self_state) (as mk-none (Maybe Bits_n))))
      mk-abort-ModPRFGame-key_bottom-Set
      (let
        ((__self_state (mk-state-ModPRFGame-key_bottom (mk-some k_new))))
        (mk-return-ModPRFGame-key_bottom-Set __global_state)))))
(define-fun
  oracle-ModPRFGame-prf-Eval
  ((__global_state CompositionState-ModPRFGame) (msg Bits_n))
  Return_ModPRFGame_prf_Eval
  (let
    ((__self_state (composition-state-ModPRFGame-prf __global_state)))
    (let
      ((__ret (oracle-ModPRFGame-key_top-Get __global_state)))
      (ite
        ((_ is mk-abort-ModPRFGame-key_top-Get) __ret)
        mk-abort-ModPRFGame-prf-Eval
        (let
          (
            (__global_state (return-ModPRFGame-key_top-Get-state __ret))
            (k (return-ModPRFGame-key_top-Get-value __ret)))
          (let
            ((out (f k msg)))
            (let
              (
                (__global_state
                  (mk-composition-state-ModPRFGame
                    (composition-state-ModPRFGame-__randomness __global_state)
                    __self_state
                    (composition-state-ModPRFGame-key_top __global_state)
                    (composition-state-ModPRFGame-key_bottom __global_state))))
              (mk-return-ModPRFGame-prf-Eval __global_state out))))))))

(check-sat)