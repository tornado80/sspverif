(declare-datatypes ((Maybe 1)) ((par (T) ((mk-some (maybe-get T)) (mk-none)))))
(declare-datatypes
  ((Tuple2 2))
  ((par (T1 T2) ((mk-tuple2 (el1 T1) (el2 T2))))))
(declare-sort Bits_n 0)
(declare-sort Bits_* 0)
(declare-fun f (Bits_n Bits_*) Bits_n)

; Left
(declare-fun __sample-rand-Left-Bits_n (Int Int) Bits_n)
(declare-datatype
  State_Left___randomness
  ((mk-state-Left-__randomness (state-Left-__randomness-ctr1 Int))))
(declare-datatype
  State_Left_key_top
  ((mk-state-Left-key_top (state-Left-key_top-T (Array Int (Maybe Bits_n))))))
(declare-datatype State_Left_prf_left ((mk-state-Left-prf_left)))
(declare-datatype
  CompositionState-Left
  (
    (mk-composition-state-Left
      (composition-state-Left-__randomness State_Left___randomness)
      (composition-state-Left-key_top State_Left_key_top)
      (composition-state-Left-prf_left State_Left_prf_left))))
(declare-datatype
  Return_Left_key_top_GET
  (
    (mk-return-Left-key_top-GET
      (return-Left-key_top-GET-state CompositionState-Left)
      (return-Left-key_top-GET-value Bits_n))
    (mk-abort-Left-key_top-GET)))
(declare-datatype
  Return_Left_key_top_SET
  (
    (mk-return-Left-key_top-SET
      (return-Left-key_top-SET-state CompositionState-Left)
      (return-Left-key_top-SET-value Int))
    (mk-abort-Left-key_top-SET)))
(declare-datatype
  Return_Left_prf_left_EVAL
  (
    (mk-return-Left-prf_left-EVAL
      (return-Left-prf_left-EVAL-state CompositionState-Left)
      (return-Left-prf_left-EVAL-value Bits_n))
    (mk-abort-Left-prf_left-EVAL)))
    
; Composition of Left
(define-fun
  oracle-Left-key_top-GET
  ((__global_state CompositionState-Left) (h Int))
  Return_Left_key_top_GET
  (let
    ((__self_state (composition-state-Left-key_top __global_state)))
    (ite
      (not
        (= (select (state-Left-key_top-T __self_state) h) (as mk-none (Maybe Bits_n))))
      (ite
        (
          (_ is (mk-none () (Maybe Bits_n)))
          (select (state-Left-key_top-T __self_state) h))
        mk-abort-Left-key_top-GET
        (let
          ((unwrap-1 (maybe-get (select (state-Left-key_top-T __self_state) h))))
          (let
            ((k unwrap-1))
            (let
              (
                (__global_state
                  (mk-composition-state-Left
                    (composition-state-Left-__randomness __global_state)
                    __self_state
                    (composition-state-Left-prf_left __global_state))))
              (mk-return-Left-key_top-GET __global_state k)))))
      mk-abort-Left-key_top-GET)))
(define-fun
  oracle-Left-key_top-SET
  ((__global_state CompositionState-Left) (h Int) (k Bits_n))
  Return_Left_key_top_SET
  (let
    ((__self_state (composition-state-Left-key_top __global_state)))
    (ite
      (= (select (state-Left-key_top-T __self_state) h) (as mk-none (Maybe Bits_n)))
      (let
        (
          (kk
            (__sample-rand-Left-Bits_n
              1
              (state-Left-__randomness-ctr1
                (composition-state-Left-__randomness __global_state)))))
        (let
          (
            (__global_state
              (mk-composition-state-Left
                (mk-state-Left-__randomness
                  (+
                    1
                    (state-Left-__randomness-ctr1
                      (composition-state-Left-__randomness __global_state))))
                (composition-state-Left-key_top __global_state)
                (composition-state-Left-prf_left __global_state))))
          (let
            (
              (__self_state
                (mk-state-Left-key_top
                  (store (state-Left-key_top-T __self_state) h (mk-some kk)))))
            (let
              (
                (__global_state
                  (mk-composition-state-Left
                    (composition-state-Left-__randomness __global_state)
                    __self_state
                    (composition-state-Left-prf_left __global_state))))
              (mk-return-Left-key_top-SET __global_state h)))))
      mk-abort-Left-key_top-SET)))
(define-fun
  oracle-Left-prf_left-EVAL
  ((__global_state CompositionState-Left) (h Int) (m Bits_*))
  Return_Left_prf_left_EVAL
  (let
    ((__self_state (composition-state-Left-prf_left __global_state)))
    (let
      ((__ret (oracle-Left-key_top-GET __global_state h)))
      (ite
        ((_ is mk-abort-Left-key_top-GET) __ret)
        mk-abort-Left-prf_left-EVAL
        (let
          (
            (__global_state (return-Left-key_top-GET-state __ret))
            (k (return-Left-key_top-GET-value __ret)))
          (let
            ((y (f k m)))
            (let
              (
                (__global_state
                  (mk-composition-state-Left
                    (composition-state-Left-__randomness __global_state)
                    (composition-state-Left-key_top __global_state)
                    __self_state)))
              (mk-return-Left-prf_left-EVAL __global_state y)))))))); Right
(declare-fun __sample-rand-Right-Bits_n (Int Int) Bits_n)
(declare-datatype
  State_Right___randomness
  ((mk-state-Right-__randomness (state-Right-__randomness-ctr1 Int))))
(declare-datatype
  State_Right_key_top
  ((mk-state-Right-key_top (state-Right-key_top-T (Array Int (Maybe Bits_n))))))
(declare-datatype
  State_Right_key_bottom
  (
    (mk-state-Right-key_bottom
      (state-Right-key_bottom-T (Array (Tuple2 Int Bits_*) (Maybe Bits_n))))))
(declare-datatype State_Right_prf_right ((mk-state-Right-prf_right)))
(declare-datatype State_Right_wrapper ((mk-state-Right-wrapper)))
(declare-datatype
  CompositionState-Right
  (
    (mk-composition-state-Right
      (composition-state-Right-__randomness State_Right___randomness)
      (composition-state-Right-key_top State_Right_key_top)
      (composition-state-Right-key_bottom State_Right_key_bottom)
      (composition-state-Right-prf_right State_Right_prf_right)
      (composition-state-Right-wrapper State_Right_wrapper))))
(declare-datatype
  Return_Right_key_top_GET
  (
    (mk-return-Right-key_top-GET
      (return-Right-key_top-GET-state CompositionState-Right)
      (return-Right-key_top-GET-value Bits_n))
    (mk-abort-Right-key_top-GET)))
(declare-datatype
  Return_Right_key_top_SET
  (
    (mk-return-Right-key_top-SET
      (return-Right-key_top-SET-state CompositionState-Right)
      (return-Right-key_top-SET-value Int))
    (mk-abort-Right-key_top-SET)))
(declare-datatype
  Return_Right_key_bottom_GET
  (
    (mk-return-Right-key_bottom-GET
      (return-Right-key_bottom-GET-state CompositionState-Right)
      (return-Right-key_bottom-GET-value Bits_n))
    (mk-abort-Right-key_bottom-GET)))
(declare-datatype
  Return_Right_key_bottom_SET
  (
    (mk-return-Right-key_bottom-SET
      (return-Right-key_bottom-SET-state CompositionState-Right)
      (return-Right-key_bottom-SET-value (Tuple2 Int Bits_*)))
    (mk-abort-Right-key_bottom-SET)))
(declare-datatype
  Return_Right_prf_right_EVAL
  (
    (mk-return-Right-prf_right-EVAL
      (return-Right-prf_right-EVAL-state CompositionState-Right)
      (return-Right-prf_right-EVAL-value (Tuple2 Int Bits_*)))
    (mk-abort-Right-prf_right-EVAL)))
(declare-datatype
  Return_Right_wrapper_EVAL
  (
    (mk-return-Right-wrapper-EVAL
      (return-Right-wrapper-EVAL-state CompositionState-Right)
      (return-Right-wrapper-EVAL-value Bits_n))
    (mk-abort-Right-wrapper-EVAL))); Composition of Right
(define-fun
  oracle-Right-key_top-GET
  ((__global_state CompositionState-Right) (h Int))
  Return_Right_key_top_GET
  (let
    ((__self_state (composition-state-Right-key_top __global_state)))
    (ite
      (not
        (= (select (state-Right-key_top-T __self_state) h) (as mk-none (Maybe Bits_n))))
      (ite
        (
          (_ is (mk-none () (Maybe Bits_n)))
          (select (state-Right-key_top-T __self_state) h))
        mk-abort-Right-key_top-GET
        (let
          ((unwrap-1 (maybe-get (select (state-Right-key_top-T __self_state) h))))
          (let
            ((k unwrap-1))
            (let
              (
                (__global_state
                  (mk-composition-state-Right
                    (composition-state-Right-__randomness __global_state)
                    __self_state
                    (composition-state-Right-key_bottom __global_state)
                    (composition-state-Right-prf_right __global_state)
                    (composition-state-Right-wrapper __global_state))))
              (mk-return-Right-key_top-GET __global_state k)))))
      mk-abort-Right-key_top-GET)))
(define-fun
  oracle-Right-key_top-SET
  ((__global_state CompositionState-Right) (h Int) (k Bits_n))
  Return_Right_key_top_SET
  (let
    ((__self_state (composition-state-Right-key_top __global_state)))
    (ite
      (= (select (state-Right-key_top-T __self_state) h) (as mk-none (Maybe Bits_n)))
      (let
        (
          (kk
            (__sample-rand-Right-Bits_n
              1
              (state-Right-__randomness-ctr1
                (composition-state-Right-__randomness __global_state)))))
        (let
          (
            (__global_state
              (mk-composition-state-Right
                (mk-state-Right-__randomness
                  (+
                    1
                    (state-Right-__randomness-ctr1
                      (composition-state-Right-__randomness __global_state))))
                (composition-state-Right-key_top __global_state)
                (composition-state-Right-key_bottom __global_state)
                (composition-state-Right-prf_right __global_state)
                (composition-state-Right-wrapper __global_state))))
          (let
            (
              (__self_state
                (mk-state-Right-key_top
                  (store (state-Right-key_top-T __self_state) h (mk-some kk)))))
            (let
              (
                (__global_state
                  (mk-composition-state-Right
                    (composition-state-Right-__randomness __global_state)
                    __self_state
                    (composition-state-Right-key_bottom __global_state)
                    (composition-state-Right-prf_right __global_state)
                    (composition-state-Right-wrapper __global_state))))
              (mk-return-Right-key_top-SET __global_state h)))))
      mk-abort-Right-key_top-SET)))
(define-fun
  oracle-Right-key_bottom-GET
  ((__global_state CompositionState-Right) (hh (Tuple2 Int Bits_*)))
  Return_Right_key_bottom_GET
  (let
    ((__self_state (composition-state-Right-key_bottom __global_state)))
    (ite
      (not
        (=
          (select (state-Right-key_bottom-T __self_state) hh)
          (as mk-none (Maybe Bits_n))))
      (ite
        (
          (_ is (mk-none () (Maybe Bits_n)))
          (select (state-Right-key_bottom-T __self_state) hh))
        mk-abort-Right-key_bottom-GET
        (let
          ((unwrap-1 (maybe-get (select (state-Right-key_bottom-T __self_state) hh))))
          (let
            ((k unwrap-1))
            (let
              (
                (__global_state
                  (mk-composition-state-Right
                    (composition-state-Right-__randomness __global_state)
                    (composition-state-Right-key_top __global_state)
                    __self_state
                    (composition-state-Right-prf_right __global_state)
                    (composition-state-Right-wrapper __global_state))))
              (mk-return-Right-key_bottom-GET __global_state k)))))
      mk-abort-Right-key_bottom-GET)))
(define-fun
  oracle-Right-key_bottom-SET
  ((__global_state CompositionState-Right) (h (Tuple2 Int Bits_*)) (k Bits_n))
  Return_Right_key_bottom_SET
  (let
    ((__self_state (composition-state-Right-key_bottom __global_state)))
    (ite
      (=
        (select (state-Right-key_bottom-T __self_state) h)
        (as mk-none (Maybe Bits_n)))
      (let
        (
          (__self_state
            (mk-state-Right-key_bottom
              (store (state-Right-key_bottom-T __self_state) h (mk-some k)))))
        (let
          (
            (__global_state
              (mk-composition-state-Right
                (composition-state-Right-__randomness __global_state)
                (composition-state-Right-key_top __global_state)
                __self_state
                (composition-state-Right-prf_right __global_state)
                (composition-state-Right-wrapper __global_state))))
          (mk-return-Right-key_bottom-SET __global_state h)))
      mk-abort-Right-key_bottom-SET)))
(define-fun
  oracle-Right-prf_right-EVAL
  ((__global_state CompositionState-Right) (h Int) (m Bits_*))
  Return_Right_prf_right_EVAL
  (let
    ((__self_state (composition-state-Right-prf_right __global_state)))
    (let
      ((__ret (oracle-Right-key_top-GET __global_state h)))
      (ite
        ((_ is mk-abort-Right-key_top-GET) __ret)
        mk-abort-Right-prf_right-EVAL
        (let
          (
            (__global_state (return-Right-key_top-GET-state __ret))
            (k (return-Right-key_top-GET-value __ret)))
          (let
            ((y (f k m)))
            (let
              ((hh (mk-tuple2 h m)))
              (let
                ((__ret (oracle-Right-key_bottom-SET __global_state hh y)))
                (ite
                  ((_ is mk-abort-Right-key_bottom-SET) __ret)
                  mk-abort-Right-prf_right-EVAL
                  (let
                    (
                      (__global_state (return-Right-key_bottom-SET-state __ret))
                      (_ (return-Right-key_bottom-SET-value __ret)))
                    (let
                      (
                        (__global_state
                          (mk-composition-state-Right
                            (composition-state-Right-__randomness __global_state)
                            (composition-state-Right-key_top __global_state)
                            (composition-state-Right-key_bottom __global_state)
                            __self_state
                            (composition-state-Right-wrapper __global_state))))
                      (mk-return-Right-prf_right-EVAL __global_state hh))))))))))))
(define-fun
  oracle-Right-wrapper-EVAL
  ((__global_state CompositionState-Right) (h Int) (m Bits_*))
  Return_Right_wrapper_EVAL
  (let
    ((__self_state (composition-state-Right-wrapper __global_state)))
    (let
      ((__ret (oracle-Right-prf_right-EVAL __global_state h m)))
      (ite
        ((_ is mk-abort-Right-prf_right-EVAL) __ret)
        mk-abort-Right-wrapper-EVAL
        (let
          (
            (__global_state (return-Right-prf_right-EVAL-state __ret))
            (_ (return-Right-prf_right-EVAL-value __ret)))
          (let
            ((hh (mk-tuple2 h m)))
            (let
              ((__ret (oracle-Right-key_bottom-GET __global_state hh)))
              (ite
                ((_ is mk-abort-Right-key_bottom-GET) __ret)
                mk-abort-Right-wrapper-EVAL
                (let
                  (
                    (__global_state (return-Right-key_bottom-GET-state __ret))
                    (k (return-Right-key_bottom-GET-value __ret)))
                  (let
                    (
                      (__global_state
                        (mk-composition-state-Right
                          (composition-state-Right-__randomness __global_state)
                          (composition-state-Right-key_top __global_state)
                          (composition-state-Right-key_bottom __global_state)
                          (composition-state-Right-prf_right __global_state)
                          __self_state)))
                    (mk-return-Right-wrapper-EVAL __global_state k)))))))))))


; define invariant on s-left,s-right
(define-fun inv                                        ; function name 
           ((s-left  CompositionState-Left) ; function input 
            (s-right CompositionState-Right))
            Bool                                       ; function behaviour           
             (
        let  (
            (bot (as mk-none (Maybe Bits_n)))
            (botint (as mk-none (Maybe Int))) 
            (botstuff (as mk-none (Maybe (Tuple2 Int Bits_*))))
             )

             ( 
;            (TIKL (Array Int               Bits_n))   ;      TIKL: T in input (top) key package left
;            (TIKR (Array Int               Bits_n))   ;      TIKR: T in input (top) key package right
;            (TOKR (Array (Tuple2 Int Bits_*) Bits_n)) ;      TOKR: T in output (bottom) key package right
  
                ; assignment of randomness state
                    let ((r-left 
                            (composition-state-Left-__randomness 
                             s-left))
                         (r-right 
                            (composition-state-Right-__randomness 
                             s-right))

                ; assignment of tables
                         (TIKL (state-Left-key_top-T
                            (composition-state-Left-key_top 
                             s-left)))
                         (TIKR (state-Right-key_top-T
                            (composition-state-Right-key_top 
                             s-right)))
                         (TOKR (state-Right-key_bottom-T
                            (composition-state-Right-key_bottom 
                             s-right))))
                (ite
                (and
                ; randomness is the same
                   (=
                   (state-Left-__randomness-ctr1 r-left)
                   (state-Right-__randomness-ctr1 r-right)
                   )
                ; (LR)  TIKL = TOKL 
                    (= TIKL TIKR)
                ; (R)   TOKL[(h,m)] = f(TIKL[h],m) or bot 
                    (forall ((h Int)(m Bits_*)(hh (Tuple2 Int Bits_*)))
                                      (=> (= hh (h m)) ; How does that work?
                                      (or (= (TOKR hh) bot) (= (TOKR hh) (f (TIKR h) m))))
                                     )
                    )
            )
            true
            false
            )))

;;;;;;;;;; EVAL oracle
; existential quantification
(assert (and (exists 
               (
               (s-left-old CompositionState-Left)
               (s-right-old CompositionState-Right)   
               ; These two lines change from oracle to oracle
               (h Int)
               (m Bits_*)
               )

; assignment after execution
      ;The following 6 lines changes from oracle to oracle:
      (let ((left-new     (oracle-Left-prf_left-EVAL s-left-old h m))) ; left function on left state
      (let ((s-left-new   (return-Left-prf_left-EVAL-state left-new)))
      (let ((y-left-new   (return-Left-prf_left-EVAL-value left-new)))
      (let ((right-new    (oracle-Right-prf_right-EVAL s-right-old h m))) ; right function on right state     
      (let ((s-right-new  (return-Right-prf_right-EVAL-state right-new)))
      (let ((y-right-new  (return-Right-prf_right-EVAL-value right-new)))

; and
(and

; pre-condition
    (= true (inv s-left-old s-right-old))     
    (forall ((n Int)) (= (__sample-rand-Left-Bits_n n) (__sample-rand-Right-Bits_n n)))    

; negation
(not (or

; both abort
(and
(= mk-abort-Left-prf-EVAL left-new)
(= mk-abort-Right-map-EVAL right-new)
)

; and
(and

; none of the oracles aborts
(not (= mk-abort-Left-prf-EVAL left-new))
(not (= mk-abort-Right-map-EVAL right-new))

; post-condition on states
(= true (inv s-left-new s-right-new))

; post-condition on outputs
(= y-left-new y-right-new )
)))
))))))))))




(check-sat)