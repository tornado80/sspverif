; invariant
; Post-condition:
; called on same inputs, then output is the same and if output was not abort, then same state
;

(declare-datatypes ((Maybe 1)) ((par (T) ((mk-some (maybe-get T)) (mk-none)))))
(declare-sort Bits_n 0)
(declare-sort Bits_* 0)
(declare-datatypes (
    (Tuple2 2)) (
        (par (T1 T2) (
            (mk-tuple2 (el1 T1) (el2 T2))
        ))
    )
)

; CompositionLeft
(declare-datatype State_CompositionLeft___randomness 
    ((mk-state-CompositionLeft-__randomness 
        (state-CompositionLeft-__randomness-ctr Int))))
(declare-fun __sample-rand-CompositionLeft (Int) Bits_n)
(declare-datatype State_CompositionLeft_key 
    ((mk-state-CompositionLeft-key 
        (state-CompositionLeft-key-T (Array Int (Maybe Bits_n))))))
(declare-datatype CompositionState-CompositionLeft 
    ((mk-composition-state-CompositionLeft 
        (composition-state-CompositionLeft-__randomness State_CompositionLeft___randomness) 
        (composition-state-CompositionLeft-key State_CompositionLeft_key))))
(declare-datatype Return_CompositionLeft_key_GET 
    ((mk-return-CompositionLeft-key-GET 
        (return-CompositionLeft-key-GET-state CompositionState-CompositionLeft) 
        (return-CompositionLeft-key-GET-value Bits_n)) 
     (mk-abort-CompositionLeft-key-GET)))
(declare-datatype Return_CompositionLeft_key_SET 
    ((mk-return-CompositionLeft-key-SET 
        (return-CompositionLeft-key-SET-state CompositionState-CompositionLeft) 
        (return-CompositionLeft-key-SET-value Int)) 
     (mk-abort-CompositionLeft-key-SET)))
(define-fun oracle-CompositionLeft-key-GET 
    ((__global_state CompositionState-CompositionLeft) (h Int)) 
        Return_CompositionLeft_key_GET 
            (let ((__self_state (composition-state-CompositionLeft-key __global_state))) 
                 (ite (not (= (select (state-CompositionLeft-key-T __self_state) h) 
                 (as mk-none (Maybe Bits_n)))) (ite ((_ is (mk-none () (Maybe Bits_n))) 
                 (select (state-CompositionLeft-key-T __self_state) h)) mk-abort-CompositionLeft-key-GET (let ((unwrap-1 (maybe-get (select (state-CompositionLeft-key-T __self_state) h)))) 
                 (let ((k unwrap-1)) (let ((__global_state (mk-composition-state-CompositionLeft (composition-state-CompositionLeft-__randomness __global_state) __self_state))) 
                 (mk-return-CompositionLeft-key-GET __global_state k))))) mk-abort-CompositionLeft-key-GET)))
(define-fun oracle-CompositionLeft-key-SET 
    ((__global_state CompositionState-CompositionLeft) (h Int) (k Bits_n)) 
    Return_CompositionLeft_key_SET 
    (let ((__self_state (composition-state-CompositionLeft-key __global_state))) 
         (ite 
            (= (select (state-CompositionLeft-key-T __self_state) h) (as mk-none (Maybe Bits_n))) 
            (let ((kk (__sample-rand-CompositionLeft (state-CompositionLeft-__randomness-ctr (composition-state-CompositionLeft-__randomness __global_state))))) (let ((__global_state (mk-composition-state-CompositionLeft (mk-state-CompositionLeft-__randomness (+ 1 (state-CompositionLeft-__randomness-ctr (composition-state-CompositionLeft-__randomness __global_state)))) (composition-state-CompositionLeft-key __global_state)))) (let ((__self_state (mk-state-CompositionLeft-key (store (state-CompositionLeft-key-T __self_state) h (mk-some kk))))) (let ((__global_state (mk-composition-state-CompositionLeft (composition-state-CompositionLeft-__randomness __global_state) __self_state))) (mk-return-CompositionLeft-key-SET __global_state h))))) mk-abort-CompositionLeft-key-SET)))
            
; CompositionRight  
(declare-datatype State_CompositionRight___randomness ((mk-state-CompositionRight-__randomness (state-CompositionRight-__randomness-ctr Int))))(declare-fun __sample-rand-CompositionRight (Int) Bits_n)(declare-datatype State_CompositionRight_key ((mk-state-CompositionRight-key (state-CompositionRight-key-T (Array Int (Maybe Bits_n))))))(declare-datatype CompositionState-CompositionRight ((mk-composition-state-CompositionRight (composition-state-CompositionRight-__randomness State_CompositionRight___randomness) (composition-state-CompositionRight-key State_CompositionRight_key))))(declare-datatype Return_CompositionRight_key_GET ((mk-return-CompositionRight-key-GET (return-CompositionRight-key-GET-state CompositionState-CompositionRight) (return-CompositionRight-key-GET-value Bits_n)) (mk-abort-CompositionRight-key-GET)))(declare-datatype Return_CompositionRight_key_SET ((mk-return-CompositionRight-key-SET (return-CompositionRight-key-SET-state CompositionState-CompositionRight) (return-CompositionRight-key-SET-value Int)) (mk-abort-CompositionRight-key-SET))); Composition of CompositionRight
(define-fun oracle-CompositionRight-key-GET 
    ((__global_state CompositionState-CompositionRight) (h Int)) 
        Return_CompositionRight_key_GET 
            (let ((__self_state (composition-state-CompositionRight-key __global_state))) 
                 (ite (not (= (select (state-CompositionRight-key-T __self_state) h) 
                 (as mk-none (Maybe Bits_n)))) (ite ((_ is (mk-none () (Maybe Bits_n)))
                 (select (state-CompositionRight-key-T __self_state) h)) mk-abort-CompositionRight-key-GET (let ((unwrap-1 (maybe-get (select (state-CompositionRight-key-T __self_state) h)))) 
                 (let ((k unwrap-1)) (let ((__global_state (mk-composition-state-CompositionRight (composition-state-CompositionRight-__randomness __global_state) __self_state))) 
                 (mk-return-CompositionRight-key-GET __global_state k))))) mk-abort-CompositionRight-key-GET)))

(define-fun oracle-CompositionRight-key-SET ((__global_state CompositionState-CompositionRight) (h Int) (k Bits_n)) Return_CompositionRight_key_SET (let ((__self_state (composition-state-CompositionRight-key __global_state))) (ite (= (select (state-CompositionRight-key-T __self_state) h) (as mk-none (Maybe Bits_n))) (let ((kk (__sample-rand-CompositionRight (state-CompositionRight-__randomness-ctr (composition-state-CompositionRight-__randomness __global_state))))) (let ((__global_state (mk-composition-state-CompositionRight (mk-state-CompositionRight-__randomness (+ 1 (state-CompositionRight-__randomness-ctr (composition-state-CompositionRight-__randomness __global_state)))) (composition-state-CompositionRight-key __global_state)))) (let ((__self_state (mk-state-CompositionRight-key (store (state-CompositionRight-key-T __self_state) h (mk-some kk))))) (let ((__global_state (mk-composition-state-CompositionRight (composition-state-CompositionRight-__randomness __global_state) __self_state))) (mk-return-CompositionRight-key-SET __global_state h))))) mk-abort-CompositionRight-key-SET)))

; define invariant on s-left,s-right
(define-fun inv                                        ; function name 
           ((s-left  CompositionState-CompositionLeft) ; function input 
            (s-right CompositionState-CompositionRight))
            Bool                                       ; function behaviour           
             (
        let  ( 
;            (TIKL (Array Int               Bits_n))   ;      TIKL: T in output  key package left
;            (TIKR (Array Int               Bits_n))   ;      TIKR: T in output  key package right
  
                ; assignment of randomness state
                         (r-left (state-CompositionLeft-__randomness-ctr
                            (composition-state-CompositionLeft-__randomness 
                             s-left)))
                         (r-right (state-CompositionRight-__randomness-ctr
                            (composition-state-CompositionRight-__randomness 
                             s-right)))

                ; assignment of tables
                         (TIKL (state-CompositionLeft-key-T
                            (composition-state-CompositionLeft-key 
                             s-left)))
                         (TIKR (state-CompositionRight-key-T 
                            (composition-state-CompositionRight-key
                             s-right)))
                )
                (ite
                (and
                ; randomness is the same
                    (= r-left r-right)           
                ; tables are the same 
                    (forall ((h Int)) (= (TIKL h) (TIKR h)) ))
            true
            false
            )))

;;;;;;;;;; Debugging
; (declare-const state-left-old  CompositionState-CompositionLeft)
; (declare-const state-right-old CompositionState-CompositionRight)
; (declare-const state-left-new  CompositionState-CompositionLeft)
; (declare-const state-right-new CompositionState-CompositionRight)
; (declare-const handle Int)
; (declare-const key-left Bits_n)
; (declare-const key-right Bits_n)



;;;;;;;;;; GET oracle
; existential quantification
(assert (exists 
               (
               (s-left-old CompositionState-CompositionLeft)
               (s-right-old CompositionState-CompositionRight)   
               ; These two lines change from oracle to oracle
               (h Int)
               )
;
;;;;;;; Debugging
;
; (= state-left-old s-left-old)
; (= state-right-old s-right-old)
; (= handle h)
;
; assignment after execution
      ;The following 6 lines changes from oracle to oracle:
      (let ((left-new     (oracle-CompositionLeft-key-GET s-left-old h))) ; left function on left state
      (let ((s-left-new   (return-CompositionLeft-key-GET-state left-new)))
      (let ((y-left-new   (return-CompositionLeft-key-GET-value left-new)))
      (let ((right-new    (oracle-CompositionRight-key-GET s-right-old h))) ; right function on right state     
      (let ((s-right-new  (return-CompositionRight-key-GET-state right-new)))
      (let ((y-right-new  (return-CompositionRight-key-GET-value right-new)))

; and
(and

; pre-condition
    (= true (inv s-left-old s-right-old))     
    (forall ((n Int)) (= (__sample-rand-CompositionLeft n) (__sample-rand-CompositionRight n)))    


; negation
(not (or

; both abort
(and
(= mk-abort-CompositionLeft-key-GET   left-new)
(= mk-abort-CompositionRight-key-GET right-new)
)

; and
(and

; none of the oracles aborts
(not (= mk-abort-CompositionLeft-key-GET   left-new))
(not (= mk-abort-CompositionRight-key-GET right-new))

; post-condition on states
(= true (inv s-left-new s-right-new))

; post-condition on outputs
(= y-left-new y-right-new )
)))

)))))))))


(check-sat)
;(get-model)
