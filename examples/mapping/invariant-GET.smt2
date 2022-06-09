; invariant
; Notation: Left: no mapping, Right: mapping
;      TIKL: T in input  (top)    key package left
;      TIKR: T in input  (top)    key package right
;      TOKL: T in output (bottom) key package left
;      TOKR: T in output (bottom) key package right
;      MIR : input- mapping table (right)
;      MOR : output-mapping table (right)
;
; Left-Right Invariant:
; (LRIa) TIKL[h] != bot iff MIR[h] != bot 
; (LRIb) MIR [h]  = h' != bot => TIKL[h] = TIKR[h']
; (LROa) TOKL[h] != bot iff MOR[h] != bot 
; (LROb) MOR [h]  = h' != bot => TOKL[h] = TOKR[h']
;
; Right-Right Invariant:
; (RI) (exists h s.t. MIR[h] = h') iff TIKR[h'] != bot
; (RO) (exists h s.t. MOR[h] = h') iff TOKR[h'] != bot
; 
; Post-condition:
; called on same inputs, then output is the same and if output was not abort, then same state
;

(declare-datatypes ((Maybe 1)) ((par (T) ((mk-some (maybe-get T)) (mk-none)))))
(declare-sort Bits_n 0)
(declare-sort Bits_* 0)
(declare-fun f (Bits_n Bits_*) Bits_n)
(declare-datatypes (
    (Tuple2 2)) (
        (par (T1 T2) (
            (mk-tuple2 (el1 T1) (el2 T2))
        ))
    )
)

; CompositionNoMappingGame
(declare-datatype State_CompositionNoMappingGame___randomness ((mk-state-CompositionNoMappingGame-__randomness (state-CompositionNoMappingGame-__randomness-ctr Int))))
(declare-fun __sample-rand-CompositionNoMappingGame (Int) Bits_n)
(declare-datatype State_CompositionNoMappingGame_key_top ((mk-state-CompositionNoMappingGame-key_top (state-CompositionNoMappingGame-key_top-T (Array Int (Maybe Bits_n))))))
(declare-datatype State_CompositionNoMappingGame_key_bottom ((mk-state-CompositionNoMappingGame-key_bottom (state-CompositionNoMappingGame-key_bottom-T (Array (Tuple2 Int Bits_*) (Maybe Bits_n))))))(declare-datatype State_CompositionNoMappingGame_prf ((mk-state-CompositionNoMappingGame-prf)))
(declare-datatype CompositionState-CompositionNoMappingGame 
        ((mk-composition-state-CompositionNoMappingGame 
                (composition-state-CompositionNoMappingGame-__randomness State_CompositionNoMappingGame___randomness) 
                (composition-state-CompositionNoMappingGame-key_top State_CompositionNoMappingGame_key_top) 
                (composition-state-CompositionNoMappingGame-key_bottom State_CompositionNoMappingGame_key_bottom) 
                (composition-state-CompositionNoMappingGame-prf State_CompositionNoMappingGame_prf))))

(declare-datatype Return_CompositionNoMappingGame_key_top_GET ((mk-return-CompositionNoMappingGame-key_top-GET (return-CompositionNoMappingGame-key_top-GET-state CompositionState-CompositionNoMappingGame) (return-CompositionNoMappingGame-key_top-GET-value Bits_n)) (mk-abort-CompositionNoMappingGame-key_top-GET)))
(declare-datatype Return_CompositionNoMappingGame_key_top_SET ((mk-return-CompositionNoMappingGame-key_top-SET (return-CompositionNoMappingGame-key_top-SET-state CompositionState-CompositionNoMappingGame) (return-CompositionNoMappingGame-key_top-SET-value Int)) (mk-abort-CompositionNoMappingGame-key_top-SET)))
(declare-datatype Return_CompositionNoMappingGame_key_bottom_GET ((mk-return-CompositionNoMappingGame-key_bottom-GET (return-CompositionNoMappingGame-key_bottom-GET-state CompositionState-CompositionNoMappingGame) (return-CompositionNoMappingGame-key_bottom-GET-value Bits_n)) (mk-abort-CompositionNoMappingGame-key_bottom-GET)))
(declare-datatype Return_CompositionNoMappingGame_key_bottom_SET ((mk-return-CompositionNoMappingGame-key_bottom-SET (return-CompositionNoMappingGame-key_bottom-SET-state CompositionState-CompositionNoMappingGame) (return-CompositionNoMappingGame-key_bottom-SET-value (Tuple2 Int Bits_*))) (mk-abort-CompositionNoMappingGame-key_bottom-SET)))
(declare-datatype Return_CompositionNoMappingGame_prf_EVAL ((mk-return-CompositionNoMappingGame-prf-EVAL (return-CompositionNoMappingGame-prf-EVAL-state CompositionState-CompositionNoMappingGame) (return-CompositionNoMappingGame-prf-EVAL-value (Tuple2 Int Bits_*))) (mk-abort-CompositionNoMappingGame-prf-EVAL))); Composition of CompositionNoMappingGame
(define-fun oracle-CompositionNoMappingGame-key_top-GET ((__global_state CompositionState-CompositionNoMappingGame) (h Int)) Return_CompositionNoMappingGame_key_top_GET (let ((__self_state (composition-state-CompositionNoMappingGame-key_top __global_state))) (ite (not (= (select (state-CompositionNoMappingGame-key_top-T __self_state) h) (as mk-none (Maybe Bits_n)))) (ite ((_ is (mk-none () (Maybe Bits_n))) (select (state-CompositionNoMappingGame-key_top-T __self_state) h)) mk-abort-CompositionNoMappingGame-key_top-GET (let ((unwrap-1 (maybe-get (select (state-CompositionNoMappingGame-key_top-T __self_state) h)))) (let ((k unwrap-1)) (let ((__global_state (mk-composition-state-CompositionNoMappingGame (composition-state-CompositionNoMappingGame-__randomness __global_state) __self_state (composition-state-CompositionNoMappingGame-key_bottom __global_state) (composition-state-CompositionNoMappingGame-prf __global_state)))) (mk-return-CompositionNoMappingGame-key_top-GET __global_state k))))) mk-abort-CompositionNoMappingGame-key_top-GET)))
(define-fun oracle-CompositionNoMappingGame-key_top-SET ((__global_state CompositionState-CompositionNoMappingGame) (h Int) (k Bits_n)) Return_CompositionNoMappingGame_key_top_SET (let ((__self_state (composition-state-CompositionNoMappingGame-key_top __global_state))) (ite (= (select (state-CompositionNoMappingGame-key_top-T __self_state) h) (as mk-none (Maybe Bits_n))) (let ((kk (__sample-rand-CompositionNoMappingGame (state-CompositionNoMappingGame-__randomness-ctr (composition-state-CompositionNoMappingGame-__randomness __global_state))))) (let ((__global_state (mk-composition-state-CompositionNoMappingGame (mk-state-CompositionNoMappingGame-__randomness (+ 1 (state-CompositionNoMappingGame-__randomness-ctr (composition-state-CompositionNoMappingGame-__randomness __global_state)))) (composition-state-CompositionNoMappingGame-key_top __global_state) (composition-state-CompositionNoMappingGame-key_bottom __global_state) (composition-state-CompositionNoMappingGame-prf __global_state)))) (let ((__self_state (mk-state-CompositionNoMappingGame-key_top (store (state-CompositionNoMappingGame-key_top-T __self_state) h (mk-some kk))))) (let ((__global_state (mk-composition-state-CompositionNoMappingGame (composition-state-CompositionNoMappingGame-__randomness __global_state) __self_state (composition-state-CompositionNoMappingGame-key_bottom __global_state) (composition-state-CompositionNoMappingGame-prf __global_state)))) (mk-return-CompositionNoMappingGame-key_top-SET __global_state h))))) mk-abort-CompositionNoMappingGame-key_top-SET)))
(define-fun oracle-CompositionNoMappingGame-key_bottom-GET ((__global_state CompositionState-CompositionNoMappingGame) (h Int) (m Bits_*)) Return_CompositionNoMappingGame_key_bottom_GET (let ((__self_state (composition-state-CompositionNoMappingGame-key_bottom __global_state))) (ite (not (= (select (state-CompositionNoMappingGame-key_bottom-T __self_state) (mk-tuple2 h m)) (as mk-none (Maybe Bits_n)))) (ite ((_ is (mk-none () (Maybe Bits_n))) (select (state-CompositionNoMappingGame-key_bottom-T __self_state) (mk-tuple2 h m))) mk-abort-CompositionNoMappingGame-key_bottom-GET (let ((unwrap-1 (maybe-get (select (state-CompositionNoMappingGame-key_bottom-T __self_state) (mk-tuple2 h m))))) (let ((k unwrap-1)) (let ((__global_state (mk-composition-state-CompositionNoMappingGame (composition-state-CompositionNoMappingGame-__randomness __global_state) (composition-state-CompositionNoMappingGame-key_top __global_state) __self_state (composition-state-CompositionNoMappingGame-prf __global_state)))) (mk-return-CompositionNoMappingGame-key_bottom-GET __global_state k))))) mk-abort-CompositionNoMappingGame-key_bottom-GET)))
(define-fun oracle-CompositionNoMappingGame-key_bottom-SET ((__global_state CompositionState-CompositionNoMappingGame) (h (Tuple2 Int Bits_*)) (k Bits_n)) Return_CompositionNoMappingGame_key_bottom_SET (let ((__self_state (composition-state-CompositionNoMappingGame-key_bottom __global_state))) (ite (= (select (state-CompositionNoMappingGame-key_bottom-T __self_state) h) (as mk-none (Maybe Bits_n))) (let ((__self_state (mk-state-CompositionNoMappingGame-key_bottom (store (state-CompositionNoMappingGame-key_bottom-T __self_state) h (mk-some k))))) (let ((__global_state (mk-composition-state-CompositionNoMappingGame (composition-state-CompositionNoMappingGame-__randomness __global_state) (composition-state-CompositionNoMappingGame-key_top __global_state) __self_state (composition-state-CompositionNoMappingGame-prf __global_state)))) (mk-return-CompositionNoMappingGame-key_bottom-SET __global_state h))) mk-abort-CompositionNoMappingGame-key_bottom-SET)))
(define-fun oracle-CompositionNoMappingGame-prf-EVAL ((__global_state CompositionState-CompositionNoMappingGame) (h Int) (m Bits_*)) Return_CompositionNoMappingGame_prf_EVAL (let ((__self_state (composition-state-CompositionNoMappingGame-prf __global_state))) (let ((__ret (oracle-CompositionNoMappingGame-key_top-GET __global_state h))) (ite ((_ is mk-abort-CompositionNoMappingGame-key_top-GET) __ret) mk-abort-CompositionNoMappingGame-prf-EVAL (let ((__global_state (return-CompositionNoMappingGame-key_top-GET-state __ret)) (k (return-CompositionNoMappingGame-key_top-GET-value __ret))) (let ((y (f k m))) (let ((hh (mk-tuple2 h m))) (let ((__ret (oracle-CompositionNoMappingGame-key_bottom-SET __global_state hh y))) (ite ((_ is mk-abort-CompositionNoMappingGame-key_bottom-SET) __ret) mk-abort-CompositionNoMappingGame-prf-EVAL (let ((__global_state (return-CompositionNoMappingGame-key_bottom-SET-state __ret)) (_ (return-CompositionNoMappingGame-key_bottom-SET-value __ret))) (let ((__global_state (mk-composition-state-CompositionNoMappingGame (composition-state-CompositionNoMappingGame-__randomness __global_state) (composition-state-CompositionNoMappingGame-key_top __global_state) (composition-state-CompositionNoMappingGame-key_bottom __global_state) __self_state))) (mk-return-CompositionNoMappingGame-prf-EVAL __global_state hh)))))))))))); CompositionMappingGame
(declare-datatype State_CompositionMappingGame___randomness ((mk-state-CompositionMappingGame-__randomness (state-CompositionMappingGame-__randomness-ctr Int))))(declare-fun __sample-rand-CompositionMappingGame (Int) Bits_n)(declare-datatype State_CompositionMappingGame_key_top ((mk-state-CompositionMappingGame-key_top (state-CompositionMappingGame-key_top-T (Array Int (Maybe Bits_n))) (state-CompositionMappingGame-key_top-S (Array Bits_n (Maybe Int))))))(declare-datatype State_CompositionMappingGame_key_bottom ((mk-state-CompositionMappingGame-key_bottom (state-CompositionMappingGame-key_bottom-T (Array (Tuple2 Int Bits_*) (Maybe Bits_n))))))(declare-datatype State_CompositionMappingGame_prf ((mk-state-CompositionMappingGame-prf)))(declare-datatype State_CompositionMappingGame_map ((mk-state-CompositionMappingGame-map (state-CompositionMappingGame-map-Input_Map (Array Int (Maybe Int))) (state-CompositionMappingGame-map-Output_Map (Array (Tuple2 Int Bits_*) (Maybe (Tuple2 Int Bits_*)))))))(declare-datatype CompositionState-CompositionMappingGame ((mk-composition-state-CompositionMappingGame (composition-state-CompositionMappingGame-__randomness State_CompositionMappingGame___randomness) (composition-state-CompositionMappingGame-key_top State_CompositionMappingGame_key_top) (composition-state-CompositionMappingGame-key_bottom State_CompositionMappingGame_key_bottom) (composition-state-CompositionMappingGame-prf State_CompositionMappingGame_prf) (composition-state-CompositionMappingGame-map State_CompositionMappingGame_map))))(declare-datatype Return_CompositionMappingGame_key_top_GET ((mk-return-CompositionMappingGame-key_top-GET (return-CompositionMappingGame-key_top-GET-state CompositionState-CompositionMappingGame) (return-CompositionMappingGame-key_top-GET-value Bits_n)) (mk-abort-CompositionMappingGame-key_top-GET)))(declare-datatype Return_CompositionMappingGame_key_top_SET ((mk-return-CompositionMappingGame-key_top-SET (return-CompositionMappingGame-key_top-SET-state CompositionState-CompositionMappingGame) (return-CompositionMappingGame-key_top-SET-value Int)) (mk-abort-CompositionMappingGame-key_top-SET)))(declare-datatype Return_CompositionMappingGame_key_bottom_GET ((mk-return-CompositionMappingGame-key_bottom-GET (return-CompositionMappingGame-key_bottom-GET-state CompositionState-CompositionMappingGame) (return-CompositionMappingGame-key_bottom-GET-value Bits_n)) (mk-abort-CompositionMappingGame-key_bottom-GET)))(declare-datatype Return_CompositionMappingGame_key_bottom_SET ((mk-return-CompositionMappingGame-key_bottom-SET (return-CompositionMappingGame-key_bottom-SET-state CompositionState-CompositionMappingGame) (return-CompositionMappingGame-key_bottom-SET-value (Tuple2 Int Bits_*))) (mk-abort-CompositionMappingGame-key_bottom-SET)))(declare-datatype Return_CompositionMappingGame_prf_EVAL ((mk-return-CompositionMappingGame-prf-EVAL (return-CompositionMappingGame-prf-EVAL-state CompositionState-CompositionMappingGame) (return-CompositionMappingGame-prf-EVAL-value (Tuple2 Int Bits_*))) (mk-abort-CompositionMappingGame-prf-EVAL)))(declare-datatype Return_CompositionMappingGame_map_EVAL ((mk-return-CompositionMappingGame-map-EVAL (return-CompositionMappingGame-map-EVAL-state CompositionState-CompositionMappingGame) (return-CompositionMappingGame-map-EVAL-value (Tuple2 Int Bits_*))) (mk-abort-CompositionMappingGame-map-EVAL)))(declare-datatype Return_CompositionMappingGame_map_SET ((mk-return-CompositionMappingGame-map-SET (return-CompositionMappingGame-map-SET-state CompositionState-CompositionMappingGame) (return-CompositionMappingGame-map-SET-value Int)) (mk-abort-CompositionMappingGame-map-SET)))(declare-datatype Return_CompositionMappingGame_map_GET ((mk-return-CompositionMappingGame-map-GET (return-CompositionMappingGame-map-GET-state CompositionState-CompositionMappingGame) (return-CompositionMappingGame-map-GET-value Bits_n)) (mk-abort-CompositionMappingGame-map-GET))); Composition of CompositionMappingGame
(define-fun oracle-CompositionMappingGame-key_top-GET ((__global_state CompositionState-CompositionMappingGame) (h Int)) Return_CompositionMappingGame_key_top_GET (let ((__self_state (composition-state-CompositionMappingGame-key_top __global_state))) (ite (not (= (select (state-CompositionMappingGame-key_top-T __self_state) h) (as mk-none (Maybe Bits_n)))) (ite ((_ is (mk-none () (Maybe Bits_n))) (select (state-CompositionMappingGame-key_top-T __self_state) h)) mk-abort-CompositionMappingGame-key_top-GET (let ((unwrap-1 (maybe-get (select (state-CompositionMappingGame-key_top-T __self_state) h)))) (let ((k unwrap-1)) (let ((__global_state (mk-composition-state-CompositionMappingGame (composition-state-CompositionMappingGame-__randomness __global_state) __self_state (composition-state-CompositionMappingGame-key_bottom __global_state) (composition-state-CompositionMappingGame-prf __global_state) (composition-state-CompositionMappingGame-map __global_state)))) (mk-return-CompositionMappingGame-key_top-GET __global_state k))))) mk-abort-CompositionMappingGame-key_top-GET)))
(define-fun oracle-CompositionMappingGame-key_top-SET ((__global_state CompositionState-CompositionMappingGame) (h Int) (k Bits_n)) Return_CompositionMappingGame_key_top_SET (let ((__self_state (composition-state-CompositionMappingGame-key_top __global_state))) (ite (= (select (state-CompositionMappingGame-key_top-T __self_state) h) (as mk-none (Maybe Bits_n))) (let ((hh (as mk-none (Maybe Int)))) (let ((kk (__sample-rand-CompositionMappingGame (state-CompositionMappingGame-__randomness-ctr (composition-state-CompositionMappingGame-__randomness __global_state))))) (let ((__global_state (mk-composition-state-CompositionMappingGame (mk-state-CompositionMappingGame-__randomness (+ 1 (state-CompositionMappingGame-__randomness-ctr (composition-state-CompositionMappingGame-__randomness __global_state)))) (composition-state-CompositionMappingGame-key_top __global_state) (composition-state-CompositionMappingGame-key_bottom __global_state) (composition-state-CompositionMappingGame-prf __global_state) (composition-state-CompositionMappingGame-map __global_state)))) (ite (not (= (select (state-CompositionMappingGame-key_top-S __self_state) kk) (as mk-none (Maybe Int)))) (let ((hh (select (state-CompositionMappingGame-key_top-S __self_state) kk))) (ite ((_ is (mk-none () (Maybe Int))) hh) mk-abort-CompositionMappingGame-key_top-SET (let ((unwrap-1 (maybe-get hh))) (let ((hh_ unwrap-1)) (let ((__global_state (mk-composition-state-CompositionMappingGame (composition-state-CompositionMappingGame-__randomness __global_state) __self_state (composition-state-CompositionMappingGame-key_bottom __global_state) (composition-state-CompositionMappingGame-prf __global_state) (composition-state-CompositionMappingGame-map __global_state)))) (mk-return-CompositionMappingGame-key_top-SET __global_state hh_)))))) (let ((__self_state (mk-state-CompositionMappingGame-key_top (store (state-CompositionMappingGame-key_top-T __self_state) h (mk-some kk)) (state-CompositionMappingGame-key_top-S __self_state)))) (let ((__self_state (mk-state-CompositionMappingGame-key_top (state-CompositionMappingGame-key_top-T __self_state) (store (state-CompositionMappingGame-key_top-S __self_state) kk (mk-some h))))) (let ((hh (mk-some h))) (ite ((_ is (mk-none () (Maybe Int))) hh) mk-abort-CompositionMappingGame-key_top-SET (let ((unwrap-1 (maybe-get hh))) (let ((hh_ unwrap-1)) (let ((__global_state (mk-composition-state-CompositionMappingGame (composition-state-CompositionMappingGame-__randomness __global_state) __self_state (composition-state-CompositionMappingGame-key_bottom __global_state) (composition-state-CompositionMappingGame-prf __global_state) (composition-state-CompositionMappingGame-map __global_state)))) (mk-return-CompositionMappingGame-key_top-SET __global_state hh_)))))))))))) mk-abort-CompositionMappingGame-key_top-SET)))
(define-fun oracle-CompositionMappingGame-key_bottom-GET ((__global_state CompositionState-CompositionMappingGame) (h Int) (m Bits_*)) Return_CompositionMappingGame_key_bottom_GET (let ((__self_state (composition-state-CompositionMappingGame-key_bottom __global_state))) (ite (not (= (select (state-CompositionMappingGame-key_bottom-T __self_state) (mk-tuple2 h m)) (as mk-none (Maybe Bits_n)))) (ite ((_ is (mk-none () (Maybe Bits_n))) (select (state-CompositionMappingGame-key_bottom-T __self_state) (mk-tuple2 h m))) mk-abort-CompositionMappingGame-key_bottom-GET (let ((unwrap-1 (maybe-get (select (state-CompositionMappingGame-key_bottom-T __self_state) (mk-tuple2 h m))))) (let ((k unwrap-1)) (let ((__global_state (mk-composition-state-CompositionMappingGame (composition-state-CompositionMappingGame-__randomness __global_state) (composition-state-CompositionMappingGame-key_top __global_state) __self_state (composition-state-CompositionMappingGame-prf __global_state) (composition-state-CompositionMappingGame-map __global_state)))) (mk-return-CompositionMappingGame-key_bottom-GET __global_state k))))) mk-abort-CompositionMappingGame-key_bottom-GET)))
(define-fun oracle-CompositionMappingGame-key_bottom-SET ((__global_state CompositionState-CompositionMappingGame) (h (Tuple2 Int Bits_*)) (k Bits_n)) Return_CompositionMappingGame_key_bottom_SET (let ((__self_state (composition-state-CompositionMappingGame-key_bottom __global_state))) (ite (= (select (state-CompositionMappingGame-key_bottom-T __self_state) h) (as mk-none (Maybe Bits_n))) (let ((__self_state (mk-state-CompositionMappingGame-key_bottom (store (state-CompositionMappingGame-key_bottom-T __self_state) h (mk-some k))))) (let ((__global_state (mk-composition-state-CompositionMappingGame (composition-state-CompositionMappingGame-__randomness __global_state) (composition-state-CompositionMappingGame-key_top __global_state) __self_state (composition-state-CompositionMappingGame-prf __global_state) (composition-state-CompositionMappingGame-map __global_state)))) (mk-return-CompositionMappingGame-key_bottom-SET __global_state h))) mk-abort-CompositionMappingGame-key_bottom-SET)))
(define-fun oracle-CompositionMappingGame-prf-EVAL ((__global_state CompositionState-CompositionMappingGame) (h Int) (m Bits_*)) Return_CompositionMappingGame_prf_EVAL (let ((__self_state (composition-state-CompositionMappingGame-prf __global_state))) (let ((__ret (oracle-CompositionMappingGame-key_top-GET __global_state h))) (ite ((_ is mk-abort-CompositionMappingGame-key_top-GET) __ret) mk-abort-CompositionMappingGame-prf-EVAL (let ((__global_state (return-CompositionMappingGame-key_top-GET-state __ret)) (k (return-CompositionMappingGame-key_top-GET-value __ret))) (let ((y (f k m))) (let ((hh (mk-tuple2 h m))) (let ((__ret (oracle-CompositionMappingGame-key_bottom-SET __global_state hh y))) (ite ((_ is mk-abort-CompositionMappingGame-key_bottom-SET) __ret) mk-abort-CompositionMappingGame-prf-EVAL (let ((__global_state (return-CompositionMappingGame-key_bottom-SET-state __ret)) (_ (return-CompositionMappingGame-key_bottom-SET-value __ret))) (let ((__global_state (mk-composition-state-CompositionMappingGame (composition-state-CompositionMappingGame-__randomness __global_state) (composition-state-CompositionMappingGame-key_top __global_state) (composition-state-CompositionMappingGame-key_bottom __global_state) __self_state (composition-state-CompositionMappingGame-map __global_state)))) (mk-return-CompositionMappingGame-prf-EVAL __global_state hh))))))))))))
(define-fun oracle-CompositionMappingGame-map-EVAL ((__global_state CompositionState-CompositionMappingGame) (h Int) (m Bits_*)) Return_CompositionMappingGame_map_EVAL (let ((__self_state (composition-state-CompositionMappingGame-map __global_state))) (ite (not (= (select (state-CompositionMappingGame-map-Input_Map __self_state) h) (as mk-none (Maybe Int)))) (ite (not (= (select (state-CompositionMappingGame-map-Output_Map __self_state) (mk-tuple2 h m)) (as mk-none (Maybe (Tuple2 Int Bits_*))))) (ite ((_ is (mk-none () (Maybe (Tuple2 Int Bits_*)))) (select (state-CompositionMappingGame-map-Output_Map __self_state) (mk-tuple2 h m))) mk-abort-CompositionMappingGame-map-EVAL (let ((unwrap-1 (maybe-get (select (state-CompositionMappingGame-map-Output_Map __self_state) (mk-tuple2 h m))))) (let ((hhh unwrap-1)) (let ((__global_state (mk-composition-state-CompositionMappingGame (composition-state-CompositionMappingGame-__randomness __global_state) (composition-state-CompositionMappingGame-key_top __global_state) (composition-state-CompositionMappingGame-key_bottom __global_state) (composition-state-CompositionMappingGame-prf __global_state) __self_state))) (mk-return-CompositionMappingGame-map-EVAL __global_state hhh))))) (ite ((_ is (mk-none () (Maybe Int))) (select (state-CompositionMappingGame-map-Input_Map __self_state) h)) mk-abort-CompositionMappingGame-map-EVAL (let ((unwrap-2 (maybe-get (select (state-CompositionMappingGame-map-Input_Map __self_state) h)))) (let ((hhh unwrap-2)) (let ((__ret (oracle-CompositionMappingGame-prf-EVAL __global_state hhh m))) (ite ((_ is mk-abort-CompositionMappingGame-prf-EVAL) __ret) mk-abort-CompositionMappingGame-map-EVAL (let ((__global_state (return-CompositionMappingGame-prf-EVAL-state __ret)) (hh (return-CompositionMappingGame-prf-EVAL-value __ret))) (let ((__self_state (mk-state-CompositionMappingGame-map (state-CompositionMappingGame-map-Input_Map __self_state) (store (state-CompositionMappingGame-map-Output_Map __self_state) (mk-tuple2 h m) (mk-some hh))))) (ite ((_ is (mk-none () (Maybe (Tuple2 Int Bits_*)))) (select (state-CompositionMappingGame-map-Output_Map __self_state) (mk-tuple2 h m))) mk-abort-CompositionMappingGame-map-EVAL (let ((unwrap-3 (maybe-get (select (state-CompositionMappingGame-map-Output_Map __self_state) (mk-tuple2 h m))))) (let ((hhhh unwrap-3)) (let ((__global_state (mk-composition-state-CompositionMappingGame (composition-state-CompositionMappingGame-__randomness __global_state) (composition-state-CompositionMappingGame-key_top __global_state) (composition-state-CompositionMappingGame-key_bottom __global_state) (composition-state-CompositionMappingGame-prf __global_state) __self_state))) (mk-return-CompositionMappingGame-map-EVAL __global_state hhhh))))))))))))) mk-abort-CompositionMappingGame-map-EVAL)))
(define-fun oracle-CompositionMappingGame-map-SET ((__global_state CompositionState-CompositionMappingGame) (h Int) (k Bits_n)) Return_CompositionMappingGame_map_SET (let ((__self_state (composition-state-CompositionMappingGame-map __global_state))) (let ((__ret (oracle-CompositionMappingGame-key_top-SET __global_state h k))) (ite ((_ is mk-abort-CompositionMappingGame-key_top-SET) __ret) mk-abort-CompositionMappingGame-map-SET (let ((__global_state (return-CompositionMappingGame-key_top-SET-state __ret)) (hh (return-CompositionMappingGame-key_top-SET-value __ret))) (ite (= (select (state-CompositionMappingGame-map-Input_Map __self_state) h) (as mk-none (Maybe Int))) (let ((__self_state (mk-state-CompositionMappingGame-map (store (state-CompositionMappingGame-map-Input_Map __self_state) h (mk-some hh)) (state-CompositionMappingGame-map-Output_Map __self_state)))) (let ((__global_state (mk-composition-state-CompositionMappingGame (composition-state-CompositionMappingGame-__randomness __global_state) (composition-state-CompositionMappingGame-key_top __global_state) (composition-state-CompositionMappingGame-key_bottom __global_state) (composition-state-CompositionMappingGame-prf __global_state) __self_state))) (mk-return-CompositionMappingGame-map-SET __global_state hh))) (let ((__global_state (mk-composition-state-CompositionMappingGame (composition-state-CompositionMappingGame-__randomness __global_state) (composition-state-CompositionMappingGame-key_top __global_state) (composition-state-CompositionMappingGame-key_bottom __global_state) (composition-state-CompositionMappingGame-prf __global_state) __self_state))) (mk-return-CompositionMappingGame-map-SET __global_state hh))))))))
(define-fun oracle-CompositionMappingGame-map-GET ((__global_state CompositionState-CompositionMappingGame) (h Int) (m Bits_*)) Return_CompositionMappingGame_map_GET (let ((__self_state (composition-state-CompositionMappingGame-map __global_state))) (ite (not (= (select (state-CompositionMappingGame-map-Output_Map __self_state) (mk-tuple2 h m)) (as mk-none (Maybe (Tuple2 Int Bits_*))))) (ite ((_ is (mk-none () (Maybe (Tuple2 Int Bits_*)))) (select (state-CompositionMappingGame-map-Output_Map __self_state) (mk-tuple2 h m))) mk-abort-CompositionMappingGame-map-GET (let ((unwrap-1 (maybe-get (select (state-CompositionMappingGame-map-Output_Map __self_state) (mk-tuple2 h m))))) (let ((hh unwrap-1)) (let ((hhh (el1 hh)) (mmm (el2 hh))) (let ((__ret (oracle-CompositionMappingGame-key_bottom-GET __global_state hhh mmm))) (ite ((_ is mk-abort-CompositionMappingGame-key_bottom-GET) __ret) mk-abort-CompositionMappingGame-map-GET (let ((__global_state (return-CompositionMappingGame-key_bottom-GET-state __ret)) (k (return-CompositionMappingGame-key_bottom-GET-value __ret))) (let ((__global_state (mk-composition-state-CompositionMappingGame (composition-state-CompositionMappingGame-__randomness __global_state) (composition-state-CompositionMappingGame-key_top __global_state) (composition-state-CompositionMappingGame-key_bottom __global_state) (composition-state-CompositionMappingGame-prf __global_state) __self_state))) (mk-return-CompositionMappingGame-map-GET __global_state k))))))))) mk-abort-CompositionMappingGame-map-GET)))

; define invariant on s-left,s-right
; Internet sais that declare-fun + assert might help Z3 more than define-fun, because define-fun is a pure macro.
;
(declare-fun inv (CompositionState-CompositionNoMappingGame ; function input 
                  CompositionState-CompositionMappingGame) Bool)

(assert (forall 
        (
         (s-left  CompositionState-CompositionNoMappingGame) ; function input 
         (s-right CompositionState-CompositionMappingGame)
        )
        (= (inv s-left s-right)
             (
        let  (
            (bot (as mk-none (Maybe Bits_n)))
            (botint (as mk-none (Maybe Int))) 
            (botstuff (as mk-none (Maybe (Tuple2 Int Bits_*))))
             )

             ( 
;            (TIKL (Array Int               Bits_n))   ;      TIKL: T in output (bottom) key package left
;            (TIKR (Array Int               Bits_n))   ;      TIKR: T in output (bottom) key package right
;            (TOKL (Array (Tuple2 Int Bits_*) Bits_n)) ;      TOKL: T in output (bottom) key package left
;            (TOKR (Array (Tuple2 Int Bits_*) Bits_n)) ;      TOKR: T in output (bottom) key package right
;            (MIR  (Array Int Int))                    ;      MIR : input- mapping table (right)
;            (MOR  (Array (Tuple2 Int Bits_*) 
;                         (Tuple2 Int Bits_*)))        ;      MOR : output- mapping table (right)
  
                ; assignment of randomness state
                    let ((r-left (state-CompositionNoMappingGame-__randomness-ctr
                            (composition-state-CompositionNoMappingGame-__randomness 
                             s-left)))
                         (r-right (state-CompositionMappingGame-__randomness-ctr
                            (composition-state-CompositionMappingGame-__randomness 
                             s-right)))

                ; assignment of tables
                         (TIKL (state-CompositionNoMappingGame-key_top-T
                            (composition-state-CompositionNoMappingGame-key_top 
                             s-left)))
                         (TIKR (state-CompositionMappingGame-key_top-T 
                            (composition-state-CompositionMappingGame-key_top
                             s-right)))
                         (TOKL (state-CompositionNoMappingGame-key_bottom-T
                            (composition-state-CompositionNoMappingGame-key_bottom 
                            s-left)))
                         (TOKR (state-CompositionMappingGame-key_bottom-T
                            (composition-state-CompositionMappingGame-key_bottom
                            s-right)))
                         (MIR  (state-CompositionMappingGame-map-Input_Map
                            (composition-state-CompositionMappingGame-map
                             s-right)))
                         (MOR  (state-CompositionMappingGame-map-Output_Map  
                            (composition-state-CompositionMappingGame-map
                             s-right)))
                )
                (ite
                (and
                ; randomness is the same
                    (= r-left r-right)           
                ; (LRIa)  TIKL[h] = bot => MIR[h]  = bot 
                    (forall ((h Int)) (=> (= (TIKL h) bot) (= (MIR h) botint))) 
                ; (LRIa') MIR[h]  = bot => TIKL[h]    
                    (forall ((h Int)) (=>  (= (MIR h) botint) (= (TIKR h) bot))) 
                ; (LRIb)  MIR [h] = (hh Int) => TIKL[h] = TIKR[hh]         
                    (forall ((h Int) (hh  Int)) 
                                     (
                                     =>  (= (MIR h) (mk-some hh))  (= (TIKL h) (TIKR hh)) 
                                     )
                    ) 
                ; (LROa)  TOKL[h] = bot => MOR[h]  = bot
                    (forall ((h (Tuple2 Int Bits_*))) 
                                      (=> (= (TOKL h) bot) (= (MOR h) botstuff)))
                ; (LROa') MOR[h]  = bot => TOKL[h]  = bot 
                    (forall ((h (Tuple2 Int Bits_*))) 
                                      (=> (= (MOR h) botstuff) (= (TOKR h) bot)))            
                ; (LROb)  MOR [h] = hh  => TOKL[h] = TOKR[hh]         
                    (forall ((h (Tuple2 Int Bits_*)) (hh (Tuple2 Int Bits_*)))
                                     (=>
                                     (= (MOR h) (mk-some hh))                                     
                                     (= (TOKL h) (TOKR hh))))
                ; (RI)  (exists h s.t. MIR[h] = h') => TIKR[h'] != bot
                    (forall ((hh Int)(h Int)) 
                                     (=> 
                                     (= (MIR h) (mk-some hh)) ; if MIR[h] = hh: Int (that is, not bot) 
                                     (not (=  (TIKR hh) bot) ; then TIKR[hh] neq bot
                                              )))
                ; (RI') TIKR[h'] != bot => (exists h s.t. MIR[h] = h')
                    (forall ((hh Int)) 
                                     (=> 
                                     (not (=  (TIKR hh) bot))
                                     (
                                     exists ((h Int))
                                     (= (MIR h) (mk-some hh)) 
                                     )))
                ; (RO)  (exists h s.t. MOR[h] = hh) => exists (hhh Int) TOKR[hh] = hhh
                    (forall ((hh (Tuple2 Int Bits_*))) 
                                     (=> 
                                     (
                                     exists ((h (Tuple2 Int Bits_*)))
                                     (= (MOR h) (mk-some hh))
                                     )
                                     (
                                     exists ((hhh Bits_n))
                                     (= (TOKR hh) (mk-some hhh))
                                     )
                                     ))
                ; (RO') TOKR[hh] = (k Bits_n)) => (exists h s.t. MOR[h] = hh)
                    (forall ((hh (Tuple2 Int Bits_*))(k Bits_n)) 
                                     (=> 
                                     (=  (TOKR hh) (mk-some k)
                                     )
                                     (exists ((h (Tuple2 Int Bits_*)))
                                     (= (MOR h) (mk-some hh))
                                     )
                                     )
                    )
            )
            true
            false
            )))
     )
))




;;;;;;;;;; GET oracle
; existential quantification
(assert (and (exists 
               (
               (s-left-old CompositionState-CompositionNoMappingGame)
               (s-right-old CompositionState-CompositionMappingGame)   
               ; These two lines change from oracle to oracle
               (h Int) 
               (m Bits_*)
               )
(and
; pre-condition
    (= true (inv s-left-old s-right-old))     
    (forall ((n Int)) (= (__sample-rand-CompositionNoMappingGame n) (__sample-rand-CompositionMappingGame n)))    

; assignment after execution
      ;The following 6 lines changes from oracle to oracle:
      (let ((left-new     (oracle-CompositionNoMappingGame-key_bottom-GET s-left-old h m))) ; left function on left state
      (let ((s-left-new   (return-CompositionNoMappingGame-key_bottom-GET-state left-new)))
      (let ((y-left-new   (return-CompositionNoMappingGame-key_bottom-GET-value left-new)))
      (let ((right-new    (oracle-CompositionMappingGame-map-GET s-right-old h m))) ; right function on right state     
      (let ((s-right-new  (return-CompositionMappingGame-map-GET-state right-new)))
      (let ((y-right-new  (return-CompositionMappingGame-map-GET-value right-new)))

; not both abort
(and
(not (= mk-abort-CompositionNoMappingGame-key_bottom-GET left-new))
(not (= mk-abort-CompositionMappingGame-map-GET right-new))
)

; post-condtion
   (not (or
      (= true (inv s-left-new s-right-new))  ; undefined stuff 
      (= y-left-new y-right-new )  ; undefined stuff 
))
)
)))
      ))))))




(check-sat)
;(get-model)
