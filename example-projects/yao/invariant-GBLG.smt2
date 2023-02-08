(declare-const randval-left-9+1 Bits_n)
(assert (= randval-left-9+1 (__sample-rand-Left-Bits_n 9 (+ 1 randctr-left-9)
)))

(declare-const randval-left-9+2 Bits_n)
(assert (= randval-left-9+2 (__sample-rand-Left-Bits_n 9 (+ 2 randctr-left-9)
)))

(declare-const randval-left-9+3 Bits_n)
(assert (= randval-left-9+3 (__sample-rand-Left-Bits_n 9 (+ 3 randctr-left-9)
)))

(declare-const randval-left-11+1 Bits_n)
(assert (= randval-left-11+1 (__sample-rand-Left-Bits_n 11 (+ 1 randctr-left-11)
)))

(declare-const randval-left-11+2 Bits_n)
(assert (= randval-left-11+2 (__sample-rand-Left-Bits_n 11 (+ 2 randctr-left-11)
)))

(declare-const randval-left-11+3 Bits_n)
(assert (= randval-left-11+3 (__sample-rand-Left-Bits_n 11 (+ 3 randctr-left-11)
)))


(define-fun randomness-mapping-GBLG () Bool
(and
;equality of values of the sample functions for the lower Key package
(= randval-left-5    randval-right-7)
(= randval-left-6    randval-right-8)

;equality of values of the sample functions for the encryptions
(= randval-left-9    randval-right-9)
(= randval-left-11   randval-right-10)
(= randval-left-9+1  randval-right-11)
(= randval-left-11+1 randval-right-12)
(= randval-left-9+2  randval-right-11)
(= randval-left-11+2 randval-right-12)
(= randval-left-9+3  randval-right-13)
(= randval-left-11+3 randval-right-14)
)
)

; special-purpose glue for this particular project
(assert
(and
              ;op should be total
(not (= (select arg-GBLG-op (mk-tuple2 true  true ))(as mk-none (Maybe Bool))))
(not (= (select arg-GBLG-op (mk-tuple2 true  false))(as mk-none (Maybe Bool))))
(not (= (select arg-GBLG-op (mk-tuple2 false true ))(as mk-none (Maybe Bool))))
(not (= (select arg-GBLG-op (mk-tuple2 false false))(as mk-none (Maybe Bool))))
))

(declare-datatype
  State_keys
  (
    (mk-state-keys
      (state-keys-T (Array Int (Maybe (Array Bool (Maybe Bits_n)))))
      (state-keys-z (Array Int (Maybe Bool)))
      (state-keys-flag (Array Int (Maybe Bool))))))

(define-fun project-State_Left_keys_top ((in State_Left_keys_top)) State_keys
  (mk-state-keys (state-Left-keys_top-T    in)
                 (state-Left-keys_top-z    in)
                 (state-Left-keys_top-flag in)))

(define-fun project-State_Right_keys_top ((in State_Right_keys_top)) State_keys
  (mk-state-keys (state-Right-keys_top-T    in)
                 (state-Right-keys_top-z    in)
                 (state-Right-keys_top-flag in)))

(define-fun project-State_Left_keys_bottom ((in State_Left_keys_bottom)) State_keys
  (mk-state-keys (state-Left-keys_bottom-T    in)
                 (state-Left-keys_bottom-z    in)
                 (state-Left-keys_bottom-flag in)))

(define-fun project-State_Right_keys_bottom ((in State_Right_keys_bottom)) State_keys
  (mk-state-keys (state-Right-keys_bottom-T    in)
                 (state-Right-keys_bottom-z    in)
                 (state-Right-keys_bottom-flag in)))

; catches corner cases of tables
;
; - entries for T are mk-none or a total table (which points to Bits_n and not to none)
;
(define-fun well-defined ((T (Array Int (Maybe (Array Bool (Maybe Bits_n)))))) Bool
  (forall ((h Int))
    (ite
      (not
        (= (select T h) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
      )
      (forall ((b Bool))
        (not
          (= (select (maybe-get (select T h)) b) (as mk-none (Maybe Bits_n)))
        )
      )
      true
    )
  )
)

; captures the possible states which a Key package can be in when
; the "top" queries are GETKEYS queries 
;
(define-fun well-defined-Key-bool ((key-state State_keys)) Bool
(let ((T    (state-keys-T    key-state))
      (flag (state-keys-flag key-state))
      (z    (state-keys-z    key-state)))

; flag is true <=> key has been chosen 
(and

;Key tables in the key packages are either completely defined or completely undefined
(well-defined T)

(forall ((hhh Int)) (=
                    (not (= (select flag hhh) (mk-some true)))
                    (or
                    (= (select T hhh) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
                    (and
                    (= (select (maybe-get (select T hhh)) true) (as mk-none (Maybe Bits_n)))
                    (= (select (maybe-get (select T hhh)) false) (as mk-none (Maybe Bits_n))))
                    )))

; z table is completely undefined
(forall ((hhh Int))
(= (select T hhh) (as mk-none (Maybe (Array Bool (Maybe Bits_n))))

)
)
)))

; captures the possible states which a Key package can be in when
; the "top" queries are GETA and SETBIT queries 
;
(define-fun well-defined-Key-active ((key-state State_keys)) Bool
(let ((T    (state-keys-T    key-state))
      (flag (state-keys-flag key-state))
      (z    (state-keys-z    key-state)))

(and
; Table entries either bot or well-defined
(well-defined T)

; flag has been set => bit has been set
(forall ((hhh Int)) (ite (=  (mk-some true)  (select flag hhh))  
                (or (=  (mk-some true)  (select z hhh))
                    (=  (mk-some false) (select z hhh)))
                    true
                    ))


; key has been set => flag has been set
(forall ((hhh Int)) (ite
                    (not
                    (or
                    (= (select T hhh) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
                    (= (select (maybe-get (select T hhh)) true) (as mk-none (Maybe Bits_n)))))
                    (not
                    (= (select flag hhh) (as mk-none (Maybe Bool))))
                    true
                    ))
)))

; This is supposed to be an invariant
(define-fun invariant-GBLG          (
        (state-left (Array Int CompositionState-Left))
        (state-right (Array Int CompositionState-Right))
        (state-length-left Int)
        (state-length-right Int)
        (state-left-new Return_Left_gate_GBLG)
        (state-right-new Return_Right_simgate_GBLG)
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
    Bool
    (let

; state of the key packages
(
(top-key-package-left (project-State_Left_keys_top          (composition-pkgstate-Left-keys_top     (select state-left state-length-left-old))))
(top-key-package-right (project-State_Right_keys_top        (composition-pkgstate-Right-keys_top    (select state-right state-length-right-old))))
(bottom-key-package-left (project-State_Left_keys_bottom    (composition-pkgstate-Left-keys_bottom  (select state-left state-length-left-old))))
(bottom-key-package-right (project-State_Right_keys_bottom  (composition-pkgstate-Right-keys_bottom (select state-right state-length-right-old))))
)

(let

; table of the bottom key package
(
(table-bottom-left (state-keys-T bottom-key-package-left))
(table-bottom-right (state-keys-T bottom-key-package-right))
)

(and
;top key package states are equal
(= top-key-package-left top-key-package-right)

;for bottom key package, tables are equal
(= table-bottom-left table-bottom-right)

;top key packages behave like a key packages
(well-defined-Key-active top-key-package-left)
(well-defined-Key-active top-key-package-right)

;bottom key packages behave like a key packages
(well-defined-Key-bool bottom-key-package-left)
(well-defined-Key-active bottom-key-package-right)

;no abort
;(not (return-Right-simgate-GBLG-is-abort state-right-new))
;(not (return-Left-gate-GBLG-is-abort state-left-new))


))))


(assert
(and
(= state-length-left-old 1)
(= state-length-right-old 1)
)
)


;;;;;;;;;; Lemmas


(define-fun top-whole-left-neu-right-neu          (
        (state-left (Array Int CompositionState-Left))
        (state-right (Array Int CompositionState-Right))
        (state-length-left Int)
        (state-length-right Int)
        (state-left-NEU Return_Left_gate_GBLG)
        (state-right-NEU Return_Right_simgate_GBLG)
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool


    (let (
      (state-left-neu (select   (return-Left-gate-GBLG-state state-left-NEU)
                                (return-Left-gate-GBLG-state-length state-left-NEU)))
      (state-right-neu (select  (return-Right-simgate-GBLG-state state-right-NEU)
                                (return-Right-simgate-GBLG-state-length state-right-NEU)))
    )

  (let

; state of the key packages
(
(top-key-package-left-neu  (project-State_Left_keys_top  (composition-pkgstate-Left-keys_top  state-left-neu)))
(top-key-package-right-neu (project-State_Right_keys_top (composition-pkgstate-Right-keys_top state-right-neu)))
(bottom-key-package-left-neu  (project-State_Left_keys_bottom (composition-pkgstate-Left-keys_bottom state-left-neu)))
(bottom-key-package-right-neu (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-neu)))
)


;;; top key packages have equal state
(= top-key-package-left-neu top-key-package-right-neu)


)))

(define-fun bot-table-left-alt-left-1
          (
        (state-left (Array Int CompositionState-Left))
        (state-right (Array Int CompositionState-Right))
        (state-length-left Int)
        (state-length-right Int)
        (state-left-NEU Return_Left_gate_GBLG)
        (state-right-NEU Return_Right_simgate_GBLG)
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool


    (let (
      (state-left-1  (select  (return-Left-gate-GBLG-state state-left-NEU)
                                ;(return-Left-gate-GBLG-state-length state-left-NEU)
                                1))
      (state-right-1 (select  (return-Right-simgate-GBLG-state state-right-NEU)
                                ;(return-Right-simgate-GBLG-state-length state-right-NEU)
                                1))
    )

  (let

; state of the key packages
(
(bottom-key-package-left-alt  (project-State_Left_keys_bottom (composition-pkgstate-Left-keys_bottom (select state-left state-length-left-old))))
(bottom-key-package-right-alt  (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom (select state-right state-length-right-old))))
(bottom-key-package-left-1  (project-State_Left_keys_bottom (composition-pkgstate-Left-keys_bottom state-left-1)))
(bottom-key-package-right-1 (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-1)))
)

;; bottom key packages have equal state
(and
(= bottom-key-package-left-1 bottom-key-package-left-alt)
)

)))


(define-fun bot-table-right-alt-right-1
          (
        (state-left (Array Int CompositionState-Left))
        (state-right (Array Int CompositionState-Right))
        (state-length-left Int)
        (state-length-right Int)
        (state-left-NEU Return_Left_gate_GBLG)
        (state-right-NEU Return_Right_simgate_GBLG)
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool


    (let (
      (state-left-1  (select  (return-Left-gate-GBLG-state state-left-NEU)
                                ;(return-Left-gate-GBLG-state-length state-left-NEU)
                                1))
      (state-right-1 (select  (return-Right-simgate-GBLG-state state-right-NEU)
                                ;(return-Right-simgate-GBLG-state-length state-right-NEU)
                                1))
    )

  (let

; state of the key packages
(
(bottom-key-package-left-alt  (project-State_Left_keys_bottom (composition-pkgstate-Left-keys_bottom (select state-left state-length-left-old))))
(bottom-key-package-right-alt  (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom (select state-right state-length-right-old))))
(bottom-key-package-left-1  (project-State_Left_keys_bottom (composition-pkgstate-Left-keys_bottom state-left-1)))
(bottom-key-package-right-1 (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-1)))
)

;; bottom key packages have equal state
(and
(= bottom-key-package-left-1 bottom-key-package-left-alt)
(= bottom-key-package-right-1 bottom-key-package-right-alt)
)

)))

(define-fun well-bot-left-NEU          (
        (state-left (Array Int CompositionState-Left))
        (state-right (Array Int CompositionState-Right))
        (state-length-left Int)
        (state-length-right Int)
        (state-left-NEU Return_Left_gate_GBLG)
        (state-right-NEU Return_Right_simgate_GBLG)
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool


    (let (
;      (state-left-1 (select  (return-Left-gate-GBLG-state state-left-NEU)
;                  1))
;      (state-left-2 (select  (return-Left-gate-GBLG-state state-left-NEU)
;                  2))
;      (state-left-3 (select  (return-Left-gate-GBLG-state state-left-NEU)
;                  3))
;      (state-left-4 (select  (return-Left-gate-GBLG-state state-left-NEU)
;                  4))
;      (state-left-5 (select  (return-Left-gate-GBLG-state state-left-NEU)
;                  5))
;      (state-left-6 (select  (return-Left-gate-GBLG-state state-left-NEU)
;                  6))
;      (state-left-7 (select  (return-Left-gate-GBLG-state state-left-NEU)
;                  7))
;      (state-left-8 (select  (return-Left-gate-GBLG-state state-left-NEU)
;                  8))
;      (state-left-9 (select  (return-Left-gate-GBLG-state state-left-NEU)
;                  9))
;      (state-left-10 (select  (return-Left-gate-GBLG-state state-left-NEU)
;                  10))
;      (state-left-11 (select  (return-Left-gate-GBLG-state state-left-NEU)
;                  11))
;      (state-left-12 (select  (return-Left-gate-GBLG-state state-left-NEU)
;                  12))
;      (state-left-13 (select  (return-Left-gate-GBLG-state state-left-NEU)
;                  13))
;      (state-left-14 (select  (return-Left-gate-GBLG-state state-left-NEU)
;                  14))
;      (state-left-15 (select  (return-Left-gate-GBLG-state state-left-NEU)
;                  16))
      (state-left-NEU (select  (return-Left-gate-GBLG-state state-left-NEU)
                  state-length-left))
    )

  (let

; state of the key packages
(
(bottom-key-package-left-NEU  (project-State_Left_keys_bottom (composition-pkgstate-Left-keys_bottom state-left-NEU)))
;(bottom-key-package-right-alt  (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom (select state-right state-length-right))))
)



;;; bot left key package is well-formed
(and
;;; bot left key package is well-formed
(and
;(well-defined-Key-bool bottom-key-package-left-1)
;(well-defined-Key-bool bottom-key-package-left-2)
;(well-defined-Key-bool bottom-key-package-left-3)
;(well-defined-Key-bool bottom-key-package-left-4)
;(well-defined-Key-bool bottom-key-package-left-5)
;(well-defined-Key-bool bottom-key-package-left-6)
;(well-defined-Key-bool bottom-key-package-left-7)
;(well-defined-Key-bool bottom-key-package-left-8)
;(well-defined-Key-bool bottom-key-package-left-9)
;(well-defined-Key-bool bottom-key-package-left-10)
;(well-defined-Key-bool bottom-key-package-left-11)
;(well-defined-Key-bool bottom-key-package-left-12)
;(well-defined-Key-bool bottom-key-package-left-13)
;(well-defined-Key-bool bottom-key-package-left-14)
;(well-defined-Key-bool bottom-key-package-left-15)
(well-defined-Key-bool bottom-key-package-left-NEU)
;(= bottom-key-package-left-2 bottom-key-package-left-1)
;(= bottom-key-package-right-2 bottom-key-package-right-1)
))));(= bottom-key-package-left-2 bottom-key-package-left-1)
;(= bottom-key-package-right-2 bottom-key-package-right-1)
)

(define-fun well-bot-right-NEU          (
        (state-left (Array Int CompositionState-Left))
        (state-right (Array Int CompositionState-Right))
        (state-length-left Int)
        (state-length-right Int)
        (state-left-NEU Return_Left_gate_GBLG)
        (state-right-NEU Return_Right_simgate_GBLG)
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool


    (let (
;      (state-right-1 (select  (return-Right-simgate-GBLG-state state-right-NEU) 
;                   1))
;      (state-right-2 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   2))
;      (state-right-3 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   3))
;      (state-right-4 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   4))
;      (state-right-5 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   5))
;      (state-right-6 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   6))
;      (state-right-7 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   7))
;      (state-right-8 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   8))
;      (state-right-9 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   9))
;      (state-right-10 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   10))
;      (state-right-11 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   11))
;      (state-right-12 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   12))
;      (state-right-13 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   13))
;      (state-right-14 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   14))
;      (state-right-15 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   15))
      (state-right-NEU (select  (return-Right-simgate-GBLG-state state-right-NEU)
                   state-length-right))

    )

  (let

; state of the key packages
(
;(bottom-key-package-right-1    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-1)))
;(bottom-key-package-right-2    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-2)))
;(bottom-key-package-right-3    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-3)))
;(bottom-key-package-right-4    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-4)))
;(bottom-key-package-right-5    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-5)))
;(bottom-key-package-right-6    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-6)))
;(bottom-key-package-right-7    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-7)))
;(bottom-key-package-right-8    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-8)))
;(bottom-key-package-right-9    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-9)))
;(bottom-key-package-right-10    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-10)))
;(bottom-key-package-right-11    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-11)))
;(bottom-key-package-right-12    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-12)))
;(bottom-key-package-right-13    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-13)))
;(bottom-key-package-right-14    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-14)))
;(bottom-key-package-right-15    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-15)))
(bottom-key-package-right-NEU  (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-NEU)))
;(bottom-key-package-right-alt  (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom (select state-right state-length-right))))
)



;;; bot right key package is well-formed
(and
;(well-defined-Key-bool bottom-key-package-right-1)
;(well-defined-Key-bool bottom-key-package-right-2)
;(well-defined-Key-bool bottom-key-package-right-3)
;(well-defined-Key-bool bottom-key-package-right-4)
;(well-defined-Key-bool bottom-key-package-right-5)
;(well-defined-Key-bool bottom-key-package-right-6)
;(well-defined-Key-bool bottom-key-package-right-7)
;(well-defined-Key-bool bottom-key-package-right-8)
;(well-defined-Key-bool bottom-key-package-right-9)
;(well-defined-Key-bool bottom-key-package-right-10)
;(well-defined-Key-bool bottom-key-package-right-11)
;(well-defined-Key-bool bottom-key-package-right-12)
;(well-defined-Key-bool bottom-key-package-right-13)
;(well-defined-Key-bool bottom-key-package-right-14)
;(well-defined-Key-bool bottom-key-package-right-15)
(well-defined-Key-active bottom-key-package-right-NEU)
;(= bottom-key-package-left-2 bottom-key-package-left-1)
;(= bottom-key-package-right-2 bottom-key-package-right-1)
))))

(define-fun well-bot-right-1          (
        (state-left (Array Int CompositionState-Left))
        (state-right (Array Int CompositionState-Right))
        (state-length-left Int)
        (state-length-right Int)
        (state-left-NEU Return_Left_gate_GBLG)
        (state-right-NEU Return_Right_simgate_GBLG)
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool


    (let (
      (state-right-1 (select  (return-Right-simgate-GBLG-state state-right-NEU) 
                   1))
;      (state-right-2 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   2))
;      (state-right-3 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   3))
;      (state-right-4 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   4))
;      (state-right-5 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   5))
;      (state-right-6 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   6))
;      (state-right-7 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   7))
;      (state-right-8 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   8))
;      (state-right-9 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   9))
;      (state-right-10 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   10))
;      (state-right-11 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   11))
;      (state-right-12 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   12))
;      (state-right-13 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   13))
;      (state-right-14 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   14))
;      (state-right-15 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   15))
      (state-right-NEU (select  (return-Right-simgate-GBLG-state state-right-NEU)
                   state-length-right))

    )

  (let

; state of the key packages
(
(bottom-key-package-right-1    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-1)))
;(bottom-key-package-right-2    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-2)))
;(bottom-key-package-right-3    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-3)))
;(bottom-key-package-right-4    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-4)))
;(bottom-key-package-right-5    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-5)))
;(bottom-key-package-right-6    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-6)))
;(bottom-key-package-right-7    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-7)))
;(bottom-key-package-right-8    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-8)))
;(bottom-key-package-right-9    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-9)))
;(bottom-key-package-right-10    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-10)))
;(bottom-key-package-right-11    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-11)))
;(bottom-key-package-right-12    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-12)))
;(bottom-key-package-right-13    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-13)))
;(bottom-key-package-right-14    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-14)))
;(bottom-key-package-right-15    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-15)))
(bottom-key-package-right-NEU  (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-NEU)))
;(bottom-key-package-right-alt  (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom (select state-right state-length-right))))
)



;;; bot right key package is defined
(and
(well-defined-Key-active bottom-key-package-right-1)
;(well-defined-Key-bool bottom-key-package-right-NEU)
))))


(define-fun pre-right         (
        (state-left (Array Int CompositionState-Left))
        (state-right (Array Int CompositionState-Right))
        (state-length-left Int)
        (state-length-right Int)
        (state-left-NEU Return_Left_gate_GBLG)
        (state-right-NEU Return_Right_simgate_GBLG)
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool


    (let (
      (state-right-1 (select  (return-Right-simgate-GBLG-state state-right-NEU) 
                   1))
;      (state-right-2 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   2))
;      (state-right-3 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   3))
;      (state-right-4 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   4))
;      (state-right-5 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   5))
;      (state-right-6 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   6))
;      (state-right-7 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   7))
;      (state-right-8 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   8))
;      (state-right-9 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   9))
;      (state-right-10 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   10))
;      (state-right-11 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   11))
;      (state-right-12 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   12))
;      (state-right-13 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   13))
;      (state-right-14 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   14))
;      (state-right-15 (select  (return-Right-simgate-GBLG-state state-right-NEU)
;                   15))
      (state-right-NEU (select  (return-Right-simgate-GBLG-state state-right-NEU)
                   state-length-right))

    )

  (let

; state of the key packages
(
(top-key-package-right-NEU     (project-State_Right_keys_top (composition-pkgstate-Right-keys_top state-right-NEU)))
(top-key-package-right-alt     (project-State_Right_keys_top (composition-pkgstate-Right-keys_top (select state-right state-length-right-old))))
(bottom-key-package-right-alt  (project-State_Right_keys_bottom  (composition-pkgstate-Right-keys_bottom (select state-right state-length-right-old))))
(bottom-key-package-right-1    (project-State_Right_keys_bottom  (composition-pkgstate-Right-keys_bottom state-right-1)))
;(bottom-key-package-right-2    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-2)))
;(bottom-key-package-right-3    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-3)))
;(bottom-key-package-right-4    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-4)))
;(bottom-key-package-right-5    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-5)))
;(bottom-key-package-right-6    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-6)))
;(bottom-key-package-right-7    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-7)))
;(bottom-key-package-right-8    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-8)))
;(bottom-key-package-right-9    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-9)))
;(bottom-key-package-right-10    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-10)))
;(bottom-key-package-right-11    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-11)))
;(bottom-key-package-right-12    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-12)))
;(bottom-key-package-right-13    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-13)))
;(bottom-key-package-right-14    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-14)))
;(bottom-key-package-right-15    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-15)))
(bottom-key-package-right-NEU  (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-NEU)))
;(bottom-key-package-right-alt  (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom (select state-right state-length-right))))
)



;;; bot right key package is defined
(and
(not (= (select (state-keys-T top-key-package-right-alt) l) (as mk-none (Maybe (Array Bool (Maybe Bits_n))))))
(not (= (select (state-keys-T top-key-package-right-alt) r) (as mk-none (Maybe (Array Bool (Maybe Bits_n))))))
(=      (select (state-keys-T bottom-key-package-right-alt) j) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
;(well-defined-Key-bool bottom-key-package-right-NEU)
))))

(define-fun lemma2-keys-2          (
        (state-left (Array Int CompositionState-Left))
        (state-right (Array Int CompositionState-Right))
        (state-length-left Int)
        (state-length-right Int)
        (state-left-NEU Return_Left_gate_GBLG)
        (state-right-NEU Return_Right_simgate_GBLG)
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool


    (let (
      (state-left-1  (select  (return-Left-gate-GBLG-state state-left-NEU)
                                ;(return-Left-gate-GBLG-state-length state-left-NEU)
                                1))
      (state-right-1 (select  (return-Right-simgate-GBLG-state state-right-NEU)
                                ;(return-Right-simgate-GBLG-state-length state-right-NEU)
                                1))
      (state-left-2  (select  (return-Left-gate-GBLG-state state-left-NEU)
                                ;(return-Left-gate-GBLG-state-length state-left-NEU)
                                2))
      (state-right-2 (select  (return-Right-simgate-GBLG-state state-right-NEU)
                                ;(return-Right-simgate-GBLG-state-length state-right-NEU)
                                2))
      (state-left-3  (select  (return-Left-gate-GBLG-state state-left-NEU)
                                ;(return-Left-gate-GBLG-state-length state-left-NEU)
                                3))
      (state-right-3 (select  (return-Right-simgate-GBLG-state state-right-NEU)
                                ;(return-Right-simgate-GBLG-state-length state-right-NEU)
                                3))
      (state-right-4 (select  (return-Right-simgate-GBLG-state state-right-NEU)
                                ;(return-Right-simgate-GBLG-state-length state-right-NEU)
                                4))
      (state-right-5 (select  (return-Right-simgate-GBLG-state state-right-NEU)
                                ;(return-Right-simgate-GBLG-state-length state-right-NEU)
                                5))
    )

  (let

; state of the key packages
(
(bottom-key-package-left-alt  (project-State_Left_keys_bottom (composition-pkgstate-Left-keys_bottom (select state-left state-length-left-old))))
(bottom-key-package-right-alt  (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom (select state-right state-length-right-old))))
(bottom-key-package-left-1  (project-State_Left_keys_bottom  (composition-pkgstate-Left-keys_bottom state-left-1)))
(bottom-key-package-right-1 (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-1)))
(bottom-key-package-left-2  (project-State_Left_keys_bottom  (composition-pkgstate-Left-keys_bottom state-left-2)))
(bottom-key-package-right-2 (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-2)))
(bottom-key-package-left-3  (project-State_Left_keys_bottom  (composition-pkgstate-Left-keys_bottom state-left-3)))
(bottom-key-package-right-3 (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-3)))
(bottom-key-package-right-4 (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-4)))
(bottom-key-package-right-5 (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-5)))
)



;;; top key packages have equal state
(and
;(= bottom-key-package-left-2 bottom-key-package-left-1)
(= bottom-key-package-right-2 bottom-key-package-right-1)
))))

(define-fun lemma2-keys-3          (
        (state-left (Array Int CompositionState-Left))
        (state-right (Array Int CompositionState-Right))
        (state-length-left Int)
        (state-length-right Int)
        (state-left-NEU Return_Left_gate_GBLG)
        (state-right-NEU Return_Right_simgate_GBLG)
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool


    (let (
      (state-left-1  (select  (return-Left-gate-GBLG-state state-left-NEU)
                                ;(return-Left-gate-GBLG-state-length state-left-NEU)
                                1))
      (state-right-1 (select  (return-Right-simgate-GBLG-state state-right-NEU)
                                ;(return-Right-simgate-GBLG-state-length state-right-NEU)
                                1))
      (state-left-2  (select  (return-Left-gate-GBLG-state state-left-NEU)
                                ;(return-Left-gate-GBLG-state-length state-left-NEU)
                                2))
      (state-right-2 (select  (return-Right-simgate-GBLG-state state-right-NEU)
                                ;(return-Right-simgate-GBLG-state-length state-right-NEU)
                                2))
      (state-left-3  (select  (return-Left-gate-GBLG-state state-left-NEU)
                                ;(return-Left-gate-GBLG-state-length state-left-NEU)
                                3))
      (state-right-3 (select  (return-Right-simgate-GBLG-state state-right-NEU)
                                ;(return-Right-simgate-GBLG-state-length state-right-NEU)
                                3))
      (state-right-4 (select  (return-Right-simgate-GBLG-state state-right-NEU)
                                ;(return-Right-simgate-GBLG-state-length state-right-NEU)
                                4))
      (state-right-5 (select  (return-Right-simgate-GBLG-state state-right-NEU)
                                ;(return-Right-simgate-GBLG-state-length state-right-NEU)
                                5))
    )

  (let

; state of the key packages
(
(bottom-key-package-left-alt   (project-State_Left_keys_bottom  (composition-pkgstate-Left-keys_bottom  (select state-left  state-length-left-old))))
(bottom-key-package-right-alt  (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom (select state-right state-length-right-old))))
(bottom-key-package-left-1     (project-State_Left_keys_bottom  (composition-pkgstate-Left-keys_bottom  state-left-1)))
(bottom-key-package-right-1    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-1)))
(bottom-key-package-left-2     (project-State_Left_keys_bottom  (composition-pkgstate-Left-keys_bottom  state-left-2)))
(bottom-key-package-right-2    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-2)))
(top-key-package-right-2       (project-State_Right_keys_top    (composition-pkgstate-Right-keys_top    state-right-2)))
(bottom-key-package-left-3     (project-State_Left_keys_bottom  (composition-pkgstate-Left-keys_bottom  state-left-3)))
(bottom-key-package-right-3    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-3)))
(bottom-key-package-right-4    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-4)))
(bottom-key-package-right-5    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-5)))
)


(let

; table of the bottom key package
(
(flag-top-right-2 (state-keys-flag top-key-package-right-2))
(T-top-right-2    (state-keys-T top-key-package-right-2))
)



;;; top key packages have equal state
(=>
(and
(= (select flag-top-right-2 l) (mk-some true))
(not (= (select T-top-right-2 l) (as mk-none (Maybe (Array Bool (Maybe Bits_n))))))
)
(= bottom-key-package-right-3 bottom-key-package-right-2)
)))))


(declare-const Z (Array Bool (Maybe Bits_n)))

(define-fun lemma2-left-keys-a          (
        (state-left-alt (Array Int CompositionState-Left))
        (state-right (Array Int CompositionState-Right))
        (state-length-left Int)
        (state-length-right Int)
        (state-left-NEU Return_Left_gate_GBLG)
        (state-right-NEU Return_Right_simgate_GBLG)
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
    Bool


    (let (
      (state-left-neu (select   (return-Left-gate-GBLG-state state-left-NEU)
                                (return-Left-gate-GBLG-state-length state-left-NEU)))
    )

    (let

; state of the key packages
(
(top-key-package-left-alt (project-State_Left_keys_top       (composition-pkgstate-Left-keys_top    (select state-left-alt state-length-left-old))))
(top-key-package-left-neu (project-State_Left_keys_top       (composition-pkgstate-Left-keys_top    state-left-neu)))
(bottom-key-package-left-alt (project-State_Left_keys_bottom (composition-pkgstate-Left-keys_bottom (select state-left-alt state-length-left-old))))
(bottom-key-package-left-neu (project-State_Left_keys_bottom (composition-pkgstate-Left-keys_bottom state-left-neu)))
)

(let

; table of the bottom key package
(
(table-top-left-alt (state-keys-T top-key-package-left-alt))
(table-top-left-neu (state-keys-T top-key-package-left-neu))
(table-bottom-left-alt (state-keys-T bottom-key-package-left-alt))
(table-bottom-left-neu (state-keys-T bottom-key-package-left-neu))
)

(let
(
              ;assignment of the sampled values for the lower Key package as a table
              (Z-left (store (store Z
                    false (mk-some randval-left-6))
                  true (mk-some randval-left-5)))
              
)

;;; bottom key packages equal except for position j
;;; and where there is j, there is the same or Z
(forall ((hh Int))
(=>
(not
(and (= j hh) (= (select table-bottom-left-alt hh) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))))
(= (select table-bottom-left-alt hh) (select table-bottom-left-neu hh))
)))))
    
    ))

(define-fun no-abort (
        (state-left-alt (Array Int CompositionState-Left))
        (state-right (Array Int CompositionState-Right))
        (state-length-left Int)
        (state-length-right Int)
        (state-left-NEU Return_Left_gate_GBLG)
        (state-right-NEU Return_Right_simgate_GBLG)
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
    Bool
      (let
      (
      (abort-left  (return-Left-gate-GBLG-is-abort  state-left-NEU))
      (abort-right (return-Right-simgate-GBLG-is-abort state-right-NEU))
      )
(and
(= abort-left  false)
(= abort-right false)
)))


(define-fun lemma2-left-keys-2          (
        (state-left (Array Int CompositionState-Left))
        (state-right (Array Int CompositionState-Right))
        (state-length-left Int)
        (state-length-right Int)
        (state-left-NEU Return_Left_gate_GBLG)
        (state-right-NEU Return_Right_simgate_GBLG)
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool


    (let (
      (state-left-1  (select  (return-Left-gate-GBLG-state state-left-NEU)
                                ;(return-Left-gate-GBLG-state-length state-left-NEU)
                                1))
      (state-right-1 (select  (return-Right-simgate-GBLG-state state-right-NEU)
                                ;(return-Right-simgate-GBLG-state-length state-right-NEU)
                                1))
      (state-left-2  (select  (return-Left-gate-GBLG-state state-left-NEU)
                                ;(return-Left-gate-GBLG-state-length state-left-NEU)
                                2))
      (state-right-2 (select  (return-Right-simgate-GBLG-state state-right-NEU)
                                ;(return-Right-simgate-GBLG-state-length state-right-NEU)
                                2))
      (state-left-3  (select  (return-Left-gate-GBLG-state state-left-NEU)
                                ;(return-Left-gate-GBLG-state-length state-left-NEU)
                                3))
      (state-right-3 (select  (return-Right-simgate-GBLG-state state-right-NEU)
                                ;(return-Right-simgate-GBLG-state-length state-right-NEU)
                                3))
      (state-right-4 (select  (return-Right-simgate-GBLG-state state-right-NEU)
                                ;(return-Right-simgate-GBLG-state-length state-right-NEU)
                                4))
      (state-right-5 (select  (return-Right-simgate-GBLG-state state-right-NEU)
                                ;(return-Right-simgate-GBLG-state-length state-right-NEU)
                                5))
    )

  (let

; state of the key packages
(
(bottom-key-package-left-alt   (project-State_Left_keys_bottom  (composition-pkgstate-Left-keys_bottom  (select state-left  state-length-left-old))))
(bottom-key-package-right-alt  (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom (select state-right state-length-right-old))))
(bottom-key-package-left-1     (project-State_Left_keys_bottom  (composition-pkgstate-Left-keys_bottom  state-left-1)))
(bottom-key-package-right-1    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-1)))
(bottom-key-package-left-2     (project-State_Left_keys_bottom  (composition-pkgstate-Left-keys_bottom  state-left-2)))
(bottom-key-package-right-2    (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-2)))
)

(let
(
              ;assignment of the sampled values for the lower Key package as a table
              (Z-left (store (store Z
                    false (mk-some randval-left-6))
                  true (mk-some randval-left-5)))
              
)


(let

; table of the bottom key package
(
(flag-bottom-left-1  (state-keys-flag bottom-key-package-left-1))
(T-bottom-left-1     (state-keys-T    bottom-key-package-left-1))
(T-bottom-left-2     (state-keys-T    bottom-key-package-left-2))
)

;;; top key packages have equal state
(=>
(= (select flag-bottom-left-1 j) (mk-some false))
(= (select    T-bottom-left-2 j) (mk-some Z))
))))))




(define-fun lemma2-left-keys-b          (
        (state-left-alt (Array Int CompositionState-Left))
        (state-right (Array Int CompositionState-Right))
        (state-length-left Int)
        (state-length-right Int)
        (state-left-NEU Return_Left_gate_GBLG)
        (state-right-NEU Return_Right_simgate_GBLG)
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
    Bool

    (let (
      (state-left-neu (select   (return-Left-gate-GBLG-state state-left-NEU)
                                (return-Left-gate-GBLG-state-length state-left-NEU)))
      (state-right-neu (select  (return-Right-simgate-GBLG-state state-right-NEU)
                                (return-Right-simgate-GBLG-state-length state-right-NEU)))
    )

    (let

; state of the key packages
(
(top-key-package-left-alt (project-State_Left_keys_top (composition-pkgstate-Left-keys_top (select state-left-alt state-length-left-old))))
(top-key-package-left-neu (project-State_Left_keys_top (composition-pkgstate-Left-keys_top state-left-neu)))
(bottom-key-package-left-alt (project-State_Left_keys_bottom (composition-pkgstate-Left-keys_bottom (select state-left-alt state-length-left-old))))
(bottom-key-package-left-neu (project-State_Left_keys_bottom (composition-pkgstate-Left-keys_bottom state-left-neu)))
)

(let

; table of the bottom key package
(
(table-top-left-alt (state-keys-T top-key-package-left-alt))
(table-top-left-neu (state-keys-T top-key-package-left-neu))
(table-bottom-left-alt (state-keys-T bottom-key-package-left-alt))
(table-bottom-left-neu (state-keys-T bottom-key-package-left-neu))
)

(let
(
              ;assignment of the sampled values for the lower Key package as a table
                (Z-left (store (store Z
                    false (mk-some randval-left-6))
                  true (mk-some randval-left-5)))
)

;;; bottom key packages equal except for position j
;;; and where there is j, there is the same or Z
( =>
(and (= (select table-bottom-left-alt j) (as mk-none (Maybe (Array Bool (Maybe Bits_n))))))
(= (select table-bottom-left-neu j) (mk-some Z-left)) ;this is the hard part in the proof
))))))

(define-fun lemma2-right-keys-a          (
        (state-left (Array Int CompositionState-Left))
        (state-right (Array Int CompositionState-Right))
        (state-length-left Int)
        (state-length-right Int)
        (state-left-NEU Return_Left_gate_GBLG)
        (state-right-NEU Return_Right_simgate_GBLG) 
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
    Bool


    (let (
      (state-left-neu (select   (return-Left-gate-GBLG-state state-left-NEU)
                                (return-Left-gate-GBLG-state-length state-left-NEU)))
      (state-right-neu (select  (return-Right-simgate-GBLG-state state-right-NEU)
                                (return-Right-simgate-GBLG-state-length state-right-NEU)))
    )
    (let

; state of the key packages
(
(top-key-package-right-alt (project-State_Right_keys_top (composition-pkgstate-Right-keys_top (select state-right state-length-right-old))))
(top-key-package-right-neu (project-State_Right_keys_top (composition-pkgstate-Right-keys_top state-right-neu)))
(bottom-key-package-right-alt (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom (select state-right state-length-right-old))))
(bottom-key-package-right-neu (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-neu)))


)

(let

; table of the bottom key package
(
(table-top-right-alt    (state-keys-T top-key-package-right-alt))
(table-top-right-neu    (state-keys-T top-key-package-right-neu))
(table-bottom-right-alt (state-keys-T bottom-key-package-right-alt))
(table-bottom-right-neu (state-keys-T bottom-key-package-right-neu))


)

(let
(
              ;assignment of the sampled values for the lower Key package as a table
              (Z-right (store (store Z
                    false (mk-some randval-right-8))
                  true (mk-some randval-right-7)))
)


;;; bottom key packages equal except for position j
;;; and where there is j, there is the same or Z
(forall ((hh Int))
(=> (not
(and (= j hh) (= (select table-bottom-right-alt hh) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))))
(= (select table-bottom-right-alt hh) (select table-bottom-right-neu hh))
;(= (select table-bottom-right-neu hh) (mk-some Z-right)) ;this is the hard part in the proof
)))))))

(define-fun lemma2-right-keys-b          (
        (state-left (Array Int CompositionState-Left))
        (state-right (Array Int CompositionState-Right))
        (state-length-left Int)
        (state-length-right Int)
        (state-left-NEU Return_Left_gate_GBLG)
        (state-right-NEU Return_Right_simgate_GBLG)
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
    Bool


    (let (
      (state-left-neu (select   (return-Left-gate-GBLG-state state-left-NEU)
                                (return-Left-gate-GBLG-state-length state-left-NEU)))
      (state-right-neu (select  (return-Right-simgate-GBLG-state state-right-NEU)
                                (return-Right-simgate-GBLG-state-length state-right-NEU)))
    )

    (let

; state of the key packages
(
(top-key-package-right-alt (project-State_Right_keys_top (composition-pkgstate-Right-keys_top (select state-right state-length-right-old))))
(top-key-package-right-neu (project-State_Right_keys_top (composition-pkgstate-Right-keys_top state-right-neu)))
(bottom-key-package-right-alt (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom (select state-right state-length-right-old))))
(bottom-key-package-right-neu (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-neu)))

)

(let

; table of the bottom key package
(
(table-top-right-alt    (state-keys-T top-key-package-right-alt))
(table-top-right-neu    (state-keys-T top-key-package-right-neu))
(table-bottom-right-alt (state-keys-T bottom-key-package-right-alt))
(table-bottom-right-neu (state-keys-T bottom-key-package-right-neu))


)

(let
(
              ;assignment of the sampled values for the lower Key package as a table
              (Z-right (store (store Z
                    false (mk-some randval-right-8))
                  true (mk-some randval-right-7)))
)


;;; bottom key packages equal except for position j
;;; and where there is j, there is the same or Z
( =>
(and (= (select table-bottom-right-alt j) (as mk-none (Maybe (Array Bool (Maybe Bits_n))))))
(= (select table-bottom-right-neu j) (mk-some Z-right))) ;this is the hard part in the proof
)))))

(define-fun lemma2-keys          (
        (state-left (Array Int CompositionState-Left))
        (state-right (Array Int CompositionState-Right))
        (state-length-left Int)
        (state-length-right Int)
        (state-left-NEU Return_Left_gate_GBLG)
        (state-right-NEU Return_Right_simgate_GBLG)
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool


    (let (
      (state-left-neu (select   (return-Left-gate-GBLG-state state-left-NEU)
                                (return-Left-gate-GBLG-state-length state-left-NEU)))
      (state-right-neu (select  (return-Right-simgate-GBLG-state state-right-NEU)
                                (return-Right-simgate-GBLG-state-length state-right-NEU)))
    )

  (let

; state of the key packages
(
(top-key-package-left-neu  (project-State_Left_keys_top  (composition-pkgstate-Left-keys_top  state-left-neu)))
(top-key-package-right-neu (project-State_Right_keys_top (composition-pkgstate-Right-keys_top state-right-neu)))
(bottom-key-package-left-neu  (project-State_Left_keys_bottom (composition-pkgstate-Left-keys_bottom state-left-neu)))
(bottom-key-package-right-neu (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-neu)))
)

(let

; table of the bottom key package
(
(table-bottom-left-neu (state-keys-T bottom-key-package-left-neu))
(table-bottom-right-neu (state-keys-T bottom-key-package-right-neu))


)


;;; top key packages have equal state
(= table-bottom-left-neu table-bottom-right-neu)


))))

(define-fun same-output          (
        (state-left (Array Int CompositionState-Left))
        (state-right (Array Int CompositionState-Right))
        (state-length-left Int)
        (state-length-right Int)
        (state-left-NEU Return_Left_gate_GBLG)
        (state-right-NEU Return_Right_simgate_GBLG)
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool
(=
(return-Left-gate-GBLG-value return-left-gate-GBLG)
(return-Right-simgate-GBLG-value return-right-simgate-GBLG)
)
)