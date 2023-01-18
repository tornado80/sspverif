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
(top-key-package-left (project-State_Left_keys_top          (composition-pkgstate-Left-keys_top     (select state-left state-length-left))))
(top-key-package-right (project-State_Right_keys_top        (composition-pkgstate-Right-keys_top    (select state-right state-length-right))))
(bottom-key-package-left (project-State_Left_keys_bottom    (composition-pkgstate-Left-keys_bottom  (select state-left state-length-left))))
(bottom-key-package-right (project-State_Right_keys_bottom  (composition-pkgstate-Right-keys_bottom (select state-right state-length-right))))
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


(not (return-Right-simgate-GBLG-is-abort state-right-new))
(not (return-Left-gate-GBLG-is-abort state-left-new))


))))

(declare-const debug-top-old-left State_keys)
(declare-const debug-top-new-left State_keys)


(assert
(and
(= 
debug-top-new-left
  (let  (
      (state-left-neu (select   (return-Left-gate-GBLG-state return-left-gate-GBLG)
                                (return-Left-gate-GBLG-state-length return-left-gate-GBLG)))
    )
    (let

; state of the key packages
(
(top-key-package-left-alt (project-State_Left_keys_top        (composition-pkgstate-Left-keys_top     (select state-left state-length-left-old))))
(top-key-package-left-neu (project-State_Left_keys_top        (composition-pkgstate-Left-keys_top     state-left-neu)))
)
top-key-package-left-neu
)))

(= 
debug-top-old-left
  (let  (
      (state-left-neu (select   (return-Left-gate-GBLG-state return-left-gate-GBLG)
                                (return-Left-gate-GBLG-state-length return-left-gate-GBLG)))
    )
    (let

; state of the key packages
(
(top-key-package-left-alt (project-State_Left_keys_top        (composition-pkgstate-Left-keys_top     (select state-left state-length-left-old))))
(top-key-package-left-neu (project-State_Left_keys_top        (composition-pkgstate-Left-keys_top     state-left-neu)))
)
top-key-package-left-alt
)))

))

;;;;;;;;;; Lemmas

(define-fun lemma1-left-keys          (
        (state-left-alt (Array Int CompositionState-Left))
        (state-right-alt (Array Int CompositionState-Right))
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

  (let  (
      (state-left-neu (select   (return-Left-gate-GBLG-state state-left-NEU)
                                (return-Left-gate-GBLG-state-length state-left-NEU)))
      (state-right-neu (select  (return-Right-simgate-GBLG-state state-right-NEU)
                                (return-Right-simgate-GBLG-state-length state-right-NEU)))
    )
    (let

; state of the key packages
(
(top-key-package-left-alt (project-State_Left_keys_top        (composition-pkgstate-Left-keys_top     (select state-left-alt state-length-left))))
(top-key-package-left-neu (project-State_Left_keys_top        (composition-pkgstate-Left-keys_top     state-left-neu)))
(bottom-key-package-left-alt (project-State_Left_keys_bottom  (composition-pkgstate-Left-keys_bottom  (select state-left-alt state-length-left))))
(bottom-key-package-left-neu (project-State_Left_keys_bottom  (composition-pkgstate-Left-keys_bottom  state-left-neu)))
)
(= top-key-package-left-alt top-key-package-left-neu)


)))

(define-fun lemma1-right-keys          (
        (state-left (Array Int CompositionState-Left))
        (state-right-alt (Array Int CompositionState-Right))
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
(top-key-package-right-alt (project-State_Right_keys_top (composition-pkgstate-Right-keys_top (select state-right-alt state-length-right))))
(top-key-package-right-neu (project-State_Right_keys_top (composition-pkgstate-Right-keys_top state-right-neu)))
(bottom-key-package-right-alt (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom (select state-right-alt state-length-right))))
(bottom-key-package-right-neu (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-neu)))
)


;;;top key packages don't change
(= top-key-package-right-alt top-key-package-right-neu)

))
    )

(define-fun lemma1-keys          (
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
      (state-right-neu (select  (return-Right-simgate-GBLG-state state-right-NEU)
                                (return-Right-simgate-GBLG-state-length state-right-NEU)))
    )

    (let

; state of the key packages
(
(top-key-package-left-alt (project-State_Left_keys_top       (composition-pkgstate-Left-keys_top    (select state-left-alt state-length-left))))
(top-key-package-left-neu (project-State_Left_keys_top       (composition-pkgstate-Left-keys_top    state-left-neu)))
(bottom-key-package-left-alt (project-State_Left_keys_bottom (composition-pkgstate-Left-keys_bottom (select state-left-alt state-length-left))))
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
(ite
(and (= j hh) (= (select table-bottom-left-alt hh) (as mk-none (Maybe (Array Bool (Maybe Bits_n))))))
true
(= (select table-bottom-left-alt hh) (select table-bottom-left-neu hh))
)))))
    
    ))

(define-fun lemma2-left-keys-b          (
        (state-left-alt (Array Int CompositionState-Left))
        (state-right (Array Int CompositionState-Right))
        (state-length-left Int)
        (state-length-right Int)
        (state-left-NEU Return_Left_gate_GBLG) ;TODO: Extract state from table
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
(top-key-package-left-alt (project-State_Left_keys_top (composition-pkgstate-Left-keys_top (select state-left-alt state-length-left))))
(top-key-package-left-neu (project-State_Left_keys_top (composition-pkgstate-Left-keys_top state-left-neu)))
(bottom-key-package-left-alt (project-State_Left_keys_bottom (composition-pkgstate-Left-keys_bottom (select state-left-alt state-length-left))))
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
(ite
(and (= j hh) (= (select table-bottom-left-alt hh) (as mk-none (Maybe (Array Bool (Maybe Bits_n))))))
;(= (select table-bottom-left-alt hh) (select table-bottom-left-neu hh))
(= (select table-bottom-left-neu hh) (mk-some Z-left)) ;this is the hard part in the proof
true
)))))
    
    ))

(define-fun lemma2-right-keys-a          (
        (state-left (Array Int CompositionState-Left))
        (state-right-alt (Array Int CompositionState-Right))
        (state-length-left Int)
        (state-length-right Int)
        (state-left-NEU Return_Left_gate_GBLG)
        (state-right-NEU Return_Right_simgate_GBLG) ;TODO: Extract state from table
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
(top-key-package-right-alt (project-State_Right_keys_top (composition-pkgstate-Right-keys_top (select state-right-alt state-length-right))))
(top-key-package-right-neu (project-State_Right_keys_top (composition-pkgstate-Right-keys_top state-right-neu)))
(bottom-key-package-right-alt (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom (select state-right-alt state-length-right))))
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
(ite
(not
(and (= j hh) (= (select table-bottom-right-alt hh) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))))
(= (select table-bottom-right-alt hh) (select table-bottom-right-neu hh))
true ;(= (select table-bottom-right-neu hh) (mk-some Z-right)) ;this is the hard part in the proof
)))))
    
    ))

(define-fun lemma2-right-keys-b          (
        (state-left (Array Int CompositionState-Left))
        (state-right-alt (Array Int CompositionState-Right))
        (state-length-left Int)
        (state-length-right Int)
        (state-left-NEU Return_Left_gate_GBLG)
        (state-right-NEU Return_Right_simgate_GBLG) ;TODO: extract state from table
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
(top-key-package-right-alt (project-State_Right_keys_top (composition-pkgstate-Right-keys_top (select state-right-alt state-length-right))))
(top-key-package-right-neu (project-State_Right_keys_top (composition-pkgstate-Right-keys_top state-right-neu)))
(bottom-key-package-right-alt (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom (select state-right-alt state-length-right))))
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
(ite
(not
(and (= j hh) (= (select table-bottom-right-alt hh) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))))
true
(= (select table-bottom-right-neu hh) (mk-some Z-right)) ;this is the hard part in the proof
)))))
    ))

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

