(declare-fun randomness-mapping-GBLG (
        (Array Int CompositionState-Left)
        (Array Int CompositionState-Right)
        Return_Left_gate_GBLG
        Return_Right_simgate_GBLG
        Int ;h
        Int ;l
        Int ;r
        (Array (Tuple2 Bool Bool) (Maybe Bool)) ;op
        Int) ;j
    Bool)

; special-purpose glue for this particular project
(assert
(and
              ;op should be total
(not (= (select arg-GBLG-op (mk-tuple2 true  true ))(as mk-none (Maybe Bool))))
(not (= (select arg-GBLG-op (mk-tuple2 true  false))(as mk-none (Maybe Bool))))
(not (= (select arg-GBLG-op (mk-tuple2 false true ))(as mk-none (Maybe Bool))))
(not (= (select arg-GBLG-op (mk-tuple2 false false))(as mk-none (Maybe Bool))))
))

(assert
;;;;;;Pre-condition (randomness mapping):
;equality of values of the sample functions for the lower Key package
(forall ((ctr Int))
(and
              (= (__sample-rand-Left-Bits_n 5 ctr)      
                 (__sample-rand-Right-Bits_n 7 ctr))    
              (= (__sample-rand-Left-Bits_n 6 ctr)      
                 (__sample-rand-Right-Bits_n 8 ctr))))) 

(assert
(forall ((ctr Int))
(and
;equality of values of the sample functions for the encryptions
              (= (__sample-rand-Left-Bits_n   9 (* 4 ctr))
                 (__sample-rand-Right-Bits_n  9 ctr))
              (= (__sample-rand-Left-Bits_n  11 (* 4 ctr))
                 (__sample-rand-Right-Bits_n 10 ctr))
              (= (__sample-rand-Left-Bits_n   9 (+ 1 (* 4 ctr)))
                 (__sample-rand-Right-Bits_n 11 ctr))
              (= (__sample-rand-Left-Bits_n  11 (+ 1 (* 4 ctr)))
                 (__sample-rand-Right-Bits_n 12 ctr))
              (= (__sample-rand-Left-Bits_n   9 (+ 2 (* 4 ctr)))
                 (__sample-rand-Right-Bits_n 13 ctr))
              (= (__sample-rand-Left-Bits_n  11 (+ 2 (* 4 ctr)))
                 (__sample-rand-Right-Bits_n 14 ctr))
              (= (__sample-rand-Left-Bits_n   9 (+ 3 (* 4 ctr)))
                 (__sample-rand-Right-Bits_n 15 ctr))
              (= (__sample-rand-Left-Bits_n  11 (+ 3 (* 4 ctr)))
                 (__sample-rand-Right-Bits_n 16 ctr))

)
)
)

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

;Key tables in the key packages are either completely defined or completely undefined
(well-defined T)

; flag is true <=> key has been chosen 
(and
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
(top-key-package-left (project-State_Left_keys_top(composition-pkgstate-Left-keys_top state-left)))
(top-key-package-right (project-State_Right_keys_top(composition-pkgstate-Right-keys_top state-right)))
(bottom-key-package-left (project-State_Left_keys_bottom (composition-pkgstate-Left-keys_bottom state-left)))
(bottom-key-package-right (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right)))
)

(let

; table of the bottom key package
(
(table-bottom-left (state-keys-T bottom-key-package-left))
(table-bottom-right (state-keys-T bottom-key-package-left))
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

(let

; counter values
(
;key sampling
              (ctr-r-left   (composition-rand-Left-5   state-left ))
              (ctr-rr-left  (composition-rand-Left-6   state-left ))
              (ctr-r-right  (composition-rand-Right-7  state-right))
              (ctr-rr-right (composition-rand-Right-8  state-right))

;randomness for the encryptions
              (ctr-left-9  (composition-rand-Left-9  state-left))
              (ctr-left-11 (composition-rand-Left-11 state-left))

              (ctr-right-9  (composition-rand-Right-9  state-right))
              (ctr-right-10 (composition-rand-Right-10 state-right))
              (ctr-right-11 (composition-rand-Right-11 state-right))
              (ctr-right-12 (composition-rand-Right-12 state-right))
              (ctr-right-13 (composition-rand-Right-13 state-right))
              (ctr-right-14 (composition-rand-Right-14 state-right))
              (ctr-right-15 (composition-rand-Right-15 state-right))
              (ctr-right-16 (composition-rand-Right-16 state-right))
)


;compatibility of the counter values
(= ctr-r-left ctr-r-right)
(= ctr-rr-left ctr-rr-right)

(= ctr-left-9  (* 4 ctr-right-9))
(= ctr-left-11 (* 4 ctr-right-10))

;and the other right counters are all equal.
(= ctr-right-9 ctr-right-10)
(= ctr-right-10 ctr-right-11)
(= ctr-right-11 ctr-right-12)
(= ctr-right-12 ctr-right-13)
(= ctr-right-13 ctr-right-14)
(= ctr-right-14 ctr-right-15)
(= ctr-right-15 ctr-right-16)

)

))))


;;;;;;;;;; Lemmas

(define-fun lemma1-left-keys          (
        (state-left-alt (Array Int CompositionState-Left))
        (state-right (Array Int CompositionState-Right))
        (state-left-neu Return_Left_gate_GBLG) ;TODO: extract state from table
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
(top-key-package-left-alt (project-State_Left_keys_top (composition-pkgstate-Left-keys_top state-left-alt)))
(top-key-package-left-neu (project-State_Left_keys_top (composition-pkgstate-Left-keys_top state-left-neu)))
(bottom-key-package-left-alt (project-State_Left_keys_bottom (composition-pkgstate-Left-keys_bottom state-left-alt)))
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


;;;top key packages don't change
(= table-top-left-alt table-top-left-neu)

))
    
    )

(define-fun lemma1-right-keys          (
        (state-left (Array Int CompositionState-Left))
        (state-right-alt (Array Int CompositionState-Right))
        (state-left-new Return_Left_gate_GBLG)
        (state-right-neu Return_Right_simgate_GBLG) ;TODO: extract state from table
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
    Bool
    (let

; state of the key packages
(
(top-key-package-right-alt (project-State_Right_keys_top (composition-pkgstate-Right-keys_top state-right-alt)))
(top-key-package-right-neu (project-State_Right_keys_top (composition-pkgstate-Right-keys_top state-right-neu)))
(bottom-key-package-right-alt (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-alt)))
(bottom-key-package-right-neu (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-neu)))
)

(let

; table of the bottom key package
(
(table-top-right-alt (state-keys-T top-key-package-right-alt))
(table-top-right-neu (state-keys-T top-key-package-right-neu))
(table-bottom-right-alt (state-keys-T bottom-key-package-right-alt))
(table-bottom-right-neu (state-keys-T bottom-key-package-right-neu))
)


;;;top key packages don't change
(= table-top-right-alt table-top-right-neu)

))
    )

(define-fun lemma1-keys          (
        (state-left (Array Int CompositionState-Left))
        (state-right (Array Int CompositionState-Right))
        (state-left-neu Return_Left_gate_GBLG) ;TODO: extract state from table
        (state-right-neu Return_Right_simgate_GBLG) ;TODO: extract state from table
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
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
(table-top-left-neu  (state-keys-T top-key-package-left-neu))
(table-top-right-neu (state-keys-T top-key-package-right-neu))
(table-bottom-left-neu  (state-keys-T bottom-key-package-left-neu))
(table-bottom-right-neu (state-keys-T bottom-key-package-right-neu))
)

;;; bottom key packages equal except for position j
;;; and where there is j, there is the same or Z
(ite
(= table-top-left-neu table-top-right-neu)
true
false)


))
    Bool)

(define-fun lemma2-left-keys-a          (
        (state-left-alt (Array Int CompositionState-Left))
        (state-right (Array Int CompositionState-Right))
        (state-left-neu Return_Left_gate_GBLG) ;TODO: Extract state from table
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
(top-key-package-left-alt (project-State_Left_keys_top (composition-pkgstate-Left-keys_top state-left-alt)))
(top-key-package-left-neu (project-State_Left_keys_top (composition-pkgstate-Left-keys_top state-left-neu)))
(bottom-key-package-left-alt (project-State_Left_keys_bottom (composition-pkgstate-Left-keys_bottom state-left-alt)))
(bottom-key-package-left-neu (project-State_Left_keys_bottom (composition-pkgstate-Left-keys_bottom state-left-neu)))
(ctr-r-left   (composition-rand-Left-3  state-left-alt))
;(ctr-r-right  (composition-rand-Right-1 state-right-old))
(ctr-rr-left  (composition-rand-Left-4  state-left-alt))
;(ctr-rr-right (composition-rand-Right-2 state-right-old))
)

(let

; table of the bottom key package
(
(table-top-left-alt (state-keys-T top-key-package-left-alt))
(table-top-left-neu (state-keys-T top-key-package-left-neu))
(table-bottom-left-alt (state-keys-T bottom-key-package-left-alt))
(table-bottom-left-neu (state-keys-T bottom-key-package-left-neu))
              ;assignment of the sampled values for the lower Key package
              (r-left   (mk-some (__sample-rand-Left-Bits_n 5 ctr-r-left)))
              (rr-left  (mk-some (__sample-rand-Left-Bits_n 6 ctr-rr-left)))

)

(let
(
              ;assignment of the sampled values for the lower Key package as a table
              (Z-left
                 (store (store Z true  r-left) false rr-left)
              )
)

;;; bottom key packages equal except for position j
;;; and where there is j, there is the same or Z
(forall ((hh Int))
(ite
(and (= j hh) (= (select table-bottom-left-alt hh) (as mk-none (Maybe (Array Bool (Maybe Bits_n))))))
true
(= (select table-bottom-left-alt hh) (select table-bottom-left-neu hh))
)))))
    
    )

(define-fun lemma2-left-keys-b          (
        (state-left-alt (Array Int CompositionState-Left))
        (state-right (Array Int CompositionState-Right))
        (state-left-neu Return_Left_gate_GBLG) ;TODO: Extract state from table
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
(top-key-package-left-alt (project-State_Left_keys_top (composition-pkgstate-Left-keys_top state-left-alt)))
(top-key-package-left-neu (project-State_Left_keys_top (composition-pkgstate-Left-keys_top state-left-neu)))
(bottom-key-package-left-alt (project-State_Left_keys_bottom (composition-pkgstate-Left-keys_bottom state-left-alt)))
(bottom-key-package-left-neu (project-State_Left_keys_bottom (composition-pkgstate-Left-keys_bottom state-left-neu)))
(ctr-r-left   (composition-rand-Left-5  state-left-alt))
(ctr-rr-left  (composition-rand-Left-6  state-left-alt))
)

(let

; table of the bottom key package
(
(table-top-left-alt (state-keys-T top-key-package-left-alt))
(table-top-left-neu (state-keys-T top-key-package-left-neu))
(table-bottom-left-alt (state-keys-T bottom-key-package-left-alt))
(table-bottom-left-neu (state-keys-T bottom-key-package-left-neu))
              ;assignment of the sampled values for the lower Key package
              (r-left   (mk-some (__sample-rand-Left-Bits_n 5 ctr-r-left)))
              (rr-left  (mk-some (__sample-rand-Left-Bits_n 6 ctr-rr-left)))
)

(let
(
              ;assignment of the sampled values for the lower Key package as a table
              (Z-left
                 (store (store Z true  r-left) false rr-left)
              )
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
    
    )

(define-fun lemma2-right-keys-a          (
        (state-left (Array Int CompositionState-Left))
        (state-right-alt (Array Int CompositionState-Right))
        (state-left-new Return_Left_gate_GBLG)
        (state-right-neu Return_Right_simgate_GBLG) ;TODO: Extract state from table
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
    Bool
    (let

; state of the key packages
(
(top-key-package-right-alt (project-State_Right_keys_top (composition-pkgstate-Right-keys_top state-right-alt)))
(top-key-package-right-neu (project-State_Right_keys_top (composition-pkgstate-Right-keys_top state-right-neu)))
(bottom-key-package-right-alt (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-alt)))
(bottom-key-package-right-neu (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-neu)))

; get current counter for Bits_n sampling
              ;assignment of the ctr of the sample instructions for the lower Key package
              (ctr-r-right  (composition-rand-Right-7 state-right-alt))
              (ctr-rr-right (composition-rand-Right-8 state-right-alt))

)

(let

; table of the bottom key package
(
(table-top-right-alt    (state-keys-T top-key-package-right-alt))
(table-top-right-neu    (state-keys-T top-key-package-right-neu))
(table-bottom-right-alt (state-keys-T bottom-key-package-right-alt))
(table-bottom-right-neu (state-keys-T bottom-key-package-right-neu))

              ;assignment of the sampled values for the lower Key package
              (r-right  (mk-some (__sample-rand-Right-Bits_n 7 ctr-r-right)))
              (rr-right (mk-some (__sample-rand-Right-Bits_n 8 ctr-rr-right)))

)

(let
(
              ;assignment of the sampled values for the lower Key package as a table
              (Z-right (store (store Z true r-right) false rr-right))
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
    
    )

(define-fun lemma2-right-keys-b          (
        (state-left (Array Int CompositionState-Left))
        (state-right-alt (Array Int CompositionState-Right))
        (state-left-new Return_Left_gate_GBLG)
        (state-right-neu Return_Right_simgate_GBLG) ;TODO: extract state from table
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
    Bool
    (let

; state of the key packages
(
(top-key-package-right-alt (project-State_Right_keys_top (composition-pkgstate-Right-keys_top state-right-alt)))
(top-key-package-right-neu (project-State_Right_keys_top (composition-pkgstate-Right-keys_top state-right-neu)))
(bottom-key-package-right-alt (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-alt)))
(bottom-key-package-right-neu (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-neu)))

; get current counter for Bits_n sampling
              ;assignment of the ctr of the sample instructions for the lower Key package
              (ctr-r-right  (composition-rand-Right-7 state-right-alt))
              (ctr-rr-right (composition-rand-Right-8 state-right-alt))
)

(let

; table of the bottom key package
(
(table-top-right-alt    (state-keys-T top-key-package-right-alt))
(table-top-right-neu    (state-keys-T top-key-package-right-neu))
(table-bottom-right-alt (state-keys-T bottom-key-package-right-alt))
(table-bottom-right-neu (state-keys-T bottom-key-package-right-neu))

              ;assignment of the sampled values for the lower Key package
              (r-right  (mk-some (__sample-rand-Right-Bits_n 7 ctr-r-right)))
              (rr-right (mk-some (__sample-rand-Right-Bits_n 8 ctr-rr-right)))

)

(let
(
              ;assignment of the sampled values for the lower Key package as a table
              (Z-right (store (store Z true r-right) false rr-right))
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
    )

;;;;;;;;;;;;;;;;;;;;;;;;;;;
; TODO
;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun lemma1-left-keys          (
        (state-left (Array Int CompositionState-Left))
        (state-right (Array Int CompositionState-Right))
        (state-left-new Return_Left_gate_GBLG)
        (state-right-new Return_Right_simgate_GBLG)
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
    Bool)

(define-fun lemma1-left-keys          (
        (state-left (Array Int CompositionState-Left))
        (state-right (Array Int CompositionState-Right))
        (state-left-new Return_Left_gate_GBLG)
        (state-right-new Return_Right_simgate_GBLG)
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
    Bool)
