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
(not (= (select op (mk-tuple2 true  true ))(as mk-none (Maybe Bool))))
(not (= (select op (mk-tuple2 true  false))(as mk-none (Maybe Bool))))
(not (= (select op (mk-tuple2 false true ))(as mk-none (Maybe Bool))))
(not (= (select op (mk-tuple2 false false))(as mk-none (Maybe Bool))))
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


(define-fun invariant-GBLG          (
        (state-left (Array Int CompositionState-Left))
        (state-right (Array Int CompositionState-Right))
        (y-left Return_Left_gate_GBLG)
        (y-right Return_Right_simgate_GBLG)
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

))))

(declare-fun foo          (
        (Array Int CompositionState-Left)
        (Array Int CompositionState-Right)
        Return_Left_gate_GBLG
        Return_Right_simgate_GBLG
        Int
        Int
        Int
        (Array (Tuple2 Bool Bool) (Maybe Bool))
        Int)
    Bool)
(declare-fun bar          (
        (Array Int CompositionState-Left)
        (Array Int CompositionState-Right)
        Return_Left_gate_GBLG
        Return_Right_simgate_GBLG
        Int
        Int
        Int
        (Array (Tuple2 Bool Bool) (Maybe Bool))
        Int)
    Bool)