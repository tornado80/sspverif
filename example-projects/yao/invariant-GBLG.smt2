;(assert
;(and
;(= state-length-left-old 1)
;(= state-length-right-old 1)
;)
;)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;   Randomness naming
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare-const randval-left-9+1 Bits_n)
(assert (= randval-left-9+1 (__sample-rand-Left_inst--Bits_n 9 (+ 1 randctr-left-9)
)))

(declare-const randval-left-9+2 Bits_n)
(assert (= randval-left-9+2 (__sample-rand-Left_inst--Bits_n 9 (+ 2 randctr-left-9)
)))

(declare-const randval-left-9+3 Bits_n)
(assert (= randval-left-9+3 (__sample-rand-Left_inst--Bits_n 9 (+ 3 randctr-left-9)
)))

(declare-const randval-left-11+1 Bits_n)
(assert (= randval-left-11+1 (__sample-rand-Left_inst--Bits_n 11 (+ 1 randctr-left-11)
)))

(declare-const randval-left-11+2 Bits_n)
(assert (= randval-left-11+2 (__sample-rand-Left_inst--Bits_n 11 (+ 2 randctr-left-11)
)))

(declare-const randval-left-11+3 Bits_n)
(assert (= randval-left-11+3 (__sample-rand-Left_inst--Bits_n 11 (+ 3 randctr-left-11)
)))

(declare-const randval-left-GETA-1 Bits_n)
(assert (= randval-left-GETA-1  (__sample-rand-Left_inst--Bits_n  1 randctr-left-1
)))

(declare-const randval-right-GETA-1 Bits_n)
(assert (= randval-right-GETA-1 (__sample-rand-Right_inst--Bits_n 1 randctr-right-1
)))

(declare-const randval-left-GETA-2 Bits_n)
(assert (= randval-left-GETA-2  (__sample-rand-Left_inst--Bits_n  2 randctr-left-2
)))

(declare-const randval-right-GETA-2 Bits_n)
(assert (= randval-right-GETA-2 (__sample-rand-Right_inst--Bits_n 2 randctr-right-2
)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;   Randomness mapping
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


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

(define-fun randomness-mapping-SETBIT () Bool
true
)

(define-fun randomness-mapping-GETAOUT () Bool
(and
(= randval-left-GETA-1 randval-right-GETA-1)
(= randval-left-GETA-2 randval-right-GETA-2)
)
)

(define-fun randomness-mapping-GETKEYSIN () Bool
true
)




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;   op is total (special-purpose glue)
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert
(and
(not (= (select arg-GBLG-op (mk-tuple2 true  true ))(as mk-none (Maybe Bool))))
(not (= (select arg-GBLG-op (mk-tuple2 true  false))(as mk-none (Maybe Bool))))
(not (= (select arg-GBLG-op (mk-tuple2 false true ))(as mk-none (Maybe Bool))))
(not (= (select arg-GBLG-op (mk-tuple2 false false))(as mk-none (Maybe Bool))))
))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;   Datatypes to extract key package state
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(declare-datatype
  State_keys
  (
    (mk-state-keys
      (state-keys-T (Array Int (Maybe (Array Bool (Maybe Bits_n)))))
      (state-keys-z (Array Int (Maybe Bool)))
      (state-keys-flag (Array Int (Maybe Bool))))))

(define-fun project-State_Left_inst-_keys_top ((in State_Left_inst-_keys_top)) State_keys
  (mk-state-keys (state-Left_inst--keys_top-T    in)
                 (state-Left_inst--keys_top-z    in)
                 (state-Left_inst--keys_top-flag in)))

(define-fun project-State_Right_inst-_keys_top ((in State_Right_inst-_keys_top)) State_keys
  (mk-state-keys (state-Right_inst--keys_top-T    in)
                 (state-Right_inst--keys_top-z    in)
                 (state-Right_inst--keys_top-flag in)))

(define-fun project-State_Left_inst-_keys_bottom ((in State_Left_inst-_keys_bottom)) State_keys
  (mk-state-keys (state-Left_inst--keys_bottom-T    in)
                 (state-Left_inst--keys_bottom-z    in)
                 (state-Left_inst--keys_bottom-flag in)))

(define-fun project-State_Right_inst-_keys_bottom ((in State_Right_inst-_keys_bottom)) State_keys
  (mk-state-keys (state-Right_inst--keys_bottom-T    in)
                 (state-Right_inst--keys_bottom-z    in)
                 (state-Right_inst--keys_bottom-flag in)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;   Well-definedness of tables
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;If T h != none => T h b != none (for both b=0 and b=1)

(define-fun well-defined ((T (Array Int (Maybe (Array Bool (Maybe Bits_n)))))) Bool
  (forall ((h Int))
    (or
      (= (select T h) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
      (forall ((b Bool))
        (not
          (= (select (maybe-get (select T h)) b) (as mk-none (Maybe Bits_n)))
)))))

; captures the possible states which a Key package can be in when
; the "top" queries are GETKEYS queries 
;
(define-fun well-defined-Key-bool ((key-state State_keys)) Bool
(let ((T    (state-keys-T    key-state))
      (flag (state-keys-flag key-state))
      (z    (state-keys-z    key-state)))

; flag is true <=> key has been chosen 
(and

;If T h != none => T h b != none (for both b=0 and b=1)
(well-defined T)

(forall ((hhh Int))
(or
    (= (select flag hhh) (as mk-none (Maybe Bool)))
    (= (select flag hhh) (   mk-some        true )))
)

;If flag h != true => T h  = none
;If flag h  = true => T h != none (for both b=0 and b=1)

(forall ((hhh Int)) 
(and 
(=>
    (not (= (select flag hhh) (mk-some true)))
    (= (select T hhh) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
)
(=>
    (= (select flag hhh) (mk-some true))
    (and
       (not (= (select T hhh)                            (as mk-none (Maybe (Array Bool (Maybe Bits_n))))))
       (not (= (select (maybe-get (select T hhh)) true ) (as mk-none (Maybe Bits_n))))
       (not (= (select (maybe-get (select T hhh)) false) (as mk-none (Maybe Bits_n))))
    )
))))))

; captures the possible states which a Key package can be in when
; the "top" queries are GETA and SETBIT queries 
;
(define-fun well-defined-Key-active ((key-state State_keys)) Bool
(let ((T    (state-keys-T    key-state))
      (flag (state-keys-flag key-state))
      (z    (state-keys-z    key-state)))

(and

;If T h != none => T h b != none (for both b=0 and b=1)
(well-defined T)

(forall ((hhh Int))
(or
  (= (select flag hhh) (as mk-none (Maybe Bool)))
  (= (select flag hhh) (   mk-some        true ))))

; flag has been set  => bit has been set
(forall ((hhh Int)) (=> (=  (mk-some true ) (select flag hhh))  
                    (or (=  (mk-some true ) (select z    hhh))
                        (=  (mk-some false) (select z    hhh))
                    )))

; key has been set => flag has been set
(forall ((hhh Int)) (=>
                    (not
                    (= (select T hhh) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
                    )
                    (= (select flag hhh) (mk-some true)))
                    ))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Invariant
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; This is supposed to be an invariant
(define-fun invariant-GBLG          (
        (state-left  (Array Int CompositionState-Left_inst- ))
        (state-right (Array Int CompositionState-Right_inst-))
        (state-length-left  Int) ;old index
        (state-length-right Int) ;old index
        (state-left-new  Return_Left_inst-_gate_GBLG)
        (state-right-new Return_Right_inst-_simgate_GBLG)
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
    Bool
    (let

; state of the key packages
(
(top-key-package-left  (project-State_Left_inst-_keys_top      (composition-pkgstate-Left_inst--keys_top     (select state-left  state-length-left))))
(top-key-package-right (project-State_Right_inst-_keys_top     (composition-pkgstate-Right_inst--keys_top    (select state-right state-length-right))))
(bot-key-package-left  (project-State_Left_inst-_keys_bottom   (composition-pkgstate-Left_inst--keys_bottom  (select state-left  state-length-left))))
(bot-key-package-right (project-State_Right_inst-_keys_bottom  (composition-pkgstate-Right_inst--keys_bottom (select state-right state-length-right))))
)

(let

; table of the bottom key package
(
(table-bot-left  (state-keys-T    bot-key-package-left))
(table-bot-right (state-keys-T    bot-key-package-right))
(    z-bot-left  (state-keys-z    bot-key-package-left))
(    z-bot-right (state-keys-z    bot-key-package-right))
(flag-bot-left   (state-keys-flag bot-key-package-left))
(flag-bot-right  (state-keys-flag bot-key-package-right))
)

(and
;top key package states are equal
(= top-key-package-left top-key-package-right)

;for bottom key package, tables are equal
(= table-bot-left table-bot-right)

;top key package state is "good"
(well-defined-Key-active top-key-package-left )
(well-defined-Key-active top-key-package-right)

;bottom key packages state is "good"
(well-defined-Key-bool   bot-key-package-left )
(well-defined-Key-active bot-key-package-right)
(forall ((h Int))
(and
    (= (select  flag-bot-left  h) 
       (select  flag-bot-right h))
(=> (= (select table-bot-left  h) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
    (= (select  flag-bot-left  h) (   mk-some        false)))
(=> (= (select table-bot-right h) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
    (and
    (= (select  flag-bot-right h) (   mk-some        false))
    (= (select     z-bot-right h) (as mk-none (Maybe Bool )))))
(=> (= (select  flag-bot-right h) (   mk-some        false))
    (= (select     z-bot-right h) (as mk-none (Maybe Bool ))))
))))))

(define-fun invariant-GBLG-post          (
        (state-left  (Array Int CompositionState-Left_inst- ))
        (state-right (Array Int CompositionState-Right_inst-))
        (state-length-left  Int) ;old index
        (state-length-right Int) ;old index
        (state-left-new  Return_Left_inst-_gate_GBLG)
        (state-right-new Return_Right_inst-_simgate_GBLG)
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
    Bool
(let (
      (state-left-nov  (select  (return-Left_inst--gate-GBLG-state        state-left-new)
                                (return-Left_inst--gate-GBLG-state-length state-left-new)
                                ))
      (state-right-nov (select  (return-Right_inst--simgate-GBLG-state        state-right-new)
                                (return-Right_inst--simgate-GBLG-state-length state-right-new)
                                ))
     )

    (let

; state of the key packages
(
(top-key-package-left  (project-State_Left_inst-_keys_top      (composition-pkgstate-Left_inst--keys_top     state-left-nov  )))
(top-key-package-right (project-State_Right_inst-_keys_top     (composition-pkgstate-Right_inst--keys_top    state-right-nov )))
(bot-key-package-left  (project-State_Left_inst-_keys_bottom   (composition-pkgstate-Left_inst--keys_bottom  state-left-nov  )))
(bot-key-package-right (project-State_Right_inst-_keys_bottom  (composition-pkgstate-Right_inst--keys_bottom state-right-nov )))
)

(let

; table of the bottom key package
(
(table-bot-left  (state-keys-T    bot-key-package-left))
(table-bot-right (state-keys-T    bot-key-package-right))
(    z-bot-left  (state-keys-z    bot-key-package-left))
(    z-bot-right (state-keys-z    bot-key-package-right))
(flag-bot-left   (state-keys-flag bot-key-package-left))
(flag-bot-right  (state-keys-flag bot-key-package-right))
)

(and
;top key package states are equal
(= top-key-package-left top-key-package-right)

;for bottom key package, tables are equal
(= table-bot-left table-bot-right)

;top key package state is "good"
(well-defined-Key-active top-key-package-left )
(well-defined-Key-active top-key-package-right)

;bottom key packages state is "good"
(well-defined-Key-bool   bot-key-package-left )
(well-defined-Key-active bot-key-package-right)
(forall ((h Int))
(and
    (= (select  flag-bot-left  h) 
       (select  flag-bot-right h))
(=> (= (select table-bot-left  h) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
    (= (select  flag-bot-left  h) (   mk-some        false)))
(=> (= (select table-bot-right h) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
    (and
    (= (select  flag-bot-right h) (   mk-some        false))
    (= (select     z-bot-right h) (as mk-none (Maybe Bool )))))
(=> (= (select  flag-bot-right h) (   mk-some        false))
    (= (select     z-bot-right h) (as mk-none (Maybe Bool ))))
)))))))

(define-fun invariant-SETBIT      (
        (state-left  (Array Int CompositionState-Left_inst- ))
        (state-right (Array Int CompositionState-Right_inst-))
        (state-length-left  Int) ;old index
        (state-length-right Int) ;old index
        (state-left-new  Return_Left_inst-_keys_top_SETBIT)
        (state-right-new Return_Right_inst-_keys_top_SETBIT)
        (h Int)
        (zz Bool))
    Bool
    (let

; state of the key packages
(
(top-key-package-left  (project-State_Left_inst-_keys_top      (composition-pkgstate-Left_inst--keys_top     (select state-left  state-length-left))))
(top-key-package-right (project-State_Right_inst-_keys_top     (composition-pkgstate-Right_inst--keys_top    (select state-right state-length-right))))
(bot-key-package-left  (project-State_Left_inst-_keys_bottom   (composition-pkgstate-Left_inst--keys_bottom  (select state-left  state-length-left))))
(bot-key-package-right (project-State_Right_inst-_keys_bottom  (composition-pkgstate-Right_inst--keys_bottom (select state-right state-length-right))))
)

(let

; table of the bottom key package
(
(table-bot-left  (state-keys-T    bot-key-package-left))
(table-bot-right (state-keys-T    bot-key-package-right))
(    z-bot-left  (state-keys-z    bot-key-package-left))
(    z-bot-right (state-keys-z    bot-key-package-right))
(flag-bot-left   (state-keys-flag bot-key-package-left))
(flag-bot-right  (state-keys-flag bot-key-package-right))
)

(and
;top key package states are equal
(= top-key-package-left top-key-package-right)

;for bottom key package, tables are equal
(= table-bot-left table-bot-right)

;top key package state is "good"
(well-defined-Key-active top-key-package-left )
(well-defined-Key-active top-key-package-right)

;bottom key packages state is "good"
(well-defined-Key-bool   bot-key-package-left )
(well-defined-Key-active bot-key-package-right)
(forall ((h Int))
(and
    (= (select  flag-bot-left  h) 
       (select  flag-bot-right h))
(=> (= (select table-bot-left  h) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
    (= (select  flag-bot-left  h) (   mk-some        false)))
(=> (= (select table-bot-right h) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
    (and
    (= (select  flag-bot-right h) (   mk-some        false))
    (= (select     z-bot-right h) (as mk-none (Maybe Bool )))))
(=> (= (select  flag-bot-right h) (   mk-some        false))
    (= (select     z-bot-right h) (as mk-none (Maybe Bool ))))
))))))


(define-fun invariant-SETBIT-post          (
        (state-left  (Array Int CompositionState-Left_inst- ))
        (state-right (Array Int CompositionState-Right_inst-))
        (state-length-left  Int) ;old index
        (state-length-right Int) ;old index
        (state-left-new  Return_Left_inst-_keys_top_SETBIT)
        (state-right-new Return_Right_inst-_keys_top_SETBIT)
        (h Int)
        (zz Bool))
    Bool
(let (
      (state-left-nov  (select  (return-Left_inst--keys_top-SETBIT-state        state-left-new)
                                (return-Left_inst--keys_top-SETBIT-state-length state-left-new)
                                ))
      (state-right-nov (select  (return-Right_inst--keys_top-SETBIT-state        state-right-new)
                                (return-Right_inst--keys_top-SETBIT-state-length state-right-new)
                                ))
     )

    (let

; state of the key packages
(
(top-key-package-left  (project-State_Left_inst-_keys_top      (composition-pkgstate-Left_inst--keys_top     state-left-nov  )))
(top-key-package-right (project-State_Right_inst-_keys_top     (composition-pkgstate-Right_inst--keys_top    state-right-nov )))
(bot-key-package-left  (project-State_Left_inst-_keys_bottom   (composition-pkgstate-Left_inst--keys_bottom  state-left-nov  )))
(bot-key-package-right (project-State_Right_inst-_keys_bottom  (composition-pkgstate-Right_inst--keys_bottom state-right-nov )))
)

(let

; table of the bottom key package
(
(table-bot-left  (state-keys-T    bot-key-package-left))
(table-bot-right (state-keys-T    bot-key-package-right))
(    z-bot-left  (state-keys-z    bot-key-package-left))
(    z-bot-right (state-keys-z    bot-key-package-right))
(flag-bot-left   (state-keys-flag bot-key-package-left))
(flag-bot-right  (state-keys-flag bot-key-package-right))
)

(and
;top key package states are equal
(= top-key-package-left top-key-package-right)

;for bottom key package, tables are equal
(= table-bot-left table-bot-right)

;top key package state is "good"
(well-defined-Key-active top-key-package-left )
(well-defined-Key-active top-key-package-right)

;bottom key packages state is "good"
(well-defined-Key-bool   bot-key-package-left )
(well-defined-Key-active bot-key-package-right)
(forall ((h Int))
(and
    (= (select  flag-bot-left  h) 
       (select  flag-bot-right h))
(=> (= (select table-bot-left  h) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
    (= (select  flag-bot-left  h) (   mk-some        false)))
(=> (= (select table-bot-right h) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
    (and
    (= (select  flag-bot-right h) (   mk-some        false))
    (= (select     z-bot-right h) (as mk-none (Maybe Bool )))))
(=> (= (select  flag-bot-right h) (   mk-some        false))
    (= (select     z-bot-right h) (as mk-none (Maybe Bool ))))
)))))))

(define-fun invariant-GETAOUT      (
        (state-left  (Array Int CompositionState-Left_inst- ))
        (state-right (Array Int CompositionState-Right_inst-))
        (state-length-left  Int) ;old index
        (state-length-right Int) ;old index
        (state-left-new  Return_Left_inst-_keys_top_GETAOUT)
        (state-right-new Return_Right_inst-_keys_top_GETAOUT)
        (h Int))
    Bool
    (let

; state of the key packages
(
(top-key-package-left  (project-State_Left_inst-_keys_top      (composition-pkgstate-Left_inst--keys_top     (select state-left  state-length-left))))
(top-key-package-right (project-State_Right_inst-_keys_top     (composition-pkgstate-Right_inst--keys_top    (select state-right state-length-right))))
(bot-key-package-left  (project-State_Left_inst-_keys_bottom   (composition-pkgstate-Left_inst--keys_bottom  (select state-left  state-length-left))))
(bot-key-package-right (project-State_Right_inst-_keys_bottom  (composition-pkgstate-Right_inst--keys_bottom (select state-right state-length-right))))
)

(let

; table of the bottom key package
(
(table-bot-left  (state-keys-T    bot-key-package-left))
(table-bot-right (state-keys-T    bot-key-package-right))
(    z-bot-left  (state-keys-z    bot-key-package-left))
(    z-bot-right (state-keys-z    bot-key-package-right))
(flag-bot-left   (state-keys-flag bot-key-package-left))
(flag-bot-right  (state-keys-flag bot-key-package-right))
)

(and
;top key package states are equal
(= top-key-package-left top-key-package-right)

;for bottom key package, tables are equal
(= table-bot-left table-bot-right)

;top key package state is "good"
(well-defined-Key-active top-key-package-left )
(well-defined-Key-active top-key-package-right)

;bottom key packages state is "good"
(well-defined-Key-bool   bot-key-package-left )
(well-defined-Key-active bot-key-package-right)
(forall ((h Int))
(and
    (= (select  flag-bot-left  h) 
       (select  flag-bot-right h))
(=> (= (select table-bot-left  h) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
    (= (select  flag-bot-left  h) (   mk-some        false)))
(=> (= (select table-bot-right h) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
    (and
    (= (select  flag-bot-right h) (   mk-some        false))
    (= (select     z-bot-right h) (as mk-none (Maybe Bool )))))
(=> (= (select  flag-bot-right h) (   mk-some        false))
    (= (select     z-bot-right h) (as mk-none (Maybe Bool ))))
))))))


(define-fun invariant-GETAOUT-post          (
        (state-left  (Array Int CompositionState-Left_inst- ))
        (state-right (Array Int CompositionState-Right_inst-))
        (state-length-left  Int) ;old index
        (state-length-right Int) ;old index
        (state-left-new  Return_Left_inst-_keys_top_GETAOUT)
        (state-right-new Return_Right_inst-_keys_top_GETAOUT)
        (h Int))
    Bool
(let (
      (state-left-nov  (select  (return-Left_inst--keys_top-GETAOUT-state        state-left-new)
                                (return-Left_inst--keys_top-GETAOUT-state-length state-left-new)
                                ))
      (state-right-nov (select  (return-Right_inst--keys_top-GETAOUT-state        state-right-new)
                                (return-Right_inst--keys_top-GETAOUT-state-length state-right-new)
                                ))
     )

    (let

; state of the key packages
(
(top-key-package-left  (project-State_Left_inst-_keys_top      (composition-pkgstate-Left_inst--keys_top     state-left-nov  )))
(top-key-package-right (project-State_Right_inst-_keys_top     (composition-pkgstate-Right_inst--keys_top    state-right-nov )))
(bot-key-package-left  (project-State_Left_inst-_keys_bottom   (composition-pkgstate-Left_inst--keys_bottom  state-left-nov  )))
(bot-key-package-right (project-State_Right_inst-_keys_bottom  (composition-pkgstate-Right_inst--keys_bottom state-right-nov )))
)

(let

; table of the bottom key package
(
(table-bot-left  (state-keys-T    bot-key-package-left))
(table-bot-right (state-keys-T    bot-key-package-right))
(    z-bot-left  (state-keys-z    bot-key-package-left))
(    z-bot-right (state-keys-z    bot-key-package-right))
(flag-bot-left   (state-keys-flag bot-key-package-left))
(flag-bot-right  (state-keys-flag bot-key-package-right))
)

(and
;top key package states are equal
(= top-key-package-left top-key-package-right)

;for bottom key package, tables are equal
(= table-bot-left table-bot-right)

;top key package state is "good"
(well-defined-Key-active top-key-package-left )
(well-defined-Key-active top-key-package-right)

;bottom key packages state is "good"
(well-defined-Key-bool   bot-key-package-left )
(well-defined-Key-active bot-key-package-right)
(forall ((h Int))
(and
    (= (select  flag-bot-left  h) 
       (select  flag-bot-right h))
(=> (= (select table-bot-left  h) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
    (= (select  flag-bot-left  h) (   mk-some        false)))
(=> (= (select table-bot-right h) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
    (and
    (= (select  flag-bot-right h) (   mk-some        false))
    (= (select     z-bot-right h) (as mk-none (Maybe Bool )))))
(=> (= (select  flag-bot-right h) (   mk-some        false))
    (= (select     z-bot-right h) (as mk-none (Maybe Bool ))))
)))))))

(define-fun invariant-GETKEYSIN      (
        (state-left  (Array Int CompositionState-Left_inst- ))
        (state-right (Array Int CompositionState-Right_inst-))
        (state-length-left  Int) ;old index
        (state-length-right Int) ;old index
        (state-left-new  Return_Left_inst-_keys_bottom_GETKEYSIN)
        (state-right-new Return_Right_inst-_keys_bottom_GETKEYSIN)
        (h Int))
    Bool
    (let

; state of the key packages
(
(top-key-package-left  (project-State_Left_inst-_keys_top      (composition-pkgstate-Left_inst--keys_top     (select state-left  state-length-left))))
(top-key-package-right (project-State_Right_inst-_keys_top     (composition-pkgstate-Right_inst--keys_top    (select state-right state-length-right))))
(bot-key-package-left  (project-State_Left_inst-_keys_bottom   (composition-pkgstate-Left_inst--keys_bottom  (select state-left  state-length-left))))
(bot-key-package-right (project-State_Right_inst-_keys_bottom  (composition-pkgstate-Right_inst--keys_bottom (select state-right state-length-right))))
)

(let

; table of the bottom key package
(
(table-bot-left  (state-keys-T    bot-key-package-left))
(table-bot-right (state-keys-T    bot-key-package-right))
(    z-bot-left  (state-keys-z    bot-key-package-left))
(    z-bot-right (state-keys-z    bot-key-package-right))
(flag-bot-left   (state-keys-flag bot-key-package-left))
(flag-bot-right  (state-keys-flag bot-key-package-right))
)

(and
;top key package states are equal
(= top-key-package-left top-key-package-right)

;for bottom key package, tables are equal
(= table-bot-left table-bot-right)

;top key package state is "good"
(well-defined-Key-active top-key-package-left )
(well-defined-Key-active top-key-package-right)

;bottom key packages state is "good"
(well-defined-Key-bool   bot-key-package-left )
(well-defined-Key-active bot-key-package-right)
(forall ((h Int))
(and
    (= (select  flag-bot-left  h) 
       (select  flag-bot-right h))
(=> (= (select table-bot-left  h) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
    (= (select  flag-bot-left  h) (   mk-some        false)))
(=> (= (select table-bot-right h) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
    (and
    (= (select  flag-bot-right h) (   mk-some        false))
    (= (select     z-bot-right h) (as mk-none (Maybe Bool )))))
(=> (= (select  flag-bot-right h) (   mk-some        false))
    (= (select     z-bot-right h) (as mk-none (Maybe Bool ))))
))))))


(define-fun invariant-GETKEYSIN-post          (
        (state-left  (Array Int CompositionState-Left_inst- ))
        (state-right (Array Int CompositionState-Right_inst-))
        (state-length-left  Int) ;old index
        (state-length-right Int) ;old index
        (state-left-new  Return_Left_inst-_keys_bottom_GETKEYSIN)
        (state-right-new Return_Right_inst-_keys_bottom_GETKEYSIN)
        (h Int))
    Bool
(let (
      (state-left-nov  (select  (return-Left_inst--keys_bottom-GETKEYSIN-state        state-left-new)
                                (return-Left_inst--keys_bottom-GETKEYSIN-state-length state-left-new)
                                ))
      (state-right-nov (select  (return-Right_inst--keys_bottom-GETKEYSIN-state        state-right-new)
                                (return-Right_inst--keys_bottom-GETKEYSIN-state-length state-right-new)
                                ))
     )

    (let

; state of the key packages
(
(top-key-package-left  (project-State_Left_inst-_keys_top      (composition-pkgstate-Left_inst--keys_top     state-left-nov  )))
(top-key-package-right (project-State_Right_inst-_keys_top     (composition-pkgstate-Right_inst--keys_top    state-right-nov )))
(bot-key-package-left  (project-State_Left_inst-_keys_bottom   (composition-pkgstate-Left_inst--keys_bottom  state-left-nov  )))
(bot-key-package-right (project-State_Right_inst-_keys_bottom  (composition-pkgstate-Right_inst--keys_bottom state-right-nov )))
)

(let

; table of the bottom key package
(
(table-bot-left  (state-keys-T    bot-key-package-left))
(table-bot-right (state-keys-T    bot-key-package-right))
(    z-bot-left  (state-keys-z    bot-key-package-left))
(    z-bot-right (state-keys-z    bot-key-package-right))
(flag-bot-left   (state-keys-flag bot-key-package-left))
(flag-bot-right  (state-keys-flag bot-key-package-right))
)

(and
;top key package states are equal
(= top-key-package-left top-key-package-right)

;for bottom key package, tables are equal
(= table-bot-left table-bot-right)

;top key package state is "good"
(well-defined-Key-active top-key-package-left )
(well-defined-Key-active top-key-package-right)

;bottom key packages state is "good"
(well-defined-Key-bool   bot-key-package-left )
(well-defined-Key-active bot-key-package-right)
(forall ((h Int))
(and
    (= (select  flag-bot-left  h) 
       (select  flag-bot-right h))
(=> (= (select table-bot-left  h) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
    (= (select  flag-bot-left  h) (   mk-some        false)))
(=> (= (select table-bot-right h) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
    (and
    (= (select  flag-bot-right h) (   mk-some        false))
    (= (select     z-bot-right h) (as mk-none (Maybe Bool )))))
(=> (= (select  flag-bot-right h) (   mk-some        false))
    (= (select     z-bot-right h) (as mk-none (Maybe Bool ))))
)))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;    LEFT aborts
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(define-fun left-all-aborts          (
        (state-left (Array Int CompositionState-Left_inst-))
        (state-right (Array Int CompositionState-Right_inst-))
        (state-length-left Int)  ; old index
        (state-length-right Int) ; old index
        (state-left-NEU Return_Left_inst-_gate_GBLG)      
        (state-right-NEU Return_Right_inst-_simgate_GBLG) 
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool


    (let (
      (state-left-1  (select  (return-Left_inst--gate-GBLG-state state-left-NEU)
                                1))
    )

  (let

; state of the key packages
(
(top-key-package-left-1     (project-State_Left_inst-_keys_top     (composition-pkgstate-Left_inst--keys_top     state-left-1)))
(bottom-key-package-left-1  (project-State_Left_inst-_keys_bottom  (composition-pkgstate-Left_inst--keys_bottom  state-left-1)))
)

(let

; table of the top key package
;        T: Table(Integer,Table(Bool,Bits(n))),
;        z: Table(Integer,Bool),
(
(T-top-left-1        (state-keys-T       top-key-package-left-1))
(z-top-left-1        (state-keys-z       top-key-package-left-1))
(flag-top-left-1     (state-keys-flag    top-key-package-left-1))
(flag-bot-left-1     (state-keys-flag bottom-key-package-left-1))
)

;;; if l is undefined, then abort
(=>
(or
(= (select    z-top-left-1 l) (as mk-none (Maybe Bool)))
(= (select flag-top-left-1 l) (as mk-none (Maybe Bool)))
(= (select flag-top-left-1 l)    (mk-some        false))
(= (select    z-top-left-1 r) (as mk-none (Maybe Bool)))
(= (select flag-top-left-1 r) (as mk-none (Maybe Bool)))
(= (select flag-top-left-1 r)    (mk-some        false))
(= (select flag-bot-left-1 j)    (mk-some        true ))
)
(= (return-Left_inst--gate-GBLG-is-abort state-left-NEU) true)
)))))

(define-fun left-inverse-all-aborts          (
        (state-left  (Array Int CompositionState-Left_inst-))
        (state-right (Array Int CompositionState-Right_inst-))
        (state-length-left  Int) ; old index
        (state-length-right Int) ; old index
        (state-left-NEU  Return_Left_inst-_gate_GBLG)      
        (state-right-NEU Return_Right_inst-_simgate_GBLG) 
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool


    (let (
      (state-left-1  (select  (return-Left_inst--gate-GBLG-state state-left-NEU)
                                ;(return-Left_inst--gate-GBLG-state-length state-left-NEU)
                                1))
    )

  (let

; state of the key packages
(
(top-key-package-left-1     (project-State_Left_inst-_keys_top     (composition-pkgstate-Left_inst--keys_top     state-left-1)))
(bottom-key-package-left-1  (project-State_Left_inst-_keys_bottom  (composition-pkgstate-Left_inst--keys_bottom  state-left-1)))
;(top-key-package-left-2     (project-State_Left_inst-_keys_top  (composition-pkgstate-Left_inst--keys_top state-left-2)))
)

(let

; table of the top key package
;        T: Table(Integer,Table(Bool,Bits(n))),
;        z: Table(Integer,Bool),
(
(T-top-left-1        (state-keys-T    top-key-package-left-1))
(z-top-left-1        (state-keys-z    top-key-package-left-1))
(flag-top-left-1     (state-keys-flag top-key-package-left-1))
(flag-bot-left-1  (state-keys-flag bottom-key-package-left-1))
)

;;; abort => z[l] or z[r] is undefined or flag[j]=true
(=>
(= (return-Left_inst--gate-GBLG-is-abort state-left-NEU) true)
(or
(= (select    z-top-left-1 l) (as mk-none (Maybe Bool)))
(= (select flag-top-left-1 l) (as mk-none (Maybe Bool)))
(= (select flag-top-left-1 l)    (mk-some        false))
(= (select    z-top-left-1 r) (as mk-none (Maybe Bool)))
(= (select flag-top-left-1 r) (as mk-none (Maybe Bool)))
(= (select flag-top-left-1 r)    (mk-some        false))
(= (select flag-bot-left-1 j)    (mk-some        true ))
)
)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;    RIGHT aborts
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun right-all-aborts          (
        (state-left     (Array Int CompositionState-Left_inst-))
        (state-right    (Array Int CompositionState-Right_inst-))
        (state-length-left Int)  ; old index
        (state-length-right Int) ; old index
        (state-left-NEU  Return_Left_inst-_gate_GBLG)      ; old index
        (state-right-NEU Return_Right_inst-_simgate_GBLG) ; old index
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool


    (let (
      (state-right-1  (select  state-right state-length-right)
                                ;(return-Left_inst--gate-GBLG-state-length state-left-NEU)
                                ;1))
    ))

  (let

; state of the key packages
(
(bottom-key-package-right-1    (project-State_Right_inst-_keys_bottom  (composition-pkgstate-Right_inst--keys_bottom  state-right-1)))
(top-key-package-right-1       (project-State_Right_inst-_keys_top     (composition-pkgstate-Right_inst--keys_top     state-right-1)))
)


(let

; tables of the top and bottom key package
(
(   T-top-right-1  (state-keys-T       top-key-package-right-1))
(   z-top-right-1  (state-keys-z       top-key-package-right-1))
(flag-top-right-1  (state-keys-flag    top-key-package-right-1))
(flag-bot-right-1  (state-keys-flag bottom-key-package-right-1))
(   z-bot-right-1  (state-keys-z    bottom-key-package-right-1))
)

;;; if j is true, then abort
(=>
(or
(= (select    z-top-right-1 l) (as mk-none (Maybe Bool)))
(= (select flag-top-right-1 l) (as mk-none (Maybe Bool)))
(= (select flag-top-right-1 l)    (mk-some        false))
(= (select    z-top-right-1 r) (as mk-none (Maybe Bool)))
(= (select flag-top-right-1 r) (as mk-none (Maybe Bool)))
(= (select flag-top-right-1 r)    (mk-some        false))
(= (select flag-bot-right-1 j)    (mk-some        true ))
(= (select    z-bot-right-1 j)    (mk-some        true ))
(= (select    z-bot-right-1 j)    (mk-some        false))
)
(= (return-Right_inst--simgate-GBLG-is-abort state-right-NEU) true)
)))))


(define-fun right-all-aborts-inverse          (
        (state-left        (Array Int CompositionState-Left_inst- ))
        (state-right       (Array Int CompositionState-Right_inst-))
        (state-length-left  Int) ; old index
        (state-length-right Int) ; old index
        (state-left-NEU     Return_Left_inst-_gate_GBLG)     ; contains own index
        (state-right-NEU    Return_Right_inst-_simgate_GBLG) ; contains own index
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool

  (let

; state of the key packages
(
(bottom-key-package-right-1    (project-State_Right_inst-_keys_bottom  (composition-pkgstate-Right_inst--keys_bottom  (select state-right state-length-right))))
(   top-key-package-right-1    (project-State_Right_inst-_keys_top     (composition-pkgstate-Right_inst--keys_top     (select state-right state-length-right))))
)


(let

; table of the bottom key package
(
(   T-top-right-1     (state-keys-T       top-key-package-right-1))
(   z-top-right-1     (state-keys-z       top-key-package-right-1))
(flag-top-right-1     (state-keys-flag    top-key-package-right-1))
(flag-bottom-right-1  (state-keys-flag bottom-key-package-right-1))
(   z-bottom-right-1  (state-keys-z    bottom-key-package-right-1))
)

;;; abort => input on l or z not defined or output was already defined.
(=>
(= (return-Right_inst--simgate-GBLG-is-abort state-right-NEU) true)
(or
(= (select    z-top-right-1    l)    (as mk-none (Maybe Bool)))
(= (select flag-top-right-1    l)    (as mk-none (Maybe Bool)))
(= (select flag-top-right-1    l)       (mk-some        false))
(= (select    z-top-right-1    r)    (as mk-none (Maybe Bool)))
(= (select flag-top-right-1    r)    (as mk-none (Maybe Bool)))
(= (select flag-top-right-1    r)       (mk-some        false))
(= (select flag-bottom-right-1 j)       (mk-some        true ))
(= (select    z-bottom-right-1 j)       (mk-some        true ))
(= (select    z-bottom-right-1 j)       (mk-some        false))
)
))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;    LEFT aborts = RIGHT aborts
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun aborts-equal          (
        (state-left  (Array Int CompositionState-Left_inst-))
        (state-right (Array Int CompositionState-Right_inst-))
        (state-length-left  Int) ; old index = 1
        (state-length-right Int) ; old index = 1
        (state-left-NEU Return_Left_inst-_gate_GBLG)      ; also contains new index    
        (state-right-NEU Return_Right_inst-_simgate_GBLG) ; also contains new index
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool


(= (return-Left_inst--gate-GBLG-is-abort     state-left-NEU)
   (return-Right_inst--simgate-GBLG-is-abort state-right-NEU))
)

(define-fun aborts-equal-SETBIT          (
        (state-left  (Array Int CompositionState-Left_inst-))
        (state-right (Array Int CompositionState-Right_inst-))
        (state-length-left  Int) ; old index = 1
        (state-length-right Int) ; old index = 1
        (state-left-NEU Return_Left_inst-_keys_top_SETBIT)      ; also contains new index    
        (state-right-NEU Return_Right_inst-_keys_top_SETBIT) ; also contains new index
        (h Int)
        (zz Bool))
        Bool


(= (return-Left_inst--keys_top-SETBIT-is-abort     state-left-NEU)
   (return-Right_inst--keys_top-SETBIT-is-abort state-right-NEU))
)

(define-fun aborts-equal-GETAOUT          (
        (state-left  (Array Int CompositionState-Left_inst-))
        (state-right (Array Int CompositionState-Right_inst-))
        (state-length-left  Int) ; old index = 1
        (state-length-right Int) ; old index = 1
        (state-left-NEU Return_Left_inst-_keys_top_GETAOUT)      ; also contains new index    
        (state-right-NEU Return_Right_inst-_keys_top_GETAOUT) ; also contains new index
        (h Int))
        Bool


(= (return-Left_inst--keys_top-GETAOUT-is-abort  state-left-NEU)
   (return-Right_inst--keys_top-GETAOUT-is-abort state-right-NEU))
)


(define-fun aborts-equal-GETKEYSIN          (
        (state-left  (Array Int CompositionState-Left_inst-))
        (state-right (Array Int CompositionState-Right_inst-))
        (state-length-left  Int) ; old index = 1
        (state-length-right Int) ; old index = 1
        (state-left-NEU Return_Left_inst-_keys_bottom_GETKEYSIN)      ; also contains new index    
        (state-right-NEU Return_Right_inst-_keys_bottom_GETKEYSIN) ; also contains new index
        (h Int))
        Bool


(= (return-Left_inst--keys_bottom-GETKEYSIN-is-abort  state-left-NEU)
   (return-Right_inst--keys_bottom-GETKEYSIN-is-abort state-right-NEU))
)

(define-fun aborts-left-right          (
        (state-left  (Array Int CompositionState-Left_inst-))
        (state-right (Array Int CompositionState-Right_inst-))
        (state-length-left  Int) ; old index = 1
        (state-length-right Int) ; old index = 1
        (state-left-NEU Return_Left_inst-_gate_GBLG)      ; also contains new index    
        (state-right-NEU Return_Right_inst-_simgate_GBLG) ; also contains new index
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool


(=> (return-Left_inst--gate-GBLG-is-abort     state-left-NEU)
    (return-Right_inst--simgate-GBLG-is-abort state-right-NEU))
)

(define-fun aborts-right-left          (
        (state-left  (Array Int CompositionState-Left_inst-))
        (state-right (Array Int CompositionState-Right_inst-))
        (state-length-left  Int) ; old index = 1
        (state-length-right Int) ; old index = 1
        (state-left-NEU Return_Left_inst-_gate_GBLG)      ; also contains new index    
        (state-right-NEU Return_Right_inst-_simgate_GBLG) ; also contains new index
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool


(=> (return-Right_inst--simgate-GBLG-is-abort state-right-NEU)
    (return-Left_inst--gate-GBLG-is-abort     state-left-NEU ))
)


; no-abort

(define-fun no-abort          (
        (state-left  (Array Int CompositionState-Left_inst-))
        (state-right (Array Int CompositionState-Right_inst-))
        (state-length-left  Int) ; old index = 1
        (state-length-right Int) ; old index = 1
        (state-left-NEU Return_Left_inst-_gate_GBLG)      ; also contains new index    
        (state-right-NEU Return_Right_inst-_simgate_GBLG) ; also contains new index
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool

(and
(= (return-Left_inst--gate-GBLG-is-abort     state-left-NEU)
   false)
(= (return-Right_inst--simgate-GBLG-is-abort     state-right-NEU)
   false)
))

(define-fun no-abort-SETBIT          (
        (state-left  (Array Int CompositionState-Left_inst-))
        (state-right (Array Int CompositionState-Right_inst-))
        (state-length-left  Int) ; old index = 1
        (state-length-right Int) ; old index = 1
        (state-left-NEU  Return_Left_inst-_keys_top_SETBIT)  ; also contains new index    
        (state-right-NEU Return_Right_inst-_keys_top_SETBIT) ; also contains new index
        (h Int)
        (zz Bool))
        Bool

(and
(= (return-Left_inst--keys_top-SETBIT-is-abort     state-left-NEU)
   false)
(= (return-Right_inst--keys_top-SETBIT-is-abort     state-right-NEU)
   false)
))

(define-fun no-abort-GETAOUT          (
        (state-left  (Array Int CompositionState-Left_inst-))
        (state-right (Array Int CompositionState-Right_inst-))
        (state-length-left  Int) ; old index = 1
        (state-length-right Int) ; old index = 1
        (state-left-NEU  Return_Left_inst-_keys_top_GETAOUT)  ; also contains new index    
        (state-right-NEU Return_Right_inst-_keys_top_GETAOUT) ; also contains new index
        (h Int))
        Bool

(and
(= (return-Left_inst--keys_top-GETAOUT-is-abort     state-left-NEU)
   false)
(= (return-Right_inst--keys_top-GETAOUT-is-abort     state-right-NEU)
   false)
))

(define-fun no-abort-GETKEYSIN          (
        (state-left  (Array Int CompositionState-Left_inst-))
        (state-right (Array Int CompositionState-Right_inst-))
        (state-length-left  Int) ; old index = 1
        (state-length-right Int) ; old index = 1
        (state-left-NEU  Return_Left_inst-_keys_bottom_GETKEYSIN)  ; also contains new index    
        (state-right-NEU Return_Right_inst-_keys_bottom_GETKEYSIN) ; also contains new index
        (h Int))
        Bool

(and
(= (return-Left_inst--keys_bottom-GETKEYSIN-is-abort     state-left-NEU)
   false)
(= (return-Right_inst--keys_bottom-GETKEYSIN-is-abort     state-right-NEU)
   false)
))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;    State lemma: top left = top right
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define-fun top-whole-left-neu-right-neu          (
        (state-left (Array Int CompositionState-Left_inst-))
        (state-right (Array Int CompositionState-Right_inst-))
        (state-length-left  Int) ;old index
        (state-length-right Int) ;old index
        (state-left-NEU Return_Left_inst-_gate_GBLG)
        (state-right-NEU Return_Right_inst-_simgate_GBLG)
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool


    (let (
      (state-left-neu (select   (return-Left_inst--gate-GBLG-state state-left-NEU)
                                (return-Left_inst--gate-GBLG-state-length state-left-NEU)))
      (state-right-neu (select  (return-Right_inst--simgate-GBLG-state state-right-NEU)
                                (return-Right_inst--simgate-GBLG-state-length state-right-NEU)))
    )

  (let

; state of the key packages
(
(   top-key-package-left-neu  (project-State_Left_inst-_keys_top     (composition-pkgstate-Left_inst--keys_top     state-left-neu)))
(   top-key-package-right-neu (project-State_Right_inst-_keys_top    (composition-pkgstate-Right_inst--keys_top    state-right-neu)))
(bottom-key-package-left-neu  (project-State_Left_inst-_keys_bottom  (composition-pkgstate-Left_inst--keys_bottom  state-left-neu)))
(bottom-key-package-right-neu (project-State_Right_inst-_keys_bottom (composition-pkgstate-Right_inst--keys_bottom state-right-neu)))
)


;;; top key packages have equal state
(= top-key-package-left-neu top-key-package-right-neu)


)))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;    State lemmas Left_inst-
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Only need to consider the bottom key package,
; because the top key package does not change
; and CVC5 has no problems proving this.
;
; no abort   =>  Position h now contains Z
; unconditional: Everywhere else same as old
;
; Approach: precondition = no-abort and 
; full characterization of no-abort
; The latter two things only come in the TOML
;
;  New Implementation:
;  bot-left-neu: characterization of new left table

(declare-const Z (Array Bool (Maybe Bits_n)))

(define-fun bot-left-neu          (
        (state-left  (Array Int CompositionState-Left_inst-))
        (state-right (Array Int CompositionState-Right_inst-))
        (state-length-left Int)  ; old index
        (state-length-right Int) ; old index
        (state-left-NEU  Return_Left_inst-_gate_GBLG)    
        (state-right-NEU Return_Right_inst-_simgate_GBLG)
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool


    (let (
      (state-left-1  (select  (return-Left_inst--gate-GBLG-state state-left-NEU)
                                ;(return-Left_inst--gate-GBLG-state-length state-left-NEU)
                                1))
      (state-left-2  (select  (return-Left_inst--gate-GBLG-state state-left-NEU)
                                ;(return-Left_inst--gate-GBLG-state-length state-left-NEU)
                                2))
      (state-left-neu  (select  (return-Left_inst--gate-GBLG-state state-left-NEU)
                              (return-Left_inst--gate-GBLG-state-length state-left-NEU)
                                 ))
    )

  (let

; state of the bottom key packages
(
(bottom-key-package-left-1     (project-State_Left_inst-_keys_bottom  (composition-pkgstate-Left_inst--keys_bottom  state-left-1)))
(bottom-key-package-left-neu   (project-State_Left_inst-_keys_bottom  (composition-pkgstate-Left_inst--keys_bottom  state-left-neu)))
)

(let
(
              ;assignment of the sampled values for the lower Key package as a table
              (Z-left (store (store Z
                  false (mk-some randval-left-6))
                  true  (mk-some randval-left-5)))
)


(let
(
              ; table of the bottom key package
              (   T-bottom-left-1     (state-keys-T    bottom-key-package-left-1))
              (   z-bottom-left-1     (state-keys-z    bottom-key-package-left-1))
              (flag-bottom-left-1     (state-keys-flag bottom-key-package-left-1))
              (   T-bottom-left-neu   (state-keys-T    bottom-key-package-left-neu))
              (   z-bottom-left-neu   (state-keys-z    bottom-key-package-left-neu))
              (flag-bottom-left-neu   (state-keys-flag bottom-key-package-left-neu))
)

;;; characerization of bottom key package state
(forall ((h Int))
     (ite 
     (= h j)
     (and
     (= (select    T-bottom-left-neu h) (mk-some Z-left))
     (= (select flag-bottom-left-neu h) (mk-some true  ))
     )
     (and
     (= (select    T-bottom-left-neu h) (select    T-bottom-left-1 h))
     (= (select    z-bottom-left-neu h) (select    z-bottom-left-1 h))
     (= (select flag-bottom-left-neu h) (select flag-bottom-left-1 h))
     )))
)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;    State lemmas Right_inst-
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define-fun bot-right-neu          (
        (state-left  (Array Int CompositionState-Left_inst-))
        (state-right (Array Int CompositionState-Right_inst-))
        (state-length-left Int)  ; old index
        (state-length-right Int) ; old index
        (state-left-NEU  Return_Left_inst-_gate_GBLG)    
        (state-right-NEU Return_Right_inst-_simgate_GBLG)
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool


    (let (
      (state-right-1   (select  (return-Right_inst--simgate-GBLG-state state-right-NEU)
                                ;(return-Left_inst--gate-GBLG-state-length state-left-NEU)
                                1))
      (state-right-2   (select  (return-Right_inst--simgate-GBLG-state state-right-NEU)
                                ;(return-Left_inst--gate-GBLG-state-length state-left-NEU)
                                2))
      (state-right-neu (select  (return-Right_inst--simgate-GBLG-state        state-right-NEU)
                                (return-Right_inst--simgate-GBLG-state-length state-right-NEU)
                                 ))
    )

  (let

; state of the bottom key packages
(
(bottom-key-package-right-1     (project-State_Right_inst-_keys_bottom  (composition-pkgstate-Right_inst--keys_bottom  state-right-1)))
(bottom-key-package-right-neu   (project-State_Right_inst-_keys_bottom  (composition-pkgstate-Right_inst--keys_bottom  state-right-neu)))
)

(let
(
              ;assignment of the sampled values for the lower Key package as a table
              (Z-right (store (store Z
                  false (mk-some randval-right-8))
                  true  (mk-some randval-right-7)))
)


(let
(
              ; table of the bottom key package
              (   T-bottom-right-1     (state-keys-T    bottom-key-package-right-1))
              (   z-bottom-right-1     (state-keys-z    bottom-key-package-right-1))
              (flag-bottom-right-1     (state-keys-flag bottom-key-package-right-1))
              (   T-bottom-right-neu   (state-keys-T    bottom-key-package-right-neu))
              (   z-bottom-right-neu   (state-keys-z    bottom-key-package-right-neu))
              (flag-bottom-right-neu   (state-keys-flag bottom-key-package-right-neu))
)

;;; characerization of bottom key package state
(forall ((h Int))
     (ite 
     (= h j)
     (and
     (= (select    T-bottom-right-neu h) (mk-some Z-right))
     (= (select flag-bottom-right-neu h) (mk-some true  ))
     )
     (and
     (= (select    T-bottom-right-neu h) (select    T-bottom-right-1 h))
     (= (select    z-bottom-right-neu h) (select    z-bottom-right-1 h))
     (= (select flag-bottom-right-neu h) (select flag-bottom-right-1 h))
     )))
)))))

(define-fun temp         (
        (state-left  (Array Int CompositionState-Left_inst-))
        (state-right (Array Int CompositionState-Right_inst-))
        (state-length-left Int)  ; old index
        (state-length-right Int) ; old index
        (state-left-NEU  Return_Left_inst-_gate_GBLG)    
        (state-right-NEU Return_Right_inst-_simgate_GBLG)
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool


    (let (
      (state-left-neu  (select  (return-Left_inst--gate-GBLG-state            state-left-NEU)
                                (return-Left_inst--gate-GBLG-state-length     state-left-NEU)))
      (state-right-neu (select  (return-Right_inst--simgate-GBLG-state        state-right-NEU)
                                (return-Right_inst--simgate-GBLG-state-length state-right-NEU)))
         )   

  (let

; state of the bottom key packages
(
(bottom-key-package-left-neu    (project-State_Left_inst-_keys_bottom   (composition-pkgstate-Left_inst--keys_bottom   state-left-neu)))
(bottom-key-package-right-neu   (project-State_Right_inst-_keys_bottom  (composition-pkgstate-Right_inst--keys_bottom  state-right-neu)))
)


(let
(
              ; table of the bottom key package
              (T-bottom-right-neu   (state-keys-T    bottom-key-package-right-neu))
              (T-bottom-left-neu    (state-keys-T    bottom-key-package-left-neu))
)

;;; characerization of bottom key package state
     (= T-bottom-left-neu T-bottom-right-neu)
))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;  OLD
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  Old Implementation:
;                  bot-Z-left-2: After first call, Z is stored at h. 23:07
;  bot-except-left-neu-left-alt: Same as before except for h.        seconds
;     bot-table-left-2-left-neu: Does not change later.              seconds



(define-fun bot-Z-left-2          (
        (state-left  (Array Int CompositionState-Left_inst-))
        (state-right (Array Int CompositionState-Right_inst-))
        (state-length-left Int)  ; old index
        (state-length-right Int) ; old index
        (state-left-NEU  Return_Left_inst-_gate_GBLG)    
        (state-right-NEU Return_Right_inst-_simgate_GBLG)
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool


    (let (
      (state-left-1  (select  (return-Left_inst--gate-GBLG-state state-left-NEU)
                                ;(return-Left_inst--gate-GBLG-state-length state-left-NEU)
                                1))
      (state-left-2  (select  (return-Left_inst--gate-GBLG-state state-left-NEU)
                                ;(return-Left_inst--gate-GBLG-state-length state-left-NEU)
                                2))
    )

  (let

; state of the bottom key packages
(
(bottom-key-package-left-1     (project-State_Left_inst-_keys_bottom  (composition-pkgstate-Left_inst--keys_bottom  state-left-1)))
(bottom-key-package-left-2     (project-State_Left_inst-_keys_bottom  (composition-pkgstate-Left_inst--keys_bottom  state-left-2)))
)

(let
(
              ;assignment of the sampled values for the lower Key package as a table
              (Z-left (store (store Z
                  false (mk-some randval-left-6))
                  true  (mk-some randval-left-5)))
)


(let
(
              ; table of the bottom key package
              (flag-bottom-left-1  (state-keys-flag bottom-key-package-left-1))
              ;(T-bottom-left-1     (state-keys-T    bottom-key-package-left-1))
              (T-bottom-left-2     (state-keys-T    bottom-key-package-left-2))
)

;;; top key packages have equal state
(=>
(not (= (select flag-bottom-left-1 j) (mk-some true)))
     (= (select    T-bottom-left-2 j) (mk-some Z-left))
))))))

(define-fun bot-except-left-neu-left-alt      (
        (state-left-alt (Array Int CompositionState-Left_inst-))
        (state-right (Array Int CompositionState-Right_inst-))
        (state-length-left-old Int)
        (state-length-right-old Int)
        (state-left-NEU Return_Left_inst-_gate_GBLG)
        (state-right-NEU Return_Right_inst-_simgate_GBLG)
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
    Bool


    (let (
      (state-left-neu (select   (return-Left_inst--gate-GBLG-state state-left-NEU)
                                (return-Left_inst--gate-GBLG-state-length state-left-NEU)))
    )

    (let

; state of the key packages
(
(top-key-package-left-alt (project-State_Left_inst-_keys_top       (composition-pkgstate-Left_inst--keys_top    (select state-left-alt state-length-left-old))))
(top-key-package-left-neu (project-State_Left_inst-_keys_top       (composition-pkgstate-Left_inst--keys_top    state-left-neu)))
(bottom-key-package-left-alt (project-State_Left_inst-_keys_bottom (composition-pkgstate-Left_inst--keys_bottom (select state-left-alt state-length-left-old))))
(bottom-key-package-left-neu (project-State_Left_inst-_keys_bottom (composition-pkgstate-Left_inst--keys_bottom state-left-neu)))
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
(forall ((hh Int))
(=>
(not
(and (= j hh) (= (select table-bottom-left-alt hh) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))))
(= (select table-bottom-left-alt hh) (select table-bottom-left-neu hh))
)))))))

(define-fun bot-table-left-2-left-neu
          (
        (state-left  (Array Int CompositionState-Left_inst-))
        (state-right (Array Int CompositionState-Right_inst-))
        (state-length-left  Int) ; length of old state
        (state-length-right Int) ; length of old state
        (state-left-NEU Return_Left_inst-_gate_GBLG)
        (state-right-NEU Return_Right_inst-_simgate_GBLG)
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool


    (let (
      (state-left-neu  (select  (return-Left_inst--gate-GBLG-state        state-left-NEU)
                                (return-Left_inst--gate-GBLG-state-length state-left-NEU)
                              ))
      (state-left-2  (select  (return-Left_inst--gate-GBLG-state state-left-NEU)
                                ;(return-Left_inst--gate-GBLG-state-length state-left-NEU)
                                2))                          
    )

  (let

; state of the key packages
(
(bottom-key-package-left-neu  (project-State_Left_inst-_keys_bottom (composition-pkgstate-Left_inst--keys_bottom state-left-neu)))
(bottom-key-package-left-2    (project-State_Left_inst-_keys_bottom (composition-pkgstate-Left_inst--keys_bottom state-left-2)))
)

;; bottom key left = bottom key right
(and
(= bottom-key-package-left-neu bottom-key-package-left-2)
)

)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Same Output
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun same-output          (
        (state-left (Array Int CompositionState-Left_inst-))
        (state-right (Array Int CompositionState-Right_inst-))
        (state-length-left-old Int)
        (state-length-right-old Int)
        (state-left-NEU Return_Left_inst-_gate_GBLG)
        (state-right-NEU Return_Right_inst-_simgate_GBLG)
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool
(=
(return-Left_inst--gate-GBLG-value return-left-gate-GBLG)
(return-Right_inst--simgate-GBLG-value return-right-simgate-GBLG)
)
)

(define-fun same-output-SETBIT          (
        (state-left (Array Int CompositionState-Left_inst-))
        (state-right (Array Int CompositionState-Right_inst-))
        (state-length-left-old Int)
        (state-length-right-old Int)
        (state-left-NEU Return_Left_inst-_keys_top_SETBIT)
        (state-right-NEU Return_Right_inst-_keys_top_SETBIT)
        (h Int)
        (zz Bool))
        Bool
(=
(return-Left_inst--keys_top-SETBIT-value return-left-keys_top-SETBIT)
(return-Right_inst--keys_top-SETBIT-value return-right-keys_top-SETBIT)
)
)

(define-fun same-output-GETAOUT          (
        (state-left (Array Int CompositionState-Left_inst-))
        (state-right (Array Int CompositionState-Right_inst-))
        (state-length-left-old Int)
        (state-length-right-old Int)
        (state-left-NEU Return_Left_inst-_keys_top_GETAOUT)
        (state-right-NEU Return_Right_inst-_keys_top_GETAOUT)
        (h Int))
        Bool
(=
(return-Left_inst--keys_top-GETAOUT-value return-left-keys_top-GETAOUT)
(return-Right_inst--keys_top-GETAOUT-value return-right-keys_top-GETAOUT)
)
)

(define-fun same-output-GETKEYSIN          (
        (state-left (Array Int CompositionState-Left_inst-))
        (state-right (Array Int CompositionState-Right_inst-))
        (state-length-left-old Int)
        (state-length-right-old Int)
        (state-left-NEU Return_Left_inst-_keys_bottom_GETKEYSIN)
        (state-right-NEU Return_Right_inst-_keys_bottom_GETKEYSIN)
        (h Int))
        Bool
(=
(return-Left_inst--keys_bottom-GETKEYSIN-value return-left-keys_bottom-GETKEYSIN)
(return-Right_inst--keys_bottom-GETKEYSIN-value return-right-keys_bottom-GETKEYSIN)
)
)
