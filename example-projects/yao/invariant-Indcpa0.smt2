(assert
(and
(= state-length-left-old 1)
(= state-length-right-old 1)
)
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;   Randomness naming
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(declare-const randval-left-GETA-1 Bits_n)
(assert (= randval-left-GETA-1  (__sample-rand-Indcpamod0-Bits_n  1 randctr-left-1
)))

(declare-const randval-right-GETA-1 Bits_n)
(assert (= randval-right-GETA-1 (__sample-rand-Indcpamon0-Bits_n 1 randctr-right-1
)))

(declare-const randval-left-GETA-2 Bits_n)
(assert (= randval-left-GETA-2  (__sample-rand-Indcpamod0-Bits_n  2 randctr-left-2
)))

(declare-const randval-right-GETA-2 Bits_n)
(assert (= randval-right-GETA-2 (__sample-rand-Indcpamon0-Bits_n 2 randctr-right-2
)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;   Randomness mapping
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


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





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;   Datatypes to extract key package state
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(declare-datatype
  State_keys
  (
    (mk-state-keys
      (state-keys-T (Maybe (Array Bool (Maybe Bits_n))))
      (state-keys-z (Maybe Bool))
      (state-keys-flag (Maybe Bool)))))

(define-fun project-State_Indcpamod0_keys_top ((in State_Indcpamod0_keys_top)) State_keys
  (mk-state-keys (state-Indcpamod0-keys_top-T    in)
                 (state-Indcpamod0-keys_top-z    in)
                 (state-Indcpamod0-keys_top-flag in)))

(define-fun project-State_Indcpamon0_indcpamon0 ((in State_Indcpamon0_indcpamon0)) State_keys
  (mk-state-keys (state-Indcpamon0-indcpamon0-T    in)
                 (state-Indcpamon0-indcpamon0-z    in)
                 (state-Indcpamon0-indcpamon0-flag in)))

(define-fun project-State_Indcpamod0_keys_bottom ((in State_Indcpamod0_keys_bottom)) State_keys
  (mk-state-keys (state-Indcpamod0-keys_bottom-T    in)
                 (state-Indcpamod0-keys_bottom-z    in)
                 (state-Indcpamod0-keys_bottom-flag in)))

(define-fun project-State_Indcpamon0_indcpamon0 ((in State_Indcpamon0_indcpamon0)) State_keys
  (mk-state-keys (state-Indcpamon0-indcpamon0-T    in)
                 (state-Indcpamon0-indcpamon0-z    in)
                 (state-Indcpamon0-indcpamon0-flag in)))

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
        (state-left  (Array Int CompositionState-Indcpamod0 ))
        (state-right (Array Int CompositionState-Indcpamon0))
        (state-length-left  Int) ;old index
        (state-length-right Int) ;old index
        (state-left-new  Return_Indcpamod0_gate_GBLG)
        (state-right-new Return_Indcpamon0_simgate_GBLG)
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
    Bool
    (let

; state of the key packages
(
(top-key-package-left  (project-State_Indcpamod0_keys_top      (composition-pkgstate-Indcpamod0-keys_top     (select state-left  state-length-left))))
(top-key-package-right (project-State_Indcpamon0_indcpamon0     (composition-pkgstate-Indcpamon0-indcpamon0    (select state-right state-length-right))))
(bot-key-package-left  (project-State_Indcpamod0_keys_bottom   (composition-pkgstate-Indcpamod0-keys_bottom  (select state-left  state-length-left))))
(bot-key-package-right (project-State_Indcpamon0_indcpamon0  (composition-pkgstate-Indcpamon0-indcpamon0 (select state-right state-length-right))))
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


(define-fun invariant-SETBIT      (
        (state-left  (Array Int CompositionState-Indcpamod0 ))
        (state-right (Array Int CompositionState-Indcpamon0))
        (state-length-left  Int) ;old index
        (state-length-right Int) ;old index
        (state-left-new  Return_Indcpamod0_keys_top_SETBIT)
        (state-right-new Return_Indcpamon0_indcpamon0_SETBIT)
        (h Int)
        (zz Bool))
    Bool
    (let

; state of the key packages
(
(top-key-package-left  (project-State_Indcpamod0_keys_top      (composition-pkgstate-Indcpamod0-keys_top     (select state-left  state-length-left))))
(top-key-package-right (project-State_Indcpamon0_indcpamon0     (composition-pkgstate-Indcpamon0-indcpamon0    (select state-right state-length-right))))
(bot-key-package-left  (project-State_Indcpamod0_keys_bottom   (composition-pkgstate-Indcpamod0-keys_bottom  (select state-left  state-length-left))))
(bot-key-package-right (project-State_Indcpamon0_indcpamon0  (composition-pkgstate-Indcpamon0-indcpamon0 (select state-right state-length-right))))
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
        (state-left  (Array Int CompositionState-Indcpamod0 ))
        (state-right (Array Int CompositionState-Indcpamon0))
        (state-length-left  Int) ;old index
        (state-length-right Int) ;old index
        (state-left-new  Return_Indcpamod0_keys_top_SETBIT)
        (state-right-new Return_Indcpamon0_indcpamon0_SETBIT)
        (h Int)
        (zz Bool))
    Bool
(let (
      (state-left-nov  (select  (return-Indcpamod0-keys_top-SETBIT-state        state-left-new)
                                (return-Indcpamod0-keys_top-SETBIT-state-length state-left-new)
                                ))
      (state-right-nov (select  (return-Indcpamon0-indcpamon0-SETBIT-state        state-right-new)
                                (return-Indcpamon0-indcpamon0-SETBIT-state-length state-right-new)
                                ))
     )

    (let

; state of the key packages
(
(top-key-package-left  (project-State_Indcpamod0_keys_top      (composition-pkgstate-Indcpamod0-keys_top     state-left-nov  )))
(top-key-package-right (project-State_Indcpamon0_indcpamon0     (composition-pkgstate-Indcpamon0-indcpamon0    state-right-nov )))
(bot-key-package-left  (project-State_Indcpamod0_keys_bottom   (composition-pkgstate-Indcpamod0-keys_bottom  state-left-nov  )))
(bot-key-package-right (project-State_Indcpamon0_indcpamon0  (composition-pkgstate-Indcpamon0-indcpamon0 state-right-nov )))
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
        (state-left  (Array Int CompositionState-Indcpamod0 ))
        (state-right (Array Int CompositionState-Indcpamon0))
        (state-length-left  Int) ;old index
        (state-length-right Int) ;old index
        (state-left-new  Return_Indcpamod0_keys_top_GETAOUT)
        (state-right-new Return_Indcpamon0_indcpamon0_GETAOUT)
        (h Int))
    Bool
    (let

; state of the key packages
(
(top-key-package-left  (project-State_Indcpamod0_keys_top      (composition-pkgstate-Indcpamod0-keys_top     (select state-left  state-length-left))))
(top-key-package-right (project-State_Indcpamon0_indcpamon0     (composition-pkgstate-Indcpamon0-indcpamon0    (select state-right state-length-right))))
(bot-key-package-left  (project-State_Indcpamod0_keys_bottom   (composition-pkgstate-Indcpamod0-keys_bottom  (select state-left  state-length-left))))
(bot-key-package-right (project-State_Indcpamon0_indcpamon0  (composition-pkgstate-Indcpamon0-indcpamon0 (select state-right state-length-right))))
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
        (state-left  (Array Int CompositionState-Indcpamod0 ))
        (state-right (Array Int CompositionState-Indcpamon0))
        (state-length-left  Int) ;old index
        (state-length-right Int) ;old index
        (state-left-new  Return_Indcpamod0_keys_top_GETAOUT)
        (state-right-new Return_Indcpamon0_indcpamon0_GETAOUT)
        (h Int))
    Bool
(let (
      (state-left-nov  (select  (return-Indcpamod0-keys_top-GETAOUT-state        state-left-new)
                                (return-Indcpamod0-keys_top-GETAOUT-state-length state-left-new)
                                ))
      (state-right-nov (select  (return-Indcpamon0-indcpamon0-GETAOUT-state        state-right-new)
                                (return-Indcpamon0-indcpamon0-GETAOUT-state-length state-right-new)
                                ))
     )

    (let

; state of the key packages
(
(top-key-package-left  (project-State_Indcpamod0_keys_top      (composition-pkgstate-Indcpamod0-keys_top     state-left-nov  )))
(top-key-package-right (project-State_Indcpamon0_indcpamon0     (composition-pkgstate-Indcpamon0-indcpamon0    state-right-nov )))
(bot-key-package-left  (project-State_Indcpamod0_keys_bottom   (composition-pkgstate-Indcpamod0-keys_bottom  state-left-nov  )))
(bot-key-package-right (project-State_Indcpamon0_indcpamon0  (composition-pkgstate-Indcpamon0-indcpamon0 state-right-nov )))
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
        (state-left (Array Int CompositionState-Indcpamod0))
        (state-right (Array Int CompositionState-Indcpamon0))
        (state-length-left Int)  ; old index
        (state-length-right Int) ; old index
        (state-left-NEU Return_Indcpamod0_gate_GBLG)      
        (state-right-NEU Return_Indcpamon0_simgate_GBLG) 
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool


    (let (
      (state-left-1  (select  (return-Indcpamod0-gate-GBLG-state state-left-NEU)
                                1))
    )

  (let

; state of the key packages
(
(top-key-package-left-1     (project-State_Indcpamod0_keys_top     (composition-pkgstate-Indcpamod0-keys_top     state-left-1)))
(bottom-key-package-left-1  (project-State_Indcpamod0_keys_bottom  (composition-pkgstate-Indcpamod0-keys_bottom  state-left-1)))
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
(= (return-Indcpamod0-gate-GBLG-is-abort state-left-NEU) true)
)))))

(define-fun left-inverse-all-aborts          (
        (state-left  (Array Int CompositionState-Indcpamod0))
        (state-right (Array Int CompositionState-Indcpamon0))
        (state-length-left  Int) ; old index
        (state-length-right Int) ; old index
        (state-left-NEU  Return_Indcpamod0_gate_GBLG)      
        (state-right-NEU Return_Indcpamon0_simgate_GBLG) 
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool


    (let (
      (state-left-1  (select  (return-Indcpamod0-gate-GBLG-state state-left-NEU)
                                ;(return-Indcpamod0-gate-GBLG-state-length state-left-NEU)
                                1))
    )

  (let

; state of the key packages
(
(top-key-package-left-1     (project-State_Indcpamod0_keys_top     (composition-pkgstate-Indcpamod0-keys_top     state-left-1)))
(bottom-key-package-left-1  (project-State_Indcpamod0_keys_bottom  (composition-pkgstate-Indcpamod0-keys_bottom  state-left-1)))
;(top-key-package-left-2     (project-State_Indcpamod0_keys_top  (composition-pkgstate-Indcpamod0-keys_top state-left-2)))
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
(= (return-Indcpamod0-gate-GBLG-is-abort state-left-NEU) true)
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
        (state-left     (Array Int CompositionState-Indcpamod0))
        (state-right    (Array Int CompositionState-Indcpamon0))
        (state-length-left Int)  ; old index
        (state-length-right Int) ; old index
        (state-left-NEU  Return_Indcpamod0_gate_GBLG)      ; old index
        (state-right-NEU Return_Indcpamon0_simgate_GBLG) ; old index
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool


    (let (
      (state-right-1  (select  state-right state-length-right)
                                ;(return-Indcpamod0-gate-GBLG-state-length state-left-NEU)
                                ;1))
    ))

  (let

; state of the key packages
(
(bottom-key-package-right-1    (project-State_Indcpamon0_indcpamon0  (composition-pkgstate-Indcpamon0-indcpamon0  state-right-1)))
(top-key-package-right-1       (project-State_Indcpamon0_indcpamon0     (composition-pkgstate-Indcpamon0-indcpamon0     state-right-1)))
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
(= (return-Indcpamon0-simgate-GBLG-is-abort state-right-NEU) true)
)))))


(define-fun right-all-aborts-inverse          (
        (state-left        (Array Int CompositionState-Indcpamod0 ))
        (state-right       (Array Int CompositionState-Indcpamon0))
        (state-length-left  Int) ; old index
        (state-length-right Int) ; old index
        (state-left-NEU     Return_Indcpamod0_gate_GBLG)     ; contains own index
        (state-right-NEU    Return_Indcpamon0_simgate_GBLG) ; contains own index
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool

  (let

; state of the key packages
(
(bottom-key-package-right-1    (project-State_Indcpamon0_indcpamon0  (composition-pkgstate-Indcpamon0-indcpamon0  (select state-right state-length-right))))
(   top-key-package-right-1    (project-State_Indcpamon0_indcpamon0     (composition-pkgstate-Indcpamon0-indcpamon0     (select state-right state-length-right))))
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
(= (return-Indcpamon0-simgate-GBLG-is-abort state-right-NEU) true)
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

(define-fun aborts-equal-ENC          (
        (state-left  (Array Int CompositionState-Indcpamod0))
        (state-right (Array Int CompositionState-Indcpamon0))
        (state-length-left  Int) ; old index = 1
        (state-length-right Int) ; old index = 1
        (state-left-NEU Return_Indcpamod0_gate_GBLG)      ; also contains new index    
        (state-right-NEU Return_Indcpamon0_simgate_GBLG) ; also contains new index
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool


(= (return-Indcpamod0-gate-GBLG-is-abort     state-left-NEU)
   (return-Indcpamon0-simgate-GBLG-is-abort state-right-NEU))
)

(define-fun aborts-equal-SETBIT          (
        (state-left  (Array Int CompositionState-Indcpamod0))
        (state-right (Array Int CompositionState-Indcpamon0))
        (state-length-left  Int) ; old index = 1
        (state-length-right Int) ; old index = 1
        (state-left-NEU Return_Indcpamod0_keys_top_SETBIT)      ; also contains new index    
        (state-right-NEU Return_Indcpamon0_indcpamon0_SETBIT) ; also contains new index
        (h Int)
        (zz Bool))
        Bool


(= (return-Indcpamod0-keys_top-SETBIT-is-abort     state-left-NEU)
   (return-Indcpamon0-indcpamon0-SETBIT-is-abort state-right-NEU))
)

(define-fun aborts-equal-GETAOUT          (
        (state-left  (Array Int CompositionState-Indcpamod0))
        (state-right (Array Int CompositionState-Indcpamon0))
        (state-length-left  Int) ; old index = 1
        (state-length-right Int) ; old index = 1
        (state-left-NEU Return_Indcpamod0_keys_top_GETAOUT)      ; also contains new index    
        (state-right-NEU Return_Indcpamon0_indcpamon0_GETAOUT) ; also contains new index
        (h Int))
        Bool


(= (return-Indcpamod0-keys_top-GETAOUT-is-abort  state-left-NEU)
   (return-Indcpamon0-indcpamon0-GETAOUT-is-abort state-right-NEU))
)




; no-abort

(define-fun no-abort-ENC          (
        (state-left  (Array Int CompositionState-Indcpamod0))
        (state-right (Array Int CompositionState-Indcpamon0))
        (state-length-left  Int) ; old index = 1
        (state-length-right Int) ; old index = 1
        (state-left-NEU Return_Indcpamod0_gate_GBLG)      ; also contains new index    
        (state-right-NEU Return_Indcpamon0_simgate_GBLG) ; also contains new index
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool

(and
(= (return-Indcpamod0-gate-GBLG-is-abort     state-left-NEU)
   false)
(= (return-Indcpamon0-simgate-GBLG-is-abort     state-right-NEU)
   false)
))

(define-fun no-abort-SETBIT          (
        (state-left  (Array Int CompositionState-Indcpamod0))
        (state-right (Array Int CompositionState-Indcpamon0))
        (state-length-left  Int) ; old index = 1
        (state-length-right Int) ; old index = 1
        (state-left-NEU  Return_Indcpamod0_keys_top_SETBIT)  ; also contains new index    
        (state-right-NEU Return_Indcpamon0_indcpamon0_SETBIT) ; also contains new index
        (h Int)
        (zz Bool))
        Bool

(and
(= (return-Indcpamod0-keys_top-SETBIT-is-abort     state-left-NEU)
   false)
(= (return-Indcpamon0-indcpamon0-SETBIT-is-abort     state-right-NEU)
   false)
))

(define-fun no-abort-GETAOUT          (
        (state-left  (Array Int CompositionState-Indcpamod0))
        (state-right (Array Int CompositionState-Indcpamon0))
        (state-length-left  Int) ; old index = 1
        (state-length-right Int) ; old index = 1
        (state-left-NEU  Return_Indcpamod0_keys_top_GETAOUT)  ; also contains new index    
        (state-right-NEU Return_Indcpamon0_indcpamon0_GETAOUT) ; also contains new index
        (h Int))
        Bool

(and
(= (return-Indcpamod0-keys_top-GETAOUT-is-abort     state-left-NEU)
   false)
(= (return-Indcpamon0-indcpamon0-GETAOUT-is-abort     state-right-NEU)
   false)
))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;    State lemma: top left = top right
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define-fun top-whole-left-neu-right-neu          (
        (state-left (Array Int CompositionState-Indcpamod0))
        (state-right (Array Int CompositionState-Indcpamon0))
        (state-length-left  Int) ;old index
        (state-length-right Int) ;old index
        (state-left-NEU Return_Indcpamod0_gate_GBLG)
        (state-right-NEU Return_Indcpamon0_simgate_GBLG)
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool


    (let (
      (state-left-neu (select   (return-Indcpamod0-gate-GBLG-state state-left-NEU)
                                (return-Indcpamod0-gate-GBLG-state-length state-left-NEU)))
      (state-right-neu (select  (return-Indcpamon0-simgate-GBLG-state state-right-NEU)
                                (return-Indcpamon0-simgate-GBLG-state-length state-right-NEU)))
    )

  (let

; state of the key packages
(
(   top-key-package-left-neu  (project-State_Indcpamod0_keys_top    (composition-pkgstate-Indcpamod0-keys_top     state-left-neu)))
(   top-key-package-right-neu (project-State_Indcpamon0_indcpamon0  (composition-pkgstate-Indcpamon0-indcpamon0   state-right-neu)))
(bottom-key-package-left-neu  (project-State_Indcpamod0_keys_bottom (composition-pkgstate-Indcpamod0-keys_bottom  state-left-neu)))
(bottom-key-package-right-neu (project-State_Indcpamon0_indcpamon0  (composition-pkgstate-Indcpamon0-indcpamon0   state-right-neu)))
)


;;; top key packages have equal state
(= top-key-package-left-neu top-key-package-right-neu)


)))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;    State lemmas Indcpamod0
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;    State lemmas Indcpamon0
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Same Output 
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun same-output-ENC          (
        (state-left (Array Int CompositionState-Indcpamod0))
        (state-right (Array Int CompositionState-Indcpamon0))
        (state-length-left-old Int)
        (state-length-right-old Int)
        (state-left-NEU Return_Indcpamod0_gate_GBLG)
        (state-right-NEU Return_Indcpamon0_simgate_GBLG)
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool
(=
(return-Indcpamod0-gate-GBLG-value return-left-gate-GBLG)
(return-Indcpamon0-simgate-GBLG-value return-right-simgate-GBLG)
)
)

(define-fun same-output-SETBIT          (
        (state-left (Array Int CompositionState-Indcpamod0))
        (state-right (Array Int CompositionState-Indcpamon0))
        (state-length-left-old Int)
        (state-length-right-old Int)
        (state-left-NEU Return_Indcpamod0_keys_top_SETBIT)
        (state-right-NEU Return_Indcpamon0_indcpamon0_SETBIT)
        (h Int)
        (zz Bool))
        Bool
(=
(return-Indcpamod0-keys_top-SETBIT-value return-left-keys_top-SETBIT)
(return-Indcpamon0-indcpamon0-SETBIT-value return-right-keys_top-SETBIT)
)
)

(define-fun same-output-GETAOUT          (
        (state-left (Array Int CompositionState-Indcpamod0))
        (state-right (Array Int CompositionState-Indcpamon0))
        (state-length-left-old Int)
        (state-length-right-old Int)
        (state-left-NEU Return_Indcpamod0_keys_top_GETAOUT)
        (state-right-NEU Return_Indcpamon0_indcpamon0_GETAOUT)
        (h Int))
        Bool
(=
(return-Indcpamod0-keys_top-GETAOUT-value return-left-keys_top-GETAOUT)
(return-Indcpamon0-indcpamon0-GETAOUT-value return-right-keys_top-GETAOUT)
)
)
