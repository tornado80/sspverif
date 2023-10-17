;;;;;;;;;;;;;;;;;
;
; left  = mod
; right = mon
;
;;;;;;;;;;;;;;;;;

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

; r, will be written into Z at true
(declare-const randval-left-GETA-1 Bits_n)
(assert (= randval-left-GETA-1  (__sample-rand-Indcpamod0-Bits_n 1 randctr-left-1
)))

; k_, will be written into Z at z
(declare-const randval-right-GETA-1 Bits_n)
(assert (= randval-right-GETA-1 (__sample-rand-Indcpamon0-Bits_n 1 randctr-right-1
)))

; rr, will be written into Z at false
(declare-const randval-left-GETA-2 Bits_n)
(assert (= randval-left-GETA-2  (__sample-rand-Indcpamod0-Bits_n 2 randctr-left-2
)))

(declare-const randval-right-GETA-2 Bits_n)
(assert (= randval-right-GETA-2 (__sample-rand-Indcpamon0-Bits_n 2 randctr-right-2
)))

; r, will be written into Z at true
(declare-const randval-left-GETA-3 Bits_n)
(assert (= randval-left-GETA-3  (__sample-rand-Indcpamod0-Bits_n  3 randctr-left-3
)))

(declare-const randval-right-GETA-3 Bits_n)
(assert (= randval-right-GETA-3 (__sample-rand-Indcpamon0-Bits_n 3 randctr-right-3
)))

; rr, will be written into Z at false
(declare-const randval-left-GETA-4 Bits_n)
(assert (= randval-left-GETA-4  (__sample-rand-Indcpamod0-Bits_n  4 randctr-left-4
)))

; k_, will be written into Z at not z
(declare-const randval-right-GETA-4 Bits_n)
(assert (= randval-right-GETA-4 (__sample-rand-Indcpamon0-Bits_n 4 randctr-right-4
)))



(declare-const randval-left-ENCN-1 Bits_n)
(assert (= randval-left-ENCN-1  (__sample-rand-Indcpamod0-Bits_n  1 randctr-left-1
)))

(declare-const randval-right-ENCN-1 Bits_n)
(assert (= randval-right-ENCN-1 (__sample-rand-Indcpamon0-Bits_n 1 randctr-right-1
)))

(declare-const randval-left-ENCN-2 Bits_n)
(assert (= randval-left-ENCN-2  (__sample-rand-Indcpamod0-Bits_n 2 randctr-left-2
)))

(declare-const randval-right-ENCN-2 Bits_n)
(assert (= randval-right-ENCN-2 (__sample-rand-Indcpamon0-Bits_n 2 randctr-right-2
)))

(declare-const randval-left-ENCN-3 Bits_n)
(assert (= randval-left-ENCN-3  (__sample-rand-Indcpamod0-Bits_n 3 randctr-left-3
)))

(declare-const randval-right-ENCN-3 Bits_n)
(assert (= randval-right-ENCN-3 (__sample-rand-Indcpamon0-Bits_n 3 randctr-right-3
)))

(declare-const randval-left-ENCN-4 Bits_n)
(assert (= randval-left-ENCN-4  (__sample-rand-Indcpamod0-Bits_n 4 randctr-left-4
)))

(declare-const randval-right-ENCN-4 Bits_n)
(assert (= randval-right-ENCN-4 (__sample-rand-Indcpamon0-Bits_n 4 randctr-right-4
)))

(declare-const randval-left-ENCN-5 Bits_n)
(assert (= randval-left-ENCN-5  (__sample-rand-Indcpamod0-Bits_n 5 randctr-left-5
)))

(declare-const randval-right-ENCN-5 Bits_n)
(assert (= randval-right-ENCN-5 (__sample-rand-Indcpamon0-Bits_n 5 randctr-right-5
)))

(declare-const randval-left-ENCN-6 Bits_n)
(assert (= randval-left-ENCN-6  (__sample-rand-Indcpamod0-Bits_n 6 randctr-left-6
)))

(declare-const randval-right-ENCN-6 Bits_n)
(assert (= randval-right-ENCN-6 (__sample-rand-Indcpamon0-Bits_n 6 randctr-right-6
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

; mon = right
; red samples with index 4 k_ ~ z
; SMP verwendet counter 1 to sample k_ ~ not z
;
; mod = left
; top key package samples r with index 1 for true
;                        rr with index 2 for false


(and
(=>
; if z = true
(=
; z
(state-Indcpamon0-red-z
(composition-pkgstate-Indcpamon0-red 
(select state-right state-length-right-old)))
(mk-some true))
(and
(=  randval-left-GETA-1 ; r at true
   randval-right-GETA-4 ; k_ at z=true
)
(=  randval-left-GETA-2 ; rr at false
   randval-right-GETA-1 ; k_ at not z = false
)
)
)
(=>
; if z = false
(=
; z
(state-Indcpamon0-red-z
(composition-pkgstate-Indcpamon0-red 
(select state-right state-length-right-old))) 
(mk-some false))
(and
(=  randval-left-GETA-1 ; r at true
   randval-right-GETA-1 ; k_ at not z
)
(=  randval-left-GETA-2 ; rr at false
   randval-right-GETA-4 ; k_ at z
)
)
)
)
)

(define-fun randomness-mapping-GETKEYSIN () Bool
true
)

(define-fun randomness-mapping-ENCN () Bool
(= randval-left-ENCN-5 randval-right-ENCN-2)
)

(define-fun randomness-mapping-ENCM () Bool
(= randval-left-ENCN-6 randval-right-ENCN-3)
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
      (state-keys-T    (Maybe (Array Bool (Maybe Bits_n))))
      (state-keys-z    (Maybe Bool))
      (state-keys-flag (Maybe Bool)))))

(define-fun project-State_Indcpamod0_keys_top ((in State_Indcpamod0_keys_top)) State_keys
  (mk-state-keys (state-Indcpamod0-keys_top-T    in)
                 (state-Indcpamod0-keys_top-z    in)
                 (state-Indcpamod0-keys_top-flag in)))



(define-fun project-keys-State_Indcpamon0_indcpamon0 ((in CompositionState-Indcpamon0)) State_keys
(let ((red-state (composition-pkgstate-Indcpamon0-red        in))
      (ind-state (composition-pkgstate-Indcpamon0-indcpamon0 in))
     )
(let ((ka    (state-Indcpamon0-red-k        red-state))
      (kina  (state-Indcpamon0-indcpamon0-k ind-state))
      (z     (state-Indcpamon0-red-z        red-state))
      (flag  (state-Indcpamon0-red-flag     red-state)))
(let ((Z (ite (or (not (= ka   (as mk-none (Maybe Bits_n))))
                  (not (= kina (as mk-none (Maybe Bits_n))))
              )
              (mk-some (store (store
                 ;initialize empty table 
                 ((as const (Array Bool (Maybe Bits_n))) (as mk-none (Maybe Bits_n))) 
                      (maybe-get z)  ka) 
                 (not (maybe-get z)) kina))
                 (as mk-none (Maybe (Array Bool (Maybe Bits_n))))
)))
     (mk-state-keys Z z flag)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;   Well-definedness of tables
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;If T h != none => T h b != none (for both b=0 and b=1)

(define-fun well-defined ((T (Maybe (Array Bool (Maybe Bits_n))))) Bool
    (or
      (= T (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
      (forall ((b Bool))
        (not
          (= (select (maybe-get T) b) (as mk-none (Maybe Bits_n))
    )
))))

; captures the possible states which a Key package can be in when
; the "top" queries are GETKEYS queries 
;
(define-fun well-defined-Key-bool ((key-state State_keys)) Bool
(let ((T    (state-keys-T    key-state))
      (flag (state-keys-flag key-state))
      (z    (state-keys-z    key-state)))

(and

; T = none or for b=0,1: T b != none
(well-defined T)

;flag is either none or true
(or
    (= flag (as mk-none (Maybe Bool)))
    (= flag (   mk-some        true)))

;flag = true <=> T != none
(=
     (= flag (mk-some true))
(not (= T (as mk-none (Maybe (Array Bool (Maybe Bits_n))))))
)

;flag = true => z != none
(=>
     (= flag (mk-some true))
(not (= z (as mk-none (Maybe Bool)))))
)

))

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

(and
(or
  (= flag (as mk-none (Maybe Bool)))
  (= flag (   mk-some        true )))

 ;flag has been set  => bit has been set
(=> (=  (mk-some true ) flag)  
                    (or (=  (mk-some true ) z)
                        (=  (mk-some false) z)
                    ))
; key has been set => flag has been set
(=> (not            (= T (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
                    )
                    (= flag (mk-some true)))
))))

(define-fun well-defined-Key-debug ((key-state State_keys)) Bool
(let ((T    (state-keys-T    key-state))
      (flag (state-keys-flag key-state))
      (z    (state-keys-z    key-state)))

(and true

;T != none or for b=0,1 T b != none
(well-defined T)
(not (= T (as mk-none (Maybe (Array Bool (Maybe Bits_n))))))
(not (= z (as mk-none (Maybe Bool))))
(= flag (mk-some true))

)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Invariant
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun invariant-ENCN          (
        (state-left  (Array Int CompositionState-Indcpamod0 ))
        (state-right (Array Int CompositionState-Indcpamon0))
        (state-length-left  Int) ;old index
        (state-length-right Int) ;old index
        (state-left-new  Return_Indcpamod0_enc_ENCN)
        (state-right-new Return_Indcpamon0_red_ENCN)
        (d Bool)
        (nzero Bits_n)
        (none  Bits_n))
    Bool
   (let

; state of the key packages
(
(top-key-package-left  (project-State_Indcpamod0_keys_top      (composition-pkgstate-Indcpamod0-keys_top     (select state-left  state-length-left))))
(top-key-package-right (project-keys-State_Indcpamon0_indcpamon0   (select state-right state-length-right)))  ;(composition-pkgstate-Indcpamon0-indcpamon0    (select state-right state-length-right))))
)

(and
;top key package states are equal
(= top-key-package-left top-key-package-right)


;top key package state is "good"
(well-defined-Key-debug top-key-package-left )
(well-defined-Key-debug top-key-package-right)

;the functions left and right are the same
(forall ((k Bits_n)(x Bits_n)(r Bits_n))
(= (__func-Indcpamon0-encn k x r) (__func-Indcpamod0-encn  k x r))
)
)))

(define-fun invariant-ENCN-post          (
        (state-left  (Array Int CompositionState-Indcpamod0 ))
        (state-right (Array Int CompositionState-Indcpamon0))
        (state-length-left  Int) ;old index
        (state-length-right Int) ;old index
        (state-left-new  Return_Indcpamod0_enc_ENCN)
        (state-right-new Return_Indcpamon0_red_ENCN)
        (d Bool)
        (nzero Bits_n)
        (none  Bits_n))
    Bool
(let (
      (state-left-nov  (select  (return-Indcpamod0-enc-ENCN-state        state-left-new)
                                (return-Indcpamod0-enc-ENCN-state-length state-left-new)
                                ))
      (state-right-nov (select  (return-Indcpamon0-red-ENCN-state        state-right-new)
                                (return-Indcpamon0-red-ENCN-state-length state-right-new)
                                ))
     )

    (let

; state of the key packages
(
(top-key-package-left  (project-State_Indcpamod0_keys_top      (composition-pkgstate-Indcpamod0-keys_top     state-left-nov  )))
(top-key-package-right (project-keys-State_Indcpamon0_indcpamon0  state-right-nov )))   ; (composition-pkgstate-Indcpamon0-indcpamon0    state-right-nov )))

(and
;top key package states are equal
(= top-key-package-left top-key-package-right)


;top key package state is "good"
(  well-defined-Key-active top-key-package-left )
(  well-defined-Key-active top-key-package-right)
))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Invariant stuff
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define-fun invariant-SETBIT      (
        (state-left  (Array Int CompositionState-Indcpamod0 ))
        (state-right (Array Int CompositionState-Indcpamon0))
        (state-length-left  Int) ;old index
        (state-length-right Int) ;old index
        (state-left-new  Return_Indcpamod0_keys_top_SETBIT)
        (state-right-new Return_Indcpamon0_red_SETBIT)
        (zz Bool))
    Bool
    (let

; state of the key packages
(
(top-key-package-left  (project-State_Indcpamod0_keys_top      (composition-pkgstate-Indcpamod0-keys_top     (select state-left  state-length-left))))
(top-key-package-right (project-keys-State_Indcpamon0_indcpamon0   (select state-right state-length-right)))  ;(composition-pkgstate-Indcpamon0-indcpamon0    (select state-right state-length-right))))
)

(and
;top key package states are equal
(= top-key-package-left top-key-package-right)


;top key package state is "good"
(well-defined-Key-active top-key-package-left )
(well-defined-Key-active top-key-package-right)

)))


(define-fun invariant-SETBIT-post          (
        (state-left  (Array Int CompositionState-Indcpamod0 ))
        (state-right (Array Int CompositionState-Indcpamon0))
        (state-length-left  Int) ;old index
        (state-length-right Int) ;old index
        (state-left-new  Return_Indcpamod0_keys_top_SETBIT)
        (state-right-new Return_Indcpamon0_red_SETBIT)
        (zz Bool))
    Bool
(let (
      (state-left-nov  (select  (return-Indcpamod0-keys_top-SETBIT-state        state-left-new)
                                (return-Indcpamod0-keys_top-SETBIT-state-length state-left-new)
                                ))
      (state-right-nov (select  (return-Indcpamon0-red-SETBIT-state        state-right-new)
                                (return-Indcpamon0-red-SETBIT-state-length state-right-new)
                                ))
     )

    (let

; state of the key packages
(
(top-key-package-left  (project-State_Indcpamod0_keys_top      (composition-pkgstate-Indcpamod0-keys_top     state-left-nov  )))
(top-key-package-right (project-keys-State_Indcpamon0_indcpamon0  state-right-nov ))   ; (composition-pkgstate-Indcpamon0-indcpamon0    state-right-nov )))
)

(and
;top key package states are equal
(= top-key-package-left top-key-package-right)


;top key package state is "good"
(well-defined-Key-active top-key-package-left )
(well-defined-Key-active top-key-package-right)

))))


(define-fun invariant-GETAOUT      (
        (state-left  (Array Int CompositionState-Indcpamod0 ))
        (state-right (Array Int CompositionState-Indcpamon0))
        (state-length-left  Int) ;old index
        (state-length-right Int) ;old index
        (state-left-new  Return_Indcpamod0_keys_top_GETAOUT)
        (state-right-new Return_Indcpamon0_red_GETAOUT)
        )
    Bool
    (let

; state of the key packages
(
(top-key-package-left  (project-State_Indcpamod0_keys_top      (composition-pkgstate-Indcpamod0-keys_top      (select state-left  state-length-left))))
(top-key-package-right (project-keys-State_Indcpamon0_indcpamon0  (select state-right state-length-right))) ;  (composition-pkgstate-Indcpamon0-indcpamon0    (select state-right state-length-right))))
)

(and
;top key package states are equal
(= top-key-package-left top-key-package-right)


;top key package state is "good"
(well-defined-Key-active top-key-package-left )
(well-defined-Key-active top-key-package-right)

)))


(define-fun invariant-GETAOUT-post          (
        (state-left  (Array Int CompositionState-Indcpamod0 ))
        (state-right (Array Int CompositionState-Indcpamon0))
        (state-length-left  Int) ;old index
        (state-length-right Int) ;old index
        (state-left-new  Return_Indcpamod0_keys_top_GETAOUT)
        (state-right-new Return_Indcpamon0_red_GETAOUT)
        )
    Bool
(let (
      (state-left-nov  (select  (return-Indcpamod0-keys_top-GETAOUT-state        state-left-new)
                                (return-Indcpamod0-keys_top-GETAOUT-state-length state-left-new)
                                ))
      (state-right-nov (select  (return-Indcpamon0-red-GETAOUT-state        state-right-new)
                                (return-Indcpamon0-red-GETAOUT-state-length state-right-new)
                                ))
     )

    (let

; state of the key packages
(
(top-key-package-left  (project-State_Indcpamod0_keys_top      (composition-pkgstate-Indcpamod0-keys_top     state-left-nov  )))
(top-key-package-right (project-keys-State_Indcpamon0_indcpamon0  state-right-nov));   (composition-pkgstate-Indcpamon0-indcpamon0    state-right-nov )))
)

(and
;top key package states are equal
(= top-key-package-left top-key-package-right)

;top key package state is "good"
(  well-defined-Key-active top-key-package-left )
(  well-defined-Key-active top-key-package-right)

))))

(define-fun invariant-GETAOUT-post-left          (
        (state-left  (Array Int CompositionState-Indcpamod0 ))
        (state-right (Array Int CompositionState-Indcpamon0))
        (state-length-left  Int) ;old index
        (state-length-right Int) ;old index
        (state-left-new  Return_Indcpamod0_keys_top_GETAOUT)
        (state-right-new Return_Indcpamon0_red_GETAOUT)
        )
    Bool
(let (
      (state-left-nov  (select  (return-Indcpamod0-keys_top-GETAOUT-state        state-left-new)
                                (return-Indcpamod0-keys_top-GETAOUT-state-length state-left-new)
                                ))
      (state-right-nov (select  (return-Indcpamon0-red-GETAOUT-state        state-right-new)
                                (return-Indcpamon0-red-GETAOUT-state-length state-right-new)
                                ))
     )

    (let

; state of the key packages
(
(top-key-package-left  (project-State_Indcpamod0_keys_top      (composition-pkgstate-Indcpamod0-keys_top     state-left-nov  )))
(top-key-package-right (project-keys-State_Indcpamon0_indcpamon0  state-right-nov));   (composition-pkgstate-Indcpamon0-indcpamon0    state-right-nov )))
)

(and
;top key package states are equal
;(= top-key-package-left top-key-package-right)

;top key package state is "good"
(well-defined-Key-active top-key-package-left )
;(well-defined-Key-active top-key-package-right)

))))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;    aborts equal
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun aborts-equal-ENCN          (
        (state-left  (Array Int CompositionState-Indcpamod0))
        (state-right (Array Int CompositionState-Indcpamon0))
        (state-length-left  Int) ; old index = 1
        (state-length-right Int) ; old index = 1
        (state-left-NEU Return_Indcpamod0_enc_ENCN)      ; also contains new index    
        (state-right-NEU Return_Indcpamon0_red_ENCN) ; also contains new index
        (d Bool)
        (nzero Bits_n)
        (none  Bits_n))
        Bool


(= (return-Indcpamod0-enc-ENCN-is-abort     state-left-NEU)
   (return-Indcpamon0-red-ENCN-is-abort     state-right-NEU))
)



(define-fun aborts-equal-SETBIT          (
        (state-left  (Array Int CompositionState-Indcpamod0))
        (state-right (Array Int CompositionState-Indcpamon0))
        (state-length-left  Int) ; old index = 1
        (state-length-right Int) ; old index = 1
        (state-left-NEU Return_Indcpamod0_keys_top_SETBIT)      ; also contains new index    
        (state-right-NEU Return_Indcpamon0_red_SETBIT) ; also contains new index
        (zz Bool))
        Bool


(= (return-Indcpamod0-keys_top-SETBIT-is-abort     state-left-NEU)
   (return-Indcpamon0-red-SETBIT-is-abort state-right-NEU))
)

(define-fun aborts-equal-GETAOUT          (
        (state-left  (Array Int CompositionState-Indcpamod0))
        (state-right (Array Int CompositionState-Indcpamon0))
        (state-length-left  Int) ; old index = 1
        (state-length-right Int) ; old index = 1
        (state-left-NEU Return_Indcpamod0_keys_top_GETAOUT)      ; also contains new index    
        (state-right-NEU Return_Indcpamon0_red_GETAOUT)          ; also contains new index
        )
        Bool


(= (return-Indcpamod0-keys_top-GETAOUT-is-abort  state-left-NEU)
   (return-Indcpamon0-red-GETAOUT-is-abort state-right-NEU))
)




; no-abort

(define-fun no-abort-ENCN          (
        (state-left  (Array Int CompositionState-Indcpamod0))
        (state-right (Array Int CompositionState-Indcpamon0))
        (state-length-left  Int) ; old index = 1
        (state-length-right Int) ; old index = 1
        (state-left-NEU  Return_Indcpamod0_enc_ENCN)  ; also contains new index    
        (state-right-NEU Return_Indcpamon0_red_ENCN) ; also contains new index
        (d Bool)
        (nzero Bits_n)
        (none  Bits_n))
        Bool

(and
(= (return-Indcpamod0-enc-ENCN-is-abort     state-left-NEU)
   false)
(= (return-Indcpamon0-red-ENCN-is-abort     state-right-NEU)
   false)
))

(define-fun left-abort-ENCN          (
        (state-left  (Array Int CompositionState-Indcpamod0))
        (state-right (Array Int CompositionState-Indcpamon0))
        (state-length-left  Int) ; old index = 1
        (state-length-right Int) ; old index = 1
        (state-left-NEU  Return_Indcpamod0_enc_ENCN)  ; also contains new index    
        (state-right-NEU Return_Indcpamon0_red_ENCN) ; also contains new index
        (d Bool)
        (nzero Bits_n)
        (none  Bits_n))
        Bool

(= (return-Indcpamod0-enc-ENCN-is-abort     state-left-NEU)
   true)
)

(define-fun right-abort-ENCN          (
        (state-left  (Array Int CompositionState-Indcpamod0))
        (state-right (Array Int CompositionState-Indcpamon0))
        (state-length-left  Int) ; old index = 1
        (state-length-right Int) ; old index = 1
        (state-left-NEU  Return_Indcpamod0_enc_ENCN)  ; also contains new index    
        (state-right-NEU Return_Indcpamon0_red_ENCN) ; also contains new index
        (d Bool)
        (nzero Bits_n)
        (none  Bits_n))
        Bool

(= (return-Indcpamon0-red-ENCN-is-abort     state-right-NEU)
   true)
)


(define-fun no-abort-SETBIT          (
        (state-left  (Array Int CompositionState-Indcpamod0))
        (state-right (Array Int CompositionState-Indcpamon0))
        (state-length-left  Int) ; old index = 1
        (state-length-right Int) ; old index = 1
        (state-left-NEU  Return_Indcpamod0_keys_top_SETBIT)  ; also contains new index    
        (state-right-NEU Return_Indcpamon0_red_SETBIT) ; also contains new index
        (zz Bool))
        Bool

(and
(= (return-Indcpamod0-keys_top-SETBIT-is-abort     state-left-NEU)
   false)
(= (return-Indcpamon0-red-SETBIT-is-abort     state-right-NEU)
   false)
))

(define-fun no-abort-GETAOUT          (
        (state-left  (Array Int CompositionState-Indcpamod0))
        (state-right (Array Int CompositionState-Indcpamon0))
        (state-length-left  Int) ; old index = 1
        (state-length-right Int) ; old index = 1
        (state-left-NEU  Return_Indcpamod0_keys_top_GETAOUT)  ; also contains new index    
        (state-right-NEU Return_Indcpamon0_red_GETAOUT) ; also contains new index
        )
        Bool

(and
(= (return-Indcpamod0-keys_top-GETAOUT-is-abort     state-left-NEU)
   false)
(= (return-Indcpamon0-red-GETAOUT-is-abort     state-right-NEU)
   false)
))

(define-fun left-abort-GETAOUT          (
        (state-left  (Array Int CompositionState-Indcpamod0))
        (state-right (Array Int CompositionState-Indcpamon0))
        (state-length-left  Int) ; old index = 1
        (state-length-right Int) ; old index = 1
        (state-left-NEU  Return_Indcpamod0_keys_top_GETAOUT)  ; also contains new index    
        (state-right-NEU Return_Indcpamon0_red_GETAOUT) ; also contains new index
        )
        Bool

(and
(= (return-Indcpamod0-keys_top-GETAOUT-is-abort     state-left-NEU)
   false)
))

(define-fun right-abort-GETAOUT          (
        (state-left  (Array Int CompositionState-Indcpamod0))
        (state-right (Array Int CompositionState-Indcpamon0))
        (state-length-left  Int) ; old index = 1
        (state-length-right Int) ; old index = 1
        (state-left-NEU  Return_Indcpamod0_keys_top_GETAOUT)  ; also contains new index    
        (state-right-NEU Return_Indcpamon0_red_GETAOUT) ; also contains new index
        )
        Bool
(and
(= (return-Indcpamon0-red-GETAOUT-is-abort     state-right-NEU)
   false)
))





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



(define-fun same-output-ENCN          (
        (state-left (Array Int CompositionState-Indcpamod0))
        (state-right (Array Int CompositionState-Indcpamon0))
        (state-length-left-old Int)
        (state-length-right-old Int)
        (state-left-NEU Return_Indcpamod0_enc_ENCN)
        (state-right-NEU Return_Indcpamon0_red_ENCN)
        (d Bool)
        (nzero Bits_n)
        (none  Bits_n))
        Bool
(=
(return-Indcpamod0-keys_top-SETBIT-value return-left-keys_top-SETBIT)
(return-Indcpamon0-red-SETBIT-value return-right-red-SETBIT)
)
)


(define-fun same-output-SETBIT          (
        (state-left (Array Int CompositionState-Indcpamod0))
        (state-right (Array Int CompositionState-Indcpamon0))
        (state-length-left-old Int)
        (state-length-right-old Int)
        (state-left-NEU Return_Indcpamod0_keys_top_SETBIT)
        (state-right-NEU Return_Indcpamon0_red_SETBIT)
        (zz Bool))
        Bool
(=
(return-Indcpamod0-keys_top-SETBIT-value return-left-keys_top-SETBIT)
(return-Indcpamon0-red-SETBIT-value return-right-red-SETBIT)
)
)

(define-fun same-output-GETAOUT          (
        (state-left (Array Int CompositionState-Indcpamod0))
        (state-right (Array Int CompositionState-Indcpamon0))
        (state-length-left-old Int)
        (state-length-right-old Int)
        (state-left-NEU Return_Indcpamod0_keys_top_GETAOUT)
        (state-right-NEU Return_Indcpamon0_red_GETAOUT)
        )
        Bool
(=
(return-Indcpamod0-keys_top-GETAOUT-value return-left-keys_top-GETAOUT)
(return-Indcpamon0-red-GETAOUT-value return-right-red-GETAOUT)
)
)
