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


; layer handle:
(declare-const handle Int)

; possible input for SETBIT
(declare-const bit Bool)

; possible input for GBLG     oracle GBLG(h: Integer, l: Integer, r: Integer, op: fn Bool,Bool -> Bool, j: Integer) -> Table(Bits(p),Bool) {
(declare-const l Int)
(declare-const r Int)
(declare-const op (Array (Tuple2 Bool Bool) (Maybe Bool)))
(declare-const j Int)

; possible state arrays
(declare-const array-state-left-old (Array Int CompositionState-Left))
(declare-const length-state-left-old Int)
(declare-const array-state-right-old (Array Int CompositionState-Right))
(declare-const length-state-right-old Int)
(declare-const array-state-left-new (Array Int CompositionState-Left))
(declare-const length-state-left-new Int)
(declare-const array-state-right-new (Array Int CompositionState-Right))
(declare-const length-state-right-new Int)

; possible state
(declare-const state-left-old CompositionState-Left)
(declare-const state-right-old CompositionState-Right)
(declare-const state-right-after-EVAL CompositionState-Right)
(declare-const state-left-new CompositionState-Left)
(declare-const state-right-new CompositionState-Right)

; return value for GBLG call
(declare-const return-left  Return_Left_gate_GBLG)
(declare-const return-right Return_Right_simgate_GBLG)
(declare-const is-abort-left Bool)
(declare-const is-abort-right Bool)
(declare-const y-left  (Maybe (Array Bits_p (Maybe Bool))))
(declare-const y-right (Maybe (Array Bits_p (Maybe Bool))))


; sampled value Z and associated values
(declare-const Z  (Array Bool (Maybe Bits_n)))
;(declare-const ctr-r-left Int)
;(declare-const ctr-r-right Int)
;(declare-const ctr-rr-left Int)
;(declare-const ctr-rr-right Int)
;(declare-const ctr-r-left-new Int)
;(declare-const ctr-r-right-new Int)
;(declare-const ctr-rr-left-new Int)
;(declare-const ctr-rr-right-new Int)
;(declare-const r-left Bits_n)
;(declare-const r-right Bits_n)
;(declare-const rr-left Bits_n)
;(declare-const rr-right Bits_n)

(push 1)
(assert true)
(check-sat) ;2
(pop 1)


(assert
(and

              ;assignment of return (value,state)
              (= return-left      (oracle-Left-gate-GBLG array-state-left-old length-state-left-old handle l r op j))
              (= return-right     (oracle-Right-simgate-GBLG array-state-right-old length-state-right-old handle l r op j))

              ;assignment of return values
              (= y-left       (return-Left-gate-GBLG-value return-left))
              (= y-right      (return-Right-simgate-GBLG-value return-right))

              ;assignment of abort values
              (= is-abort-left    (return-Left-gate-GBLG-is-abort return-left))
              (= is-abort-right   (return-Right-simgate-GBLG-is-abort return-right))

              ;assignment of return state
              (= array-state-left-new   (return-Left-gate-GBLG-state return-left))
              (= array-state-right-new  (return-Right-simgate-GBLG-state return-right))

              ;assignment of return length
              (= length-state-left-new   (return-Left-gate-GBLG-state-length return-left))
              (= length-state-right-new  (return-Right-simgate-GBLG-state-length return-right))

              ;assignment of return state
              (= state-left-new   (select array-state-left-new length-state-left-new))
              (= state-right-new  (select array-state-right-new length-state-right-new))

              ;initial state list contains only one state
              (= length-state-left-old 1)
              (= length-state-right-old 1)

              ;assignment of old state
              (= state-left-old   (select array-state-left-old length-state-left-old))
              (= state-right-old  (select array-state-right-old length-state-right-old))

)
)

;(push 1)
;(assert true)
;(check-sat) ;3
;(pop 1)


; special-purpose glue for this particular project
(assert
(and
              ;op should be total
(not (= (select op (mk-tuple2 true  true ))(as mk-none (Maybe Bool))))
(not (= (select op (mk-tuple2 true  false))(as mk-none (Maybe Bool))))
(not (= (select op (mk-tuple2 false true ))(as mk-none (Maybe Bool))))
(not (= (select op (mk-tuple2 false false))(as mk-none (Maybe Bool))))
))

;(push 1)
;(assert true)
;(check-sat) ;4
;(pop 1)

(assert
;;;;;;Pre-condition (randomness mapping):
;equality of values of the sample functions for the lower Key package
(forall ((ctr Int))
(and
              (= (__sample-rand-Left-Bits_n 5 ctr)      ;used to be 3 --> 5
                 (__sample-rand-Right-Bits_n 7 ctr))    ;used to be 1 --> 7
              (= (__sample-rand-Left-Bits_n 6 ctr)      ;used to be 4 --> 6
                 (__sample-rand-Right-Bits_n 8 ctr))))) ;used to be 2 --> 8

;used to be 3 --> 5
;used to be 1 --> 7
;used to be 4 --> 6
;used to be 2 --> 8

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
);(push 1)
;(assert true)
;(check-sat) ;5
;(pop 1)


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
;(push 1)
;(assert true)
;(check-sat) ;6
;(pop 1)


(define-fun invariant-keys ((state-left CompositionState-Left)(state-right CompositionState-Right)) Bool


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



(define-fun invariant-ctr ((state-left CompositionState-Left)(state-right CompositionState-Right)) Bool

(let

; counter values
(
;key sampling
              (ctr-r-left   (composition-rand-Left-5   state-left ))
              (ctr-rr-left  (composition-rand-Left-6   state-left ))
              (ctr-r-right  (composition-rand-Right-7  state-right))
              (ctr-rr-right (composition-rand-Right-8  state-right))

              (ctr-rin-oo-right  (composition-rand-Right-9  state-right))
              (ctr-rout-oo-right (composition-rand-Right-10 state-right))
;assignment of the ctr of the sample instructions for the 8 encryptions on the left
              (ctr-rin-left  (composition-rand-Left-9  state-left))
              (ctr-rout-left (composition-rand-Left-11 state-left))
)


;compatibility of the counter values
(= ctr-rin-left (* 4 ctr-rin-oo-right))
(= ctr-rout-left (* 4 ctr-rout-oo-right))
(= ctr-r-left ctr-r-right)
(= ctr-rr-left ctr-rr-right)

)
)

;used to be 3 --> 5 left
;used to be 1 --> 7 right
;used to be 4 --> 6 left
;used to be 2 --> 8 right

(define-fun lemma1-left-keys ((state-left-alt CompositionState-Left)(state-left-neu CompositionState-Left)) Bool

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

)))

(define-fun lemma1-right-keys ((state-right-alt CompositionState-Right)(state-right-neu CompositionState-Right)) Bool

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

)))

(define-fun lemma1-keys
           ((state-left-neu CompositionState-Left)(state-right-neu CompositionState-Right)) Bool

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


)))


(define-fun lemma2-left-keys-a ((state-left-alt CompositionState-Left)(state-left-neu CompositionState-Left)) Bool

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

;used to be 3 --> 5
;used to be 1 --> 7
;used to be 4 --> 6
;used to be 2 --> 8


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
))))))

(define-fun lemma2-left-keys-b ((state-left-alt CompositionState-Left)(state-left-neu CompositionState-Left)) Bool

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

;used to be 3 --> 5
;used to be 1 --> 7
;used to be 4 --> 6
;used to be 2 --> 8


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

;used to be 3 --> 5
;used to be 1 --> 7
;used to be 4 --> 6
;used to be 2 --> 8


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
))))))

(define-fun lemma2-right-keys-a ((state-right-alt CompositionState-Right)(state-right-neu CompositionState-Right)) Bool

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

;used to be 3 --> 5 left
;used to be 1 --> 7 right
;used to be 4 --> 6 left
;used to be 2 --> 8 right


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

;used to be 3 --> 5 left
;used to be 1 --> 7 right
;used to be 4 --> 6 left
;used to be 2 --> 8 right


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
))))))


(define-fun lemma2-right-keys-b ((state-right-alt CompositionState-Right)(state-right-neu CompositionState-Right)) Bool

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

;used to be 3 --> 5 left
;used to be 1 --> 7 right
;used to be 4 --> 6 left
;used to be 2 --> 8 right


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
))))))

(define-fun lemma2-sample ((state-left-alt CompositionState-Left)(state-right-alt CompositionState-Right)) Bool
(let
(
              ;assignment of the ctr of the sample instructions for the lower Key package
              (ctr-r-left   (composition-rand-Left-5  state-left-alt))
              (ctr-rr-left  (composition-rand-Left-6  state-left-alt))
              (ctr-r-right  (composition-rand-Right-7 state-right-alt))
              (ctr-rr-right (composition-rand-Right-8 state-right-alt))
)

;used to be 3 --> 5 left
;used to be 1 --> 7 right
;used to be 4 --> 6 left
;used to be 2 --> 8 right


(let
(
              ;assignment of the sampled values for the lower Key package
              (r-left   (mk-some (__sample-rand-Left-Bits_n 5 ctr-r-left)))
              (rr-left  (mk-some (__sample-rand-Left-Bits_n 6 ctr-rr-left)))
              (r-right  (mk-some (__sample-rand-Right-Bits_n 7 ctr-r-right)))
              (rr-right (mk-some (__sample-rand-Right-Bits_n 8 ctr-rr-right)))
)

(= r-left   rr-left)
(= r-right  rr-right)
)))


(define-fun lemma2-keys ((state-left-neu CompositionState-Left)(state-right-neu CompositionState-Right)) Bool

(let

; state of the key packages
(
(top-key-package-left-neu     (project-State_Left_keys_top  (composition-pkgstate-Left-keys_top state-left-neu)))
(top-key-package-right-neu    (project-State_Right_keys_top (composition-pkgstate-Right-keys_top state-right-neu)))
(bottom-key-package-left-neu  (project-State_Left_keys_bottom  (composition-pkgstate-Left-keys_bottom state-left-neu)))
(bottom-key-package-right-neu (project-State_Right_keys_bottom (composition-pkgstate-Right-keys_bottom state-right-neu)))
)

(let

; table of the bottom key package
(
(table-top-left-neu     (state-keys-T top-key-package-left-neu))
(table-top-right-neu    (state-keys-T top-key-package-right-neu))
(table-bottom-left-neu  (state-keys-T bottom-key-package-left-neu))
(table-bottom-right-neu (state-keys-T bottom-key-package-right-neu))
)

;;; bottom key packages equal except for position j
;;; and where there is j, there is the same or Z
(forall ((hh Int))
(= (select table-bottom-left-neu hh) (select table-bottom-right-neu hh))
))))


;(define-fun lemma3-left-keys ((state-left-alt CompositionState-Left)(state-left-neu CompositionState-Left)) Bool
;
;(let
;
;; state of the key packages
;(
;(top-key-package-left-alt (project-State_Left_keys_top (composition-pkgstate-Left-keys_top state-left-alt)))
;(top-key-package-left-neu (project-State_Left_keys_top (composition-pkgstate-Left-keys_top state-left-neu)))
;(bottom-key-package-left-alt (project-State_Left_keys_bottom (composition-pkgstate-Left-keys_bottom state-left-alt)))
;(bottom-key-package-left-neu (project-State_Left_keys_bottom (composition-pkgstate-Left-keys_bottom state-left-neu)))
;
;)
;
;(select Z-left true              (= r-left   (__sample-rand-Left-Bits_n 3 ctr-r-left))
;;              (= r-right  (__sample-rand-Right-Bits_n 1 ctr-r-right))
;              (= rr-left  (__sample-rand-Left-Bits_n 4 ctr-rr-left))
;;              (= rr-right (__sample-rand-Right-Bits_n 2 ctr-rr-left))
;
;              ;assignment of the sampled values for the lower Key package as a table
;              (= (mk-some  r-left)  (select Z-left   true))
;              (= (mk-some rr-left)  (select Z-left  false))
;
;(let
;
;; table of the bottom key package
;(
;(table-top-left-alt (state-keys-T bottom-key-package-left-alt))
;(table-top-left-neu (state-keys-T bottom-key-package-left-neu))
;(table-bottom-left-alt (state-keys-T bottom-key-package-left-alt))
;(table-bottom-left-neu (state-keys-T bottom-key-package-left-neu))
;)
;
;;;; bottom key packages equal except for position j
;;;; and where there is j, there is the same or Z
;(forall ((hh Int))
;(ite
;(and (= j hh) (= (select table-bottom-left-alt hh) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))))
;(= (select table-bottom-right-new hh) (mk-some Z-left)) ;this is the hard part in the proof
;true
;))))



(push 1)

(assert (and (invariant-keys state-left-old state-right-old)
             (invariant-ctr state-left-old state-right-old)
             (not is-abort-right)
             (not is-abort-left)
             (not (invariant-ctr state-left-new state-right-new))))
(check-sat) ;3
;(get-model)
(pop 1)

(push 1)

(assert (and (invariant-keys state-left-old state-right-old)
             (invariant-ctr state-left-old state-right-old)
             (invariant-ctr state-left-new state-right-new)
             (not is-abort-right)
             (not is-abort-left)
             (not (lemma2-sample state-left-old state-right-old))))
(check-sat) ;3
;(get-model)
(pop 1)


(push 1)
(assert (and (invariant-keys state-left-old state-right-old)
             (invariant-ctr state-left-old state-right-old)
             (invariant-ctr state-left-new state-right-new)
             (not is-abort-right)
             (not is-abort-left)
             (not (lemma1-left-keys state-left-old state-left-new))))
(check-sat) ;4
;(get-model)
(pop 1)

(push 1)

(assert (and (invariant-keys state-left-old state-right-old)
             (invariant-ctr state-left-old state-right-old)
             (invariant-ctr state-left-new state-right-new)
             (not is-abort-right)
             (not is-abort-left)
             (lemma1-left-keys state-left-old state-left-new)
             (not (lemma1-right-keys state-right-old state-right-new))))
(check-sat) ;5
;(get-model)
(pop 1)

(push 1)

(assert (and (invariant-keys state-left-old state-right-old)
             (invariant-ctr state-left-old state-right-old)
             (invariant-ctr state-left-new state-right-new)
             (not is-abort-right)
             (not is-abort-left)
             (lemma1-left-keys state-left-old state-left-new)
             (lemma1-right-keys state-right-old state-right-new)
             (not (lemma1-keys state-left-new state-right-new))))
(check-sat) ;6
;(get-model)
(pop 1)

(push 1)

(assert (and (invariant-keys          state-left-old  state-right-old)
             (invariant-ctr           state-left-old  state-right-old)
             (invariant-ctr state-left-new state-right-new)
             (not is-abort-right)
             (not is-abort-left)
             (lemma1-left-keys        state-left-old  state-left-new)
             (lemma1-right-keys       state-right-old state-right-new)
             (lemma1-keys             state-left-new  state-right-new)
             (not (lemma2-left-keys-a state-left-old  state-left-new))
             ))
(check-sat) ;7
;(get-model)
(pop 1)

(push 1)

(assert (and (invariant-keys          state-left-old state-right-old)
             (invariant-ctr           state-left-old state-right-old)
             (invariant-ctr           state-left-new state-right-new)
             (not is-abort-right)
             (not is-abort-left)
             (lemma1-left-keys        state-left-old state-left-new)
             (lemma1-right-keys       state-right-old state-right-new)
             (lemma1-keys             state-left-new  state-right-new)
             (lemma2-left-keys-a      state-left-old state-left-new)
             (not (lemma2-left-keys-b state-left-old state-left-new))
             ))
(check-sat) ;8
;(get-model)
(pop 1)

(push 1)

(assert (and (invariant-keys          state-left-old  state-right-old)
             (invariant-ctr           state-left-old  state-right-old)
             (invariant-ctr           state-left-new  state-right-new)
             (not is-abort-right)
             (not is-abort-left)
             (lemma1-left-keys        state-left-old  state-left-new)
             (lemma1-right-keys       state-right-old state-right-new)
             (lemma1-keys             state-left-new  state-right-new)
             (lemma2-left-keys-a      state-left-old  state-left-new)
             (lemma2-left-keys-b      state-left-old  state-left-new)
             (not (lemma2-right-keys-a  state-right-old state-right-new))
             ))
(check-sat) ;9
;(get-model)
(pop 1)

(push 1)

(assert (and (invariant-keys          state-left-old  state-right-old)
             (invariant-ctr           state-left-old  state-right-old)
             (invariant-ctr           state-left-new  state-right-new)
             (not is-abort-right)
             (not is-abort-left)
             (lemma1-left-keys        state-left-old  state-left-new)
             (lemma1-right-keys       state-right-old state-right-new)
             (lemma1-keys             state-left-new  state-right-new)
             (lemma2-left-keys-a      state-left-old  state-left-new)
             (lemma2-left-keys-b      state-left-old  state-left-new)
             (lemma2-right-keys-a     state-right-old state-right-new)
             (not (lemma2-right-keys-b  state-right-old state-right-new))
             ))
(check-sat) ;10
;(get-model)
(pop 1)


(push 1)

(assert (and (invariant-keys         state-left-old  state-right-old)
             (invariant-ctr          state-left-old  state-right-old)
             (invariant-ctr          state-left-new state-right-new)
             (not is-abort-right)
             (not is-abort-left)
             (lemma1-left-keys       state-left-old  state-left-new)
             (lemma1-right-keys      state-right-old state-right-new)
             (lemma1-keys            state-left-new  state-right-new)
             (lemma2-left-keys-a     state-left-old  state-left-new)
             (lemma2-left-keys-b     state-left-old  state-left-new)
             (lemma2-right-keys-a    state-right-old state-right-new)
             (lemma2-right-keys-b    state-right-old state-right-new)
             (not (lemma2-keys       state-left-new  state-right-new))))
(check-sat) ;10
;(get-model)
(pop 1)

(push 1)

(assert (and (invariant-keys         state-left-old  state-right-old)
             (invariant-ctr          state-left-old  state-right-old)
             (invariant-ctr          state-left-new state-right-new)
             (not is-abort-right)
             (not is-abort-left)
             (lemma1-left-keys       state-left-old  state-left-new)
             (lemma1-right-keys      state-right-old state-right-new)
             (lemma1-keys            state-left-new  state-right-new)
             (lemma2-left-keys-a     state-left-old  state-left-new)
             (lemma2-left-keys-b     state-left-old  state-left-new)
             (lemma2-right-keys-a    state-right-old state-right-new)
             (lemma2-right-keys-b    state-right-old state-right-new)
             (not (invariant-keys    state-left-new  state-right-new))))
(check-sat) ;11
;(get-model)
(pop 1)

(push 1)

(assert (and (invariant-keys state-left-old state-right-old)
             (invariant-ctr state-left-old state-right-old)
             (invariant-keys state-left-new state-right-new)
             (invariant-ctr state-left-new state-right-new)
             (not is-abort-right)
             (not is-abort-left)
             (= y-left y-right)
             ))
(check-sat) ;12
;(get-model)
(pop 1)
