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

