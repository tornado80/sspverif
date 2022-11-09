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


(define-fun lemma2-left-keys ((state-left-alt CompositionState-Left)(state-left-neu CompositionState-Left)) Bool

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
(ctr-r-left-new   (composition-rand-Left-3  state-left-neu))
;(ctr-r-right-new  (composition-rand-Right-1 state-right-new))
(ctr-rr-left-new  (composition-rand-Left-4  state-left-neu))
;(ctr-rr-right-new (composition-rand-Right-2 state-right-new))
)

(let

; table of the bottom key package
(
(table-top-left-alt (state-keys-T top-key-package-left-alt))
(table-top-left-neu (state-keys-T top-key-package-left-neu))
(table-bottom-left-alt (state-keys-T bottom-key-package-left-alt))
(table-bottom-left-neu (state-keys-T bottom-key-package-left-neu))
              ;assignment of the sampled values for the lower Key package
              (r-left   (__sample-rand-Left-Bits_n 3 ctr-r-left))
 ;             (r-right  (__sample-rand-Right-Bits_n 1 ctr-r-right))
              (rr-left  (__sample-rand-Left-Bits_n 4 ctr-rr-left))
 ;             (rr-right (__sample-rand-Right-Bits_n 2 ctr-rr-left))

              ;assignment of the sampled values for the lower Key package as a table
              (Z-left
                 (store 
                       (store Z-left true  (mk-some  r-left))
                       false (mk-some rr-left))
              )
;              (Z-right
;                 (store 
;                       (store Z-right true  (mk-some  r-right))
;                       false (mk-some rr-right))

)

;;; bottom key packages equal except for position j
;;; and where there is j, there is the same or Z
(forall ((hh Int))
(ite
(not
(and (= j hh) (= (select table-bottom-left-alt hh) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))))
;(= (select table-bottom-right-new hh) (mk-some Z-right)) ;this is the hard part in the proof
(= (select table-bottom-left-alt hh) (select table-bottom-left-neu hh))
true
)))))



(define-fun lemma2-right-keys ((state-right-alt CompositionState-Right)(state-right-neu CompositionState-Right)) Bool

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
(table-top-right-alt    (state-keys-T top-key-package-right-alt))
(table-top-right-neu    (state-keys-T top-key-package-right-neu))
(table-bottom-right-alt (state-keys-T bottom-key-package-right-alt))
(table-bottom-right-neu (state-keys-T bottom-key-package-right-neu))
)

;;; bottom key packages equal except for position j
;;; and where there is j, there is the same or Z
(forall ((hh Int))
(ite
(not
(and (= j hh) (= (select table-bottom-right-alt hh) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))))
;(= (select table-bottom-right-new hh) (mk-some Z-right)) ;this is the hard part in the proof
(= (select table-bottom-right-alt hh) (select table-bottom-right-neu hh))
true
)))))

(define-fun lemma2-keys ((state-left-neu CompositionState-Left)(state-right-neu CompositionState-Right)) Bool

(let

; state of the key packages
(
(top-key-package-left-neu  (project-State_Left_keys_top  (composition-pkgstate-Left-keys_top state-left-neu)))
(top-key-package-right-neu (project-State_Right_keys_top (composition-pkgstate-Right-keys_top state-right-neu)))
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
(ite
(not
;(and 
(= j hh)) ;(= (select table-bottom-right-alt hh) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))))
;(= (select table-bottom-right-new hh) (mk-some Z-right)) ;this is the hard part in the proof
(= (select table-bottom-left-neu hh) (select table-bottom-right-neu hh))
true
)))))


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

