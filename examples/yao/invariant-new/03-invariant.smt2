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

