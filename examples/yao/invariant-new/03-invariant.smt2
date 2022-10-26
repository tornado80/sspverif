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
;(= top-key-package-left top-key-package-left)

;for bottom key package, tables are equal
;(= table-bottom-left table-bottom-right)

;top key packages behave like a key packages
(well-defined-Key-active top-key-package-left)
(well-defined-Key-active top-key-package-right)

;bottom key packages behave like a key packages
(well-defined-Key-bool bottom-key-package-left)
(well-defined-Key-active bottom-key-package-right)

))))


;(define-fun invariant-ctr ((state-left Type)(state-right Type)) Bool
;
;TODO
;compatibility of the counter values
;(= ctr-rin-left (* 4 ctr-rin-oo-right))
;(= ctr-rout-left (* 4 ctr-rout-oo-right))
;
;)

