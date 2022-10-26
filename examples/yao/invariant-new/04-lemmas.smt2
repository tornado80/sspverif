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
(table-top-left-alt (state-keys-T bottom-key-package-left-alt))
(table-top-left-neu (state-keys-T bottom-key-package-left-neu))
(table-bottom-left-alt (state-keys-T bottom-key-package-left-alt))
(table-bottom-left-neu (state-keys-T bottom-key-package-left-neu))
)


;;;top key packages don't change
(table-top-left-alt table-top-left-neu)

)))
