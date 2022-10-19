(define-fun invariant ((state-left Type)(state-right Type)) Bool

(let

; state of the key packages
(= top-key-package-left ...)
(= top-key-package-right ...)
(= bottom-key-package-left ...)
(= bottom-key-package-right ...)

(let

; table of the bottom key package
(table-bottom-left ...)
(table-bottom-right ...)

(and
;top key package states are equal
(= top-key-package-left top-key-package-left)

;for bottom key package, tables are equal
(= table-bottom-left table-bottom-right)

;top key packages behave like a key packages
(= true well-defined-Key-active top-key-package-left)
(= true well-defined-Key-active top-key-package-right)

;bottom key packages behave like a key packages
(= true well-defined-Key-active bottom-key-package-left)
(= true well-defined-Key-active bottom-key-package-right)

))))