(push 1)

(check-sat) 

(pop 1)

;;;;;;;;;;;;; temp

(assert precondition-holds)

(push 1)

(check-sat)

(pop 1)

(assert (and precondition-holds
             (not is-abort-right)
             (not is-abort-left)
             (not lemma4)))

(push 1)

(check-sat)
(get-model)

(pop 1)

(assert (and precondition-holds
             (not is-abort-right)
             (not is-abort-left)
             (not lemma3)))
(push 1)

(check-sat)

(pop 1)

(assert (and precondition-holds
             (not is-abort-right)
             (not is-abort-left)
             (not lemma2)))
(push 1)

(check-sat)

(pop 1)

(assert (and precondition-holds
             (not is-abort-right)
             (not is-abort-left)
             (not lemma1)))
(push 1)

(check-sat)

(pop 1)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; end of temp
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;missing:
;precondition holds on starting state
(push 1)

(check-sat)

(pop 1)
;pre-condition => lemmas
(assert (and precondition-holds
             (not is-abort-right)
             (not is-abort-left)
             (not lemmas-hold)))


(push 1)

(check-sat)
;(get-model)

(pop 1)

;pre-condition + lemmas => post-condition
(assert (and precondition-holds
             lemmas-hold
             (not is-abort-right)
             (not is-abort-left)
             (not postcondition-holds)))

;(get-model)

;pre-condition + lemmas => standard post-condition
(assert (and precondition-holds 
             lemmas-hold
             (not standard-postcondition-holds)))
(push 1)

(check-sat)
;(get-model)

(pop 1)
