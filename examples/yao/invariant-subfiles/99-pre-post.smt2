
;;;;;;;;;;;;; temp
(push 1)

(assert precondition-holds)
(check-sat) ;8

(pop 1)

(push 1)

(assert (and precondition-holds
             (not is-abort-right)
             (not is-abort-left)
             (not lemma4)))
(check-sat) ;9
(get-model)
(pop 1)





(push 1)

(assert (and precondition-holds
             (not is-abort-right)
             (not is-abort-left)
             (not lemma3)))
(check-sat) ;10
;(get-model)
(pop 1)

(push 1)
(assert (and precondition-holds
             (not is-abort-right)
             (not is-abort-left)
             (not lemma2)))
(check-sat) ;11
;(get-model)
(pop 1)

(push 1)
(assert (and precondition-holds
             (not is-abort-right)
             (not is-abort-left)
             (not lemma1)))
(check-sat) ;12
;(get-model)
(pop 1)

(push 1)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; end of temp
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;missing:
;precondition holds on starting state
;pre-condition => lemmas
(assert (and precondition-holds
             (not is-abort-right)
             (not is-abort-left)
             (not lemmas-hold)))


(check-sat) ;13
;(get-model)
(pop 1)

(push 1)

;pre-condition + lemmas => post-condition
(assert (and precondition-holds
             lemmas-hold
             (not is-abort-right)
             (not is-abort-left)
             (not postcondition-holds)))

(check-sat) ;14
;(get-model)
(pop 1)

(push 1)

;pre-condition + lemmas => standard post-condition
(assert (and precondition-holds 
             lemmas-hold
             (not standard-postcondition-holds)))
(check-sat) ;15
;(get-model)
(pop 1)

(push 1)
