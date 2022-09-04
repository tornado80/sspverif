;missing:
;precondition holds on starting state

(check-sat)

(push 1)
;pre-condition => lemmas
(assert (and precondition-holds
             (not is-abort-right)
             (not is-abort-left)
             (not lemmas-hold)))

(check-sat)
(pop 1)

(push 1)

;pre-condition + lemmas => post-condition
(assert (and precondition-holds
             lemmas-hold
             (not is-abort-right)
             (not is-abort-left)
             (not postcondition-holds)))

(check-sat)
(pop 1)

(push 1)

;pre-condition + lemmas => standard post-condition
(assert (and precondition-holds 
             lemmas-hold
             (not standard-postcondition-holds)))
(check-sat)
(pop 1)
