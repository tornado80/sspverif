
;;;;;;;;;;;;; temp
;(push 1)

;(assert precondition-holds)
;(check-sat) ;7

;(pop 1)

(push 1)

(assert (and precondition-holds
             (not is-abort-right)
             (not is-abort-left)
             (not lemma1)))
(check-sat) ;2 ;4 ;8
;(get-model)
(pop 1)





(push 1)

(assert (and precondition-holds
             lemma1
             (not is-abort-right)
             (not is-abort-left)
             (not lemma2)))
(check-sat) ;3 ;5 ;9
;(get-model)
(pop 1)

(push 1)
(assert (and precondition-holds
             lemma1
             lemma2
             (not is-abort-right)
             (not is-abort-left)
             (not lemma3)))
(check-sat) ;4 ;6 ;10
;(get-model)
(pop 1)

(push 1)
(assert (and precondition-holds
             lemma1
             lemma2
             lemma3
             (not is-abort-right)
             (not is-abort-left)
             (not lemma4)))
(check-sat) ;5 ;7 ;11
;(get-model)
(pop 1)

(push 1)


;pre-condition + lemmas => post-condition
(assert (and precondition-holds
             lemmas-hold
             (not is-abort-right)
             (not is-abort-left)
             (not postcondition-holds)))

(check-sat) ;6  ;12
;(get-model)
(pop 1)

(push 1)

;pre-condition + lemmas => standard post-condition
(assert (and precondition-holds 
             lemmas-hold
             postcondition-holds
             (not is-abort-right)
             (not is-abort-left)
             (not (= value-left value-right))))
(check-sat) ;7  ;13
(pop 1)

(push 1)
(assert (and precondition-holds
        (or
        (not (ite is-abort-left is-abort-right true))))
)
(check-sat) ;8
;(get-model)
(pop 1)

(push 1)
(assert (and precondition-holds
        (or
        (not (ite is-abort-right is-abort-left true))))
)
(check-sat) ;9
(get-model)
(pop 1)

