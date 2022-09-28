
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
(check-sat) ;4 ;8
;(get-model)
(pop 1)





(push 1)

(assert (and precondition-holds
             lemma1
             (not is-abort-right)
             (not is-abort-left)
             (not lemma2)))
(check-sat) ;5 ;9
;(get-model)
(pop 1)

(push 1)
(assert (and precondition-holds
             lemma1
             lemma2
             (not is-abort-right)
             (not is-abort-left)
             (not lemma3)))
(check-sat) ;6 ;10
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
(check-sat) ;7 ;11
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
;(assert (and precondition-holds
;             (not is-abort-right)
;             (not is-abort-left)
;             (not lemmas-hold)))
;
;
;(check-sat) ;13
;;(get-model)
;(pop 1)
;
;(push 1)

;pre-condition + lemmas => post-condition
(assert (and precondition-holds
             lemmas-hold
             (not is-abort-right)
             (not is-abort-left)
             (not postcondition-holds)))

(check-sat) ;8 ;12
;(get-model)
(pop 1)

(push 1)

;pre-condition + lemmas => standard post-condition
(assert (and precondition-holds 
             lemmas-hold
             postcondition-holds
             (not standard-postcondition-holds)))
(check-sat) ;9 ;13
(get-model)
(pop 1)

(push 1)
