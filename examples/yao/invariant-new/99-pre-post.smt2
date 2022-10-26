;(push 1)
;(assert true)
;(check-sat) ;7
;(pop 1)


(push 1)

(assert (and (invariant-keys state-left-old state-right-old)
             (invariant-ctr state-left-old state-right-old)
             (not is-abort-right)
             (not is-abort-left)
             (not (invariant-keys state-left-old state-right-old))))
(check-sat) ;5 ;8
;(get-model)
(pop 1)

(push 1)

(assert (and (invariant-keys state-left-old state-right-old)
             (invariant-ctr state-left-old state-right-old)
             (not is-abort-right)
             (not is-abort-left)
             (not (weak-invariant-keys state-left-old state-right-old))))
(check-sat) ;5 ;8
;(get-model)
(pop 1)

(push 1)

(assert (and (invariant-keys state-left-old state-right-old)
             (invariant-ctr state-left-old state-right-old)
             (not is-abort-right)
             (not is-abort-left)
             (not lemma1-left-keys)))
(check-sat) ;5 ;8
;(get-model)
(pop 1)

(push 1)

(assert (and (invariant-keys state-left-old state-right-old)
             (invariant-ctr state-left-old state-right-old)
             (not is-abort-right)
             (not is-abort-left)
             lemma1-left-keys
             (not (weak-invariant-keys state-left-new state-right-old))))
(check-sat) ;5 ;8
;(get-model)
(pop 1)


(push 1)

(assert (and (invariant-keys state-left-old state-right-old)
             (invariant-keys state-left-new state-right-after-EVAL)
             (invariant-ctr state-left-old state-right-old)
             (not is-abort-right)
             (not is-abort-left)
             (not (invariant-keys state-left-new state-right-new))))
(check-sat) ;6 ;9
;(get-model)
(pop 1)




(push 1)

(assert (and (invariant-keys state-left-old state-right-old)
             (invariant-ctr state-left-old state-right-old)
             (invariant-keys state-left-new state-right-new)
             (not is-abort-right)
             (not is-abort-left)
             (not (invariant-ctr state-left-new state-right-new))))
(check-sat) ;10
;(get-model)
(pop 1)

(push 1)

(assert (and (invariant-keys state-left-old state-right-old)
             (invariant-ctr state-left-old state-right-old)
             (invariant-keys state-left-new state-right-new)
             (invariant-ctr state-left-new state-right-new)
             (not is-abort-right)
             (not is-abort-left)
             (y-left y-right)
             ))
(check-sat) ;11
;(get-model)
(pop 1)
