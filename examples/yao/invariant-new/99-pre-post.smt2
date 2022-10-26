(push 1)

(check-sat) ;2
;(get-model)
(pop 1)

(push 1)

(assert (and (invariant-keys state-left-old state-right-old)
             (invariant-ctr state-left-old state-right-old)
             (not is-abort-right)
             (not is-abort-left)
             (not (invariant-keys state-left-old state-right-after-EVAL))))
(check-sat) ;2
;(get-model)
(pop 1)

(push 1)

(assert (and (invariant-keys state-left-old state-right-old)
             (invariant-keys state-left-new state-right-after-EVAL)
             (invariant-ctr state-left-old state-right-old)
             (not is-abort-right)
             (not is-abort-left)
             (not (invariant-keys state-left-new state-right-new))))
(check-sat) ;2
;(get-model)
(pop 1)




(push 1)

(assert (and (invariant-keys state-left-old state-right-old)
             (invariant-ctr state-left-old state-right-old)
             (invariant-keys state-left-new state-right-new)
             (not is-abort-right)
             (not is-abort-left)
             (not (invariant-ctr state-left-new state-right-new))))
(check-sat) ;3
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
(check-sat) ;4
;(get-model)
(pop 1)
