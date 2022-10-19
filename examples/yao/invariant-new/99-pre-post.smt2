(push 1)

(assert (and (invariant-key state-left-old state-right-old)
             (not is-abort-right)
             (not is-abort-left)
             (not (invariant-key state-left-new state-right-new))))
(check-sat) ;2
;(get-model)
(pop 1)

(push 1)

(assert (and (invariant-key state-left-old state-right-old)
             (invariant-ctr state-left-old state-right-old)
             (invariant-key state-left-new state-right-new)
             (not is-abort-right)
             (not is-abort-left)
             (not (invariant-ctr state-left-new state-right-new))))
(check-sat) ;3
;(get-model)
(pop 1)

(push 1)

(assert (and (invariant-key state-left-old state-right-old)
             (invariant-ctr state-left-old state-right-old)
             (invariant-key state-left-new state-right-new)
             (invariant-ctr state-left-new state-right-new)
             (not is-abort-right)
             (not is-abort-left)
             (y-left y-right)
             ))
(check-sat) ;4
;(get-model)
(pop 1)
