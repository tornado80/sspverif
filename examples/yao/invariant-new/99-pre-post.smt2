


(push 1)
(assert (and (invariant-keys state-left-old state-right-old)
             (invariant-ctr state-left-old state-right-old)
             (not is-abort-right)
             (not is-abort-left)
             (not (lemma1-left-keys state-left-old state-left-new))))
(check-sat) ;3
;(get-model)
(pop 1)

(push 1)

(assert (and (invariant-keys state-left-old state-right-old)
             (invariant-ctr state-left-old state-right-old)
             (not is-abort-right)
             (not is-abort-left)
             (lemma1-left-keys state-left-old state-left-new)
             (not (lemma1-right-keys state-right-old state-right-new))))
(check-sat) ;4
;(get-model)
(pop 1)

(push 1)

(assert (and (invariant-keys state-left-old state-right-old)
             (invariant-ctr state-left-old state-right-old)
             (not is-abort-right)
             (not is-abort-left)
             (lemma1-left-keys state-left-old state-left-new)
             (lemma1-right-keys state-right-old state-right-new)
             (not (lemma1-keys state-left-new state-right-old))))
(check-sat) ;5
;(get-model)
(pop 1)

(push 1)

(assert (and (invariant-keys state-left-old state-right-old)
             (invariant-ctr state-left-old state-right-old)
             (not is-abort-right)
             (not is-abort-left)
             (lemma1-left-keys state-left-old state-left-new)
             (lemma1-right-keys state-right-old state-right-new)
             (lemma1-keys       state-left-new   state-right-old)
             (not (lemma2-left-keys state-left-old state-left-new))
             ))
(check-sat) ;6
;(get-model)
(pop 1)

(push 1)

(assert (and (invariant-keys state-left-old state-right-old)
             (invariant-ctr state-left-old state-right-old)
             (not is-abort-right)
             (not is-abort-left)
             (lemma1-left-keys state-left-old state-left-new)
             (lemma1-right-keys state-right-old state-right-new)
             (lemma1-keys       state-left-new   state-right-old)
             (lemma2-left-keys state-left-old state-left-new)
             (not (lemma2-right-keys state-right-old state-right-new))
             ))
(check-sat) ;7
;(get-model)
(pop 1)


(push 1)

(assert (and (invariant-keys state-left-old state-right-old)
             (invariant-ctr state-left-old state-right-old)
             (not is-abort-right)
             (not is-abort-left)
             (lemma1-left-keys  state-left-old   state-left-new)
             (lemma1-right-keys state-right-old  state-right-new)
             (lemma1-keys       state-left-new   state-right-old)
             (lemma2-left-keys  state-left-old   state-left-new)
             (lemma2-right-keys state-right-old  state-right-new)
             (not (lemma2-keys  state-left-new   state-right-new))))
(check-sat) ;8
;(get-model)
(pop 1)

(push 1)

(assert (and (invariant-keys state-left-old state-right-old)
             (invariant-ctr state-left-old state-right-old)
             (not is-abort-right)
             (not is-abort-left)
             (lemma1-left-keys  state-left-old   state-left-new)
             (lemma1-right-keys state-right-old  state-right-new)
             (lemma1-keys       state-left-new   state-right-old)
             (lemma2-left-keys  state-left-old   state-left-new)
             (lemma2-right-keys state-right-old  state-right-new)
             (not (invariant-keys state-left-new state-right-new))))
(check-sat) ;8
;(get-model)
(pop 1)




(push 1)

(assert (and (invariant-keys state-left-old state-right-old)
             (invariant-ctr state-left-old state-right-old)
             (invariant-keys state-left-new state-right-new)
             (not is-abort-right)
             (not is-abort-left)
             (not (invariant-ctr state-left-new state-right-new))))
(check-sat) ;9
;(get-model)
(pop 1)

(push 1)

(assert (and (invariant-keys state-left-old state-right-old)
             (invariant-ctr state-left-old state-right-old)
             (invariant-keys state-left-new state-right-new)
             (invariant-ctr state-left-new state-right-new)
             (not is-abort-right)
             (not is-abort-left)
             (= y-left y-right)
             ))
(check-sat) ;10
;(get-model)
(pop 1)
