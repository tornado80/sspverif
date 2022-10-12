;;;;;;;;;;;; High-level goal
; pre-condition => (1) left-abort <=> right-abort
;                  (2) if no abort =>
;                               (a) pre-condition as post-condition
;                               (b) y-left = y-right
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
             is-abort-left
        (not is-abort-right))
)


(check-sat) ;8
;(get-model)
(pop 1)

(push 1)
(assert (and precondition-holds
             (or
 (= (select table-flag-top-right-old l) (as mk-none (Maybe Bool)))
 (= (select table-flag-top-right-old l) (mk-some false))
 (= (select table-flag-top-right-old r) (as mk-none (Maybe Bool)))
 (= (select table-flag-top-right-old r) (mk-some false))
             )
        (not is-abort-left))
)

(check-sat) ;9
;(get-model)
(pop 1)

(push 1)
(assert (and precondition-holds
        (not  (or
 (= (select table-flag-top-right-old l) (as mk-none (Maybe Bool)))
 (= (select table-flag-top-right-old l) (mk-some false))
 (= (select table-flag-top-right-old r) (as mk-none (Maybe Bool)))
 (= (select table-flag-top-right-old r) (mk-some false))
             ))
(or
 (= (select table-z-bottom-right-old j) (mk-some true))
 (= (select table-z-bottom-right-old j) (mk-some false))
)
             is-abort-right
        (not is-abort-left))
)

(check-sat) ;10
;(get-model)
(pop 1)

(push 1)

(assert (and precondition-holds
        (not  (or
 (= (select table-flag-top-right-old l) (as mk-none (Maybe Bool)))
 (= (select table-flag-top-right-old l) (mk-some false))
 (= (select table-z-top-right-old l) (as mk-none (Maybe Bool)))
 (= (select table-flag-top-right-old r) (as mk-none (Maybe Bool)))
 (= (select table-flag-top-right-old r) (mk-some false))
 (= (select table-z-top-right-old r) (as mk-none (Maybe Bool)))
 (= (select table-z-bottom-right-old j) (mk-some true))
 (= (select table-z-bottom-right-old j) (mk-some false))
        ))
             is-abort-right
        )
)

(check-sat) ;11
(get-model)
(pop 1)

(push 1)
(assert (and precondition-holds
        (not  (or
 (= (select table-flag-top-right-old l) (as mk-none (Maybe Bool)))
 (= (select table-flag-top-right-old l) (mk-some false))
 (= (select table-flag-top-right-old r) (as mk-none (Maybe Bool)))
 (= (select table-flag-top-right-old r) (mk-some false))
 (= (select table-z-bottom-right-old j) (mk-some true))
 (= (select table-z-bottom-right-old j) (mk-some false))
        ))
             is-abort-right
        (not is-abort-left))
)

(check-sat) ;12
(get-model)
(pop 1)
