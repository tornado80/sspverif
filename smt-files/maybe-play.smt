(declare-datatypes ((Maybe 1))
  ; for CVC4
  ;((par (T) ((mk-some (get T)) (mk-none (hint T))))))
  ; for z3
  ((par (T) ((mk-some (get T)) (mk-none)))))


(declare-const some-string (Maybe String))
(declare-const bot-string (Maybe String))

(declare-const whatisthisthing String)
(declare-const this-is-bot Bool)

(declare-const whatisthatthing String)
(declare-const that-is-bot Bool)

(assert (= some-string (mk-some "foo")))
; CVC4 needs a type hint for String here
;(assert (= bot-string  (mk-none "")))
; z3 doesn't
(assert (= bot-string (as mk-none (Maybe String))))


(assert (= ((_ is mk-none) bot-string) this-is-bot))
(assert (= ((_ is mk-none) some-string) that-is-bot))

; CVC4 says this is "", z3 says this is (get (mk-none ""))
; Personally, I think z3 is right (jw)
;   1y later: I think both are correct, because I have
;   since learned about the (_ is X) tester. (jw)
(assert (= whatisthisthing (get bot-string)))
(assert (= whatisthatthing (get some-string))) ; "foo"



(declare-datatypes ((list 1)) 
    ((par (T) (
        (cons (head T) (tail (list T)))
        (nil)
    )))
)




(check-sat)
(get-model)