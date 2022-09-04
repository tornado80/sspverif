; Goal:
; Use equality on KEYS packages as invariant
; prove that on same inputs, all oracles give same output

; possible input for all (and sufficient for GETKEYSIN/GETKEYSOUT):
(declare-const handle Int)

; possible input for SETBIT
(declare-const bit Bool)

; possible input for GBLG     oracle GBLG(h: Integer, l: Integer, r: Integer, op: fn Bool,Bool -> Bool, j: Integer) -> Table(Bits(p),Bool) {
(declare-const l Int)
(declare-const r Int)
(declare-const op (Array (Tuple2 Bool Bool) (Maybe Bool)))
(declare-const j Int)


; possible state
(declare-const state-left-old CompositionState-Left)
(declare-const state-right-old CompositionState-Right)
(declare-const state-left-new CompositionState-Left)
(declare-const state-right-new CompositionState-Right)

; return value - type depends on oracle call; only GBLG is interesting, actually.
(declare-const return-left Return_Left_gate_GBLG)
(declare-const return-right Return_Right_simgate_GBLG)
(declare-const is-abort-left Bool)
(declare-const is-abort-right Bool)
(declare-const value-left (Array Bits_p (Maybe Bool)))
(declare-const value-right (Array Bits_p (Maybe Bool)))

; sampled value Z and associated values
(declare-const Z-left  (Array Bool (Maybe Bits_n)))
(declare-const Z-right (Array Bool (Maybe Bits_n)))
(declare-const ctr-r-left Int)
(declare-const ctr-r-right Int)
(declare-const ctr-rr-left Int)
(declare-const ctr-rr-right Int)
(declare-const r-left Bits_n)
(declare-const r-right Bits_n)
(declare-const rr-left Bits_n)
(declare-const rr-right Bits_n)



; composition-rand-Right-3 global-old-composition-state - this is the counter
; Die counter sind zufällig die gleichen
; pre-condition composition-rand-Left-3 old-state-l = composition-rand-Right-3 old-state-r 
; pre-condition composition-rand-Left-4 old-state-l = composition-rand-Right-4 old-state-r ;
;   __sample-rand-Left-Bits_n 3 composition-rand-Left-3 global-old-composition-state
; = __sample-rand-Right-Bits_n 3 composition-rand-Right-3 global-old-composition-state
;   __sample-rand-Left-Bits_n 3 composition-rand-Left-3 global-old-composition-state
; = __sample-rand-Right-Bits_n 3 composition-rand-Right-3 global-old-composition-state
;   __sample-rand-Right-Bits_n (composition-rand-Left-3 global-old-composition-state)



(assert (and  ;assignment of return (value,state)
              (= return-left      (oracle-Left-gate-GBLG state-left-old handle l r op j))
              (= return-right     (oracle-Right-simgate-GBLG state-right-old handle l r op j))

              ;assignment of return values
              (= value-left       (return-Left-gate-GBLG-value return-left))
              (= value-right      (return-Right-simgate-GBLG-value return-right))

              ;assignment of abort values
              (= is-abort-left    (= mk-abort-Left-gate-GBLG return-left))
              (= is-abort-right   (= mk-abort-Right-simgate-GBLG return-right))

              ;assignment of return state
              (= state-left-new   (return-Left-gate-GBLG-state return-left))
              (= state-right-new  (return-Right-simgate-GBLG-state return-right))

              ;assignment of the ctr of the sample instructions for the lower Key package
              (= ctr-r-left   (composition-rand-Left-3  state-left-old))
              (= ctr-r-right  (composition-rand-Right-3 state-right-old))
              (= ctr-rr-left  (composition-rand-Left-4  state-left-old))
              (= ctr-rr-right (composition-rand-Right-4 state-right-old))

              ;assignment of the sampled values for the lower Key package
              (= r-left   (__sample-rand-Left-Bits_n 3 ctr-r-left))
              (= r-right  (__sample-rand-Right-Bits_n 3 ctr-r-right))
              (= rr-left  (__sample-rand-Left-Bits_n 4 ctr-rr-left))
              (= rr-right (__sample-rand-Right-Bits_n 4 ctr-rr-left))

              ;assignment of the sampled values for the lower Key package as a table
              (=  r-left  (maybe-get (select Z-left    true)))
              (= rr-left  (maybe-get  (select Z-left  false)))
              (= r-right  (maybe-get  (select Z-right  true)))
              (= rr-right (maybe-get (select Z-right  false)))

              ;equality of ctr/values of the sample instructions for the lower Key package
              (= ctr-r-left ctr-r-right)
              (= ctr-rr-left ctr-rr-right)
              (= r-left r-right)
              (= rr-left rr-right)


))









; The 2 top key packages should have the same state on the left and the right.
(define-fun key-top-lr-eq ((left CompositionState-Left) (right CompositionState-Right)) Bool
  (forall ((h Int)) (=  (select (state-Left-keys_top-T (composition-pkgstate-Left-keys_top left))
                                h)
                        (select (state-Right-keys_top-T (composition-pkgstate-Right-keys_top right))
                                h))))

; Left: The state of the top key package does not change when GBLG is called
(define-fun key-top-ll-eq ((old CompositionState-Left) (new CompositionState-Left)) Bool
  (forall ((h Int)) (=  (select (state-Left-keys_top-T (composition-pkgstate-Left-keys_top old))
                                h)
                        (select (state-Left-keys_top-T (composition-pkgstate-Left-keys_top new))
                                h))))

; Right: The state of the top key package does not change when GBLG is called
(define-fun key-top-rr-eq ((old CompositionState-Right) (new CompositionState-Right)) Bool
  (forall ((h Int)) (=  (select (state-Right-keys_top-T (composition-pkgstate-Right-keys_top old))
                                h)
                        (select (state-Right-keys_top-T (composition-pkgstate-Right-keys_top new))
                                h))))

; Left: The state of the bottom key package is mostly the same as before except at the point h j r op that was written to
(define-fun key-bottom-l-mostly-eq ((old CompositionState-Left) (new CompositionState-Left) 
                                    (h Int) (l Int) (r Int) (op (Array (Tuple2 Bool Bool) (Maybe Bool)))) Bool
  (forall ((hh Int))  (or (= h hh)
                                      (=  (select (state-Left-keys_bottom-T (composition-pkgstate-Left-keys_bottom new))
                                                  hh)
                                          (select (state-Left-keys_bottom-T (composition-pkgstate-Left-keys_bottom old))
                                                  hh)))))


; The state of the bottom key package on the right is mostly the same as before except at the point h that was written to
(define-fun key-bottom-r-mostly-eq ((old CompositionState-Right) (new CompositionState-Right) 
                                    (h Int) (l Int) (r Int) (op (Array (Tuple2 Bool Bool) (Maybe Bool)))) Bool
  (forall ((hh Int))  (or (= h hh)
                                      (=  (select (state-Right-keys_bottom-T (composition-pkgstate-Right-keys_bottom new))
                                                  hh)
                                          (select (state-Right-keys_bottom-T (composition-pkgstate-Right-keys_bottom old))
                                                  hh)))))

; Right: The state of the bottom key package at position h is equal to what was sampled (or was defined before).
(define-fun key-bottom-r-ok-after-call ((old CompositionState-Right) (new CompositionState-Right) (h Int) (l Int) (r Int) (op (Array (Tuple2 Bool Bool) (Maybe Bool)))) Bool 
  (or
  (=  (select (state-Right-keys_bottom-T (composition-pkgstate-Right-keys_bottom new))
                                                  h)
                                          (select (state-Right-keys_bottom-T (composition-pkgstate-Right-keys_bottom old))
                                                  h))
  (=      (maybe-get (select  (state-Right-keys_bottom-T (composition-pkgstate-Right-keys_bottom new))
                              h))
                              ; put randomness sampling here XXX
                              ; if it was none before, then it is equal to sample now
          Z-right)))

; The state of the bottom key package on the left at position h is equal to what was sampled (or was defined before)).
(define-fun key-bottom-l-ok-after-call ((old CompositionState-Left) (new CompositionState-Left) (h Int) (l Int) (r Int) (op (Array (Tuple2 Bool Bool) (Maybe Bool)))) Bool 
  (or
  (=  (select (state-Left-keys_bottom-T (composition-pkgstate-Left-keys_bottom new))
                                                  h)
                                          (select (state-Left-keys_bottom-T (composition-pkgstate-Left-keys_bottom old))
                                                  h))                              ; put randomness sampling here
                              ; if it was none before, then it is equal to sample now
  (=  (maybe-get(select (state-Left-keys_bottom-T (composition-pkgstate-Left-keys_bottom new))
                                                  h))
                              
      Z-left)))

; should this really use the old state?? Not here
(define-fun post-condition ((left CompositionState-Left) (right CompositionState-Right) (h Int) (l Int) (r Int) (op (Array (Tuple2 Bool Bool) (Maybe Bool)))) Bool
  (forall ((h Int)) (=  (select (state-Left-keys_top-T (composition-pkgstate-Left-keys_top left))
                                h)
                        (select (state-Right-keys_top-T (composition-pkgstate-Right-keys_top  right))
                                h))))


(declare-const precondition-holds Bool)
(assert (= precondition-holds (and  (not is-abort-right)
                                    (not is-abort-left)
                                    ;(key-bottom-ok state-right-old)
                                    (key-top-lr-eq state-left-old state-right-old))))

;; This is just to verify that the current state is satisfiable. It definitely should be.
(check-sat)

(push 1)
;;; prove right bottom key mostly equal lemma
(assert (and  precondition-holds
              (not
                ;; proved statement starts here
                (key-bottom-r-mostly-eq state-right-old state-right-new handle l r op))))
(check-sat)
(pop 1)

(push 1)
;;; prove right bottom keys wellformed after call lemma
(assert (and  precondition-holds
              ;; lemmata start here
              (not (key-bottom-r-ok-after-call state-right-old state-right-new handle l r op))))
(check-sat)
(pop 1)

(push 1)
;;; prove right bottom key mostly equal lemma
(assert (and  precondition-holds
              (not
                ;; proved statement starts here
                (key-bottom-l-mostly-eq state-left-old state-left-new handle l r op))))
(check-sat)
(pop 1)

(push 1)
;;; prove right bottom keys wellformed after call lemma
(assert (and  precondition-holds
              ;; lemmata start here
              (not (key-bottom-l-ok-after-call state-left-old state-left-new handle l r op))))
(check-sat)
(pop 1)


(push 1)
;; prove left-left lemma
(assert (and  precondition-holds
              (not
                ;; proved statement starts here
                (key-top-ll-eq state-left-old state-left-new))))
(check-sat)
(pop 1)
;
;; prove right-right lemma
(push 1)
(assert (and  precondition-holds
              (not
                ;; proved statement starts here
                (key-top-rr-eq state-right-old state-right-new))))
(check-sat)
(pop 1)



(push 1)
; prove left-right lemma
(assert (and    precondition-holds
                ;; lemmata start here
                (key-top-rr-eq state-right-old state-right-new)
                (key-top-ll-eq state-left-old state-left-new)
                (not
                    ;; proved statement starts here
                    (key-top-lr-eq state-left-new state-right-new))))
(check-sat)
(pop 1)


;; check that the post-condition follows
(push 1)
(assert (and    ;precondition-holds
                ;;; lemmata start here
                (key-top-ll-eq state-left-old state-left-new)
                (key-top-rr-eq state-right-old state-right-new)
                (key-top-lr-eq state-left-new state-right-new)
                (key-bottom-l-mostly-eq state-left-old state-left-new handle l r op)
                (key-bottom-r-mostly-eq state-right-old state-right-new handle l r op)
                (key-bottom-l-ok-after-call state-left-old state-left-new handle l r op)
                (key-bottom-r-ok-after-call state-right-old state-right-new handle l r op)
                (or
                ;one of the post-conditions fail
                    (not (post-condition state-left-new state-right-new handle l r op))
                    (not (key-bottom-l-ok state-left-new))
                    (not (key-bottom-r-ok state-right-new))                    
                    )))
(check-sat)
(pop 1)

; this should not be a problem.
; the fact that this is a problem might be informative.
(push 1)
;(assert (key-tables-empty state-right-old))

;(assert (and  (right-key-bottom-set-implies-top-set state-right-old)))
              ;(right-key-top-set-implies-bottom-set state-right-old)))
      
(assert (key-bottom-r-ok state-right-old))
(check-sat)
;(get-model)
(pop 1)

(push 1)
(assert (key-bottom-l-ok state-left-old))
(check-sat)
;(get-model)
(pop 1)

;; this also shouldn't be a problem, but probably t his problem is just caused by the above problem.
(push 1)
;; check that there is a valid assignment for the precondition
(assert precondition-holds)
(check-sat)
;(get-model)
(pop 1)