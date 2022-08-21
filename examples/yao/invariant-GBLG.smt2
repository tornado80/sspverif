; Goal:
; Use equality on KEYS packages as invariant
; prove that on same inputs, all oracles give same output

; possible input for all (and sufficient for GETKEYSIN/GETKEYSOUT):
(declare-const handle Int)

; possible input for SETBIT
(declare-const bit Bool)

; possible input for GBLG     oracle GBLG(h: Integer, l: Integer, r: Integer, op: fn Bool,Bool -> Bool, j: Integer) -> Table(Bits(p),Bool) {
(declare-const l Integer)
(declare-const r Integer)
(declare-const op fun (Bool Bool) Bool)

; possible state
(declare-const state-left-old CompositionState-Left)
(declare-const state-right-old CompositionState-Right)
(declare-const state-left-new CompositionState-Left)
(declare-const state-right-new CompositionState-Right)

; return value - type depends on oracle call; only GBLG is interesting, actually.
(declare-const return-left Return_Left_gate_left_GBLG)
(declare-const return-right Return_Right_simgate_GBLG)
(declare-const is-abort-left Bool)
(declare-const is-abort-right Bool)


(assert (and  ;return-left and return-right are helper variables
              (= return-left      (oracle-Left-prf_left-EVAL state-left-old handle message))
              (= return-right     (oracle-Right-wrapper-EVAL state-right-old handle message))

              ;return values are the same on both sides
              (= value-left       (return-Left-prf_left-EVAL-value return-left))
              (= value-right      (return-Right-wrapper-EVAL-value return-right))

              ;return both sides either abort or do not abort
              (= is-abort-left    (= mk-abort-Left-prf_left-EVAL return-left))
              (= is-abort-right   (= mk-abort-Right-wrapper-EVAL return-right))

              ;helper variables for new left state and new right state which will be used below
              (= state-left-new   (return-Left-prf_left-EVAL-state return-left))
              (= state-right-new  (return-Right-wrapper-EVAL-state return-right))))

              ;Here, we need to additionally say something about sample instructions for lower Key package


; The 2 top key packages should have the same state on the left and the right.
(define-fun key-top-lr-eq ((left CompositionState-Left) (right CompositionState-Right)) Bool
  (forall ((h Int)) (=  (select (state-Left-key_top-T (composition-state-Left-key_top left))
                                h)
                        (select (state-Right-key_top-T (composition-state-Right-key_top right))
                                h))))

; The state of the top key package does not change when GBLG is called on the left
(define-fun key-top-ll-eq ((old CompositionState-Left) (new CompositionState-Left)) Bool
  (forall ((h Int)) (=  (select (state-Left-key_top-T (composition-state-Left-key_top old))
                                h)
                        (select (state-Left-key_top-T (composition-state-Left-key_top new))
                                h))))

; The state of the top key package does not change when GBLG is called on the right
(define-fun key-top-rr-eq ((old CompositionState-Right) (new CompositionState-Right)) Bool
  (forall ((h Int)) (=  (select (state-Right-key_top-T (composition-state-Right-key_top old))
                                h)
                        (select (state-Right-key_top-T (composition-state-Right-key_top new))
                                h))))

; The state of the bottom key package on the left is mostly the same as before except at the point h that was written to
(define-fun key-bottom-l-mostly-eq ((old CompositionState-Left) (new CompositionState-Left) (h Int)) Bool
  (forall ((hh Int))  (or (= h hh)
                                      (=  (select (state-Left-key_bottom-T (composition-state-Left-key_bottom new))
                                                  (mk-tuple2 hh))
                                          (select (state-Left-key_bottom-T (composition-state-Left-key_bottom old))
                                                  (mk-tuple2 hh))))))


; The state of the bottom key package on the right is mostly the same as before except at the point h that was written to
(define-fun key-bottom-r-mostly-eq ((old CompositionState-Right) (new CompositionState-Right) (h Int)) Bool
  (forall ((hh Int))  (or (= h hh)
                                      (=  (select (state-Right-key_bottom-T (composition-state-Right-key_bottom new))
                                                  (mk-tuple2 hh))
                                          (select (state-Right-key_bottom-T (composition-state-Right-key_bottom old))
                                                  (mk-tuple2 hh))))))

; The state of the bottom key package on the right at position h is equal to what was sampled (or was defined before).
(define-fun key-bottom-r-ok-after-call ((old CompositionState-Right) (new CompositionState-Right) (h Int)) Bool 
  (=      (maybe-get (select  (state-Right-key_bottom-T (composition-state-Right-key_bottom new))
                              (mk-tuple2 h)))
                              ; put randomness sampling here XXX
      (f  (maybe-get (select  (state-Right-key_top-T    (composition-state-Right-key_top    old))
                              h))
          m)))

; The state of the bottom key package on the left at position h is equal to what was sampled (or was defined before)).
(define-fun key-bottom-r-ok-after-call ((old CompositionState-Left) (new CompositionState-Left) (h Int)) Bool 
  (=      (maybe-get (select  (state-Left-key_bottom-T (composition-state-Left-key_bottom new))
                              (mk-tuple2 h)))
                              ; put randomness sampling here XXX
      (f  (maybe-get (select  (state-Left-key_top-T    (composition-state-Left-key_top    old))
                              h))
          m)))

; should this really use the old state?? Not here
(define-fun post-condition ((left CompositionState-Left) (right CompositionState-Right) (h Int)) Bool
  (forall ((h Int)) (=  (select (state-Left-key_top-T (composition-state-Left-key_top left))
                                h)
                        (select (state-Right-key_top-T (composition-state-Right-key_top  right))
                                h))))


(declare-const precondition-holds Bool)
(assert (= precondition-holds (and  (not is-abort-right)
                                    (not is-abort-left)
                                    (key-bottom-ok state-right-old)
                                    (key-top-lr-eq state-left-old state-right-old))))

;; This is just to verify that the current state is satisfiable. It definitely should be.
(check-sat)

(push 1)
;;; prove right bottom key mostly equal lemma
(assert (and  precondition-holds
              (not
                ;; proved statement starts here
                (key-bottom-mostly-eq state-right-old state-right-new handle message))))
(check-sat)
(pop 1)

(push 1)
;;; prove right bottom keys wellformed after call lemma
(assert (and  precondition-holds
              ;; lemmata start here
              (not (key-bottom-ok-after-call state-right-old state-right-new handle message))))
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
(assert (and    precondition-holds
                ;;; lemmata start here
                (key-top-ll-eq state-left-old state-left-new)
                (key-top-rr-eq state-right-old state-right-new)
                (key-top-lr-eq state-left-new state-right-new)
                (key-bottom-mostly-eq state-right-old state-right-new handle message)
                (key-bottom-ok-after-call state-right-old state-right-new handle message)
                (or
                    (not (post-condition state-left-new state-right-new handle message))
                    (not (key-bottom-ok state-right-new)))))
(check-sat)
(pop 1)

; this should not be a problem.
; the fact that this is a problem might be informative.
(push 1)
;(assert (key-tables-empty state-right-old))

;(assert (and  (right-key-bottom-set-implies-top-set state-right-old)))
              ;(right-key-top-set-implies-bottom-set state-right-old)))
      
(assert (key-bottom-ok state-right-old))
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