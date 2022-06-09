(
  ;; universe for Bits_n:
  ;;   Bits_n!val!1 Bits_n!val!0
  ;; -----------
  ;; definitions for universe elements:
  (declare-fun Bits_n!val!1 () Bits_n)
  (declare-fun Bits_n!val!0 () Bits_n)
  ;; cardinality constraint:
  (forall ((x Bits_n)) (or (= x Bits_n!val!1) (= x Bits_n!val!0)))
  ;; -----------


;; As required, state-left-old = state-right-old
  (define-fun state-left-old () CompositionState-CompositionLeft
    (let ((a!1 (mk-state-CompositionLeft-key
             (store ((as const (Array Int (Maybe Bits_n)))
                      (mk-some Bits_n!val!1))
                    1
                    (mk-some Bits_n!val!0)))))
  (mk-composition-state-CompositionLeft
    (mk-state-CompositionLeft-__randomness 0)
    a!1)))

;; As required, state-left-old = state-right-old
  (define-fun state-right-old () CompositionState-CompositionRight
    (let ((a!1 (mk-state-CompositionRight-key
             (store ((as const (Array Int (Maybe Bits_n)))
                      (mk-some Bits_n!val!1))
                    1
                    (mk-some Bits_n!val!0)))))
  (mk-composition-state-CompositionRight
    (mk-state-CompositionRight-__randomness 0)
    a!1)))

;; We make a query with handle = 1
  (define-fun handle () Int
    1)

;; We obtain back key = Bits_n!val!1, but how can this be?
  (define-fun key-left () Bits_n
    Bits_n!val!1)

;; We obtain back key = Bits_n!val!0 since this is the key value everywhere
  (define-fun key-right () Bits_n
    Bits_n!val!0)



;; As required, state-left-new = state-right-new
  (define-fun state-right-new () CompositionState-CompositionRight
    (mk-composition-state-CompositionRight
  (mk-state-CompositionRight-__randomness 0)
  (mk-state-CompositionRight-key
    ((as const (Array Int (Maybe Bits_n))) (mk-some Bits_n!val!0)))))

;; As required, state-left-new = state-right-new
  (define-fun state-left-new () CompositionState-CompositionLeft
    (mk-composition-state-CompositionLeft
  (mk-state-CompositionLeft-__randomness 0)
  (mk-state-CompositionLeft-key
    ((as const (Array Int (Maybe Bits_n))) (mk-some Bits_n!val!0)))))

 
  (define-fun __sample-rand-CompositionRight ((x!0 Int)) Bits_n
    Bits_n!val!1)
 
  (define-fun __sample-rand-CompositionLeft ((x!0 Int)) Bits_n
    (__sample-rand-CompositionRight x!0))
)