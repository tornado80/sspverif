; At each entry, the table is either none or a total table
(define-fun well-defined ((T (Array Int (Maybe (Array Bool (Maybe Bits_n)))))) Bool
  (forall ((h Int))
    (ite
      (not
        (= (select T h) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
      )
      (forall ((b Bool))
        (not
          (= (select (maybe-get (select T h)) b) (as mk-none (Maybe Bits_n)))
        )
      )
      true
    )
  )
)

(declare-const hhh Int)
(define-fun well-defined-ish ((T (Array Int (Maybe (Array Bool (Maybe Bits_n)))))(hhh Int)) Bool
    (ite
      (not
        (= (select T hhh) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
      )
      (forall ((b Bool))
        (not
          (= (select (maybe-get (select T hhh)) b) (as mk-none (Maybe Bits_n)))
        )
      )
      true
    )
  )


(push 1)

(assert true)
(check-sat) ;3

(pop 1)
