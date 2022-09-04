; At each entry, the table is either none or a total table
(define-fun well-defined ((T (Array Int (Maybe (Array Bool (Maybe Bits_n)))))) Bool
  (forall ((h Int))
    (or
    ; either undefined
        (
        (= (select T h) (as mk-none (Maybe (Array Int (Maybe (Array Bool (Maybe Bits_n))))))))
    ; or total
    (forall ((b Bool))
        (not
        (= (select (select T h) b) (as mk-none (Maybe Bits_n))))
        )
    )
  )
)