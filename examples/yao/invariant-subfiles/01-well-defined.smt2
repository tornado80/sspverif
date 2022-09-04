; At each entry, the table is either none or a total table
(define-fun well-defined ((T (Array(Int Maybe(Array(Bool Maybe(Bits(n)))))))) Bool
  (forall ((h Int))
    (or
    ; either undefined
        (
        (= (as mk-none (Maybe (Array(Bool Maybe(Bits(n)))))) (select (T h))))
    (forall ((b Bool))
        (not
        (= (as mk-none (Maybe Bits_n)) (select (select T h) b)))
        )
    )
  )
)