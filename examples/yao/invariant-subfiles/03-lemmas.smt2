(declare-const lemmas-hold Bool)
(declare-const lemma1 Bool)
(declare-const lemma2 Bool)
(declare-const lemma3 Bool)
(declare-const lemma4 Bool)
(declare-const lemma5 Bool)

(assert (= lemmas-hold (and
lemma1
lemma2
lemma3
lemma4
lemma5)))

(assert (= lemma1 (and
;;;; Lemma on key tables
(well-defined table-top-left-new)
(well-defined table-top-right-new)
(well-defined table-bottom-left-new)
(well-defined table-bottom-right-new)
)))

(declare-const debug-top-left Bool)
(declare-const debug-top-right Bool)
(declare-const debug-bottom-left Bool)
(declare-const debug-bottom-right Bool)

(assert 
(and
(= (well-defined table-top-left-new) debug-top-left)
(= (well-defined table-top-right-new) debug-top-right)
(= (well-defined-ish table-bottom-left-new hhh) debug-bottom-left)
(= (well-defined-ish table-bottom-right-new hhh) debug-bottom-right)
))





(assert (= lemma2 (and
; top tables remain the same
(= table-top-left-old table-top-left-new)
(= table-top-right-old table-top-right-new)
)))

(assert (= lemma3 (and
; left: bottom tables are mostly equal and where they are not equal, there is Z
(forall ((hh Int))
(ite
(and (= j hh) (= (select table-bottom-left-old hh) (as mk-none (Maybe (Array Bool (Maybe Bits_n))))))
(= (select table-bottom-left-new hh) (mk-some Z-left))
(= (select table-bottom-left-old hh) (select table-bottom-left-new hh))
))
)))

;(declare-const hhh Int)

(assert (= lemma4 (and
; right: bottom tables are mostly equal and where they are not equal, there is Z
(forall ((hh Int))
(ite
(and (= j hh) (= (select table-bottom-right-old hh) (as mk-none (Maybe (Array Bool (Maybe Bits_n))))))
(= (select table-bottom-right-new hh) (mk-some Z-right))
(= (select table-bottom-right-old hh) (select table-bottom-right-new hh))
))
))
)

;(push 1)

;(assert true)
;(check-sat) ;5

;(pop 1)

