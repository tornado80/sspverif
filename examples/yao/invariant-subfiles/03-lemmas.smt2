(declare-const lemmas-hold Bool)
(assert (= lemmas-hold (and
;;;; Lemma on key tables
(well-defined table-top-left-new)
(well-defined table-top-right-new)
(well-defined table-bottom-left-new)
(well-defined table-bottom-right-new)

; top tables remain the same
(= table-top-left-old table-top-left-new)
(= table-top-right-old table-top-right-new)

; left: bottom tables are mostly equal and where they are not equal, there is Z
(forall hh
(or
(= (select table-bottom-left-old hh) (select table-bottom-left-new hh))
(and
(= h hh)
(= (select table-bottom-left-new hh) Z)
)))

; right: bottom tables are mostly equal and where they are not equal, there is Z
(forall hh
(or
(= (select table-bottom-right-old hh) (select table-bottom-right-new hh))
(and
(= h hh)
(= (select table-bottom-right-new hh) Z)
)))
)))
 
