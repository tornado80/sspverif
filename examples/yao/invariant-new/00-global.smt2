; layer handle:
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
(declare-const state-right-after-EVAL CompositionState-Right)
(declare-const state-left-new CompositionState-Left)
(declare-const state-right-new CompositionState-Right)

; possible state
(declare-const length-state-left-old Bool)
(declare-const length-state-right-old Bool)


(assert
(and

              ;assignment of return (value,state)
              (= return-left      (oracle-Left-gate-GBLG array-state-left-old length-state-left-old handle l r op j))
              (= return-right     (oracle-Right-simgate-GBLG array-state-right-old length-state-right-old handle l r op j))

              ;assignment of return values
              (= value-left       (return-Left-gate-GBLG-value return-left))
              (= value-right      (return-Right-simgate-GBLG-value return-right))

              ;assignment of abort values
              (= is-abort-left    (= mk-abort-Left-gate-GBLG return-left))
              (= is-abort-right   (= mk-abort-Right-simgate-GBLG return-right))

              ;assignment of return state
              (= array-state-left-new   (return-Left-gate-GBLG-state return-left))
              (= array-state-right-new  (return-Right-simgate-GBLG-state return-right))

              ;assignment of return length
              (= length-state-left-new   (return-Left-gate-GBLG-state-length return-left))
              (= length-state-right-new  (return-Right-simgate-GBLG-state-length return-right))

              ;initial state list contains only one state
              (= length-state-left-old 1)
              (= length-state-right-old 1)
)
)