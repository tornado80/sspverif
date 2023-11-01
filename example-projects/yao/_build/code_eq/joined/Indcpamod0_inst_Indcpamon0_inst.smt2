(set-logic ALL)
(declare-sort Bits_m 0)
(declare-sort Bits_p 0)
(declare-sort Bits_n 0)
(declare-datatypes ((Maybe 1)
)
 ((par (T)
 ((mk-some (maybe-get T)
)
 (mk-none)
)
)
)
)
(declare-datatypes ((ReturnValue 1)
)
 ((par (T)
 ((mk-return-value (return-value T)
)
 (mk-abort)
)
)
)
)
(declare-datatypes ((Tuple1 1)
)
 ((par (T1)
 ((mk-tuple1 (el1 T1)
)
)
)
)
)
(declare-datatypes ((Tuple2 2)
)
 ((par (T1 T2)
 ((mk-tuple2 (el1 T1)
 (el2 T2)
)
)
)
)
)
(declare-datatypes ((Tuple3 3)
)
 ((par (T1 T2 T3)
 ((mk-tuple3 (el1 T1)
 (el2 T2)
 (el3 T3)
)
)
)
)
)
(declare-datatypes ((Tuple4 4)
)
 ((par (T1 T2 T3 T4)
 ((mk-tuple4 (el1 T1)
 (el2 T2)
 (el3 T3)
 (el4 T4)
)
)
)
)
)
(declare-datatypes ((Tuple5 5)
)
 ((par (T1 T2 T3 T4 T5)
 ((mk-tuple5 (el1 T1)
 (el2 T2)
 (el3 T3)
 (el4 T4)
 (el5 T5)
)
)
)
)
)
(declare-datatypes ((Tuple6 6)
)
 ((par (T1 T2 T3 T4 T5 T6)
 ((mk-tuple6 (el1 T1)
 (el2 T2)
 (el3 T3)
 (el4 T4)
 (el5 T5)
 (el6 T6)
)
)
)
)
)
(declare-datatypes ((Tuple7 7)
)
 ((par (T1 T2 T3 T4 T5 T6 T7)
 ((mk-tuple7 (el1 T1)
 (el2 T2)
 (el3 T3)
 (el4 T4)
 (el5 T5)
 (el6 T6)
 (el7 T7)
)
)
)
)
)
(declare-datatypes ((Tuple8 8)
)
 ((par (T1 T2 T3 T4 T5 T6 T7 T8)
 ((mk-tuple8 (el1 T1)
 (el2 T2)
 (el3 T3)
 (el4 T4)
 (el5 T5)
 (el6 T6)
 (el7 T7)
 (el8 T8)
)
)
)
)
)
(declare-datatypes ((Tuple9 9)
)
 ((par (T1 T2 T3 T4 T5 T6 T7 T8 T9)
 ((mk-tuple9 (el1 T1)
 (el2 T2)
 (el3 T3)
 (el4 T4)
 (el5 T5)
 (el6 T6)
 (el7 T7)
 (el8 T8)
 (el9 T9)
)
)
)
)
)
(declare-datatypes ((Tuple10 10)
)
 ((par (T1 T2 T3 T4 T5 T6 T7 T8 T9 T10)
 ((mk-tuple10 (el1 T1)
 (el2 T2)
 (el3 T3)
 (el4 T4)
 (el5 T5)
 (el6 T6)
 (el7 T7)
 (el8 T8)
 (el9 T9)
 (el10 T10)
)
)
)
)
)
(declare-datatypes ((Tuple11 11)
)
 ((par (T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11)
 ((mk-tuple11 (el1 T1)
 (el2 T2)
 (el3 T3)
 (el4 T4)
 (el5 T5)
 (el6 T6)
 (el7 T7)
 (el8 T8)
 (el9 T9)
 (el10 T10)
 (el11 T11)
)
)
)
)
)
(declare-datatypes ((Tuple12 12)
)
 ((par (T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12)
 ((mk-tuple12 (el1 T1)
 (el2 T2)
 (el3 T3)
 (el4 T4)
 (el5 T5)
 (el6 T6)
 (el7 T7)
 (el8 T8)
 (el9 T9)
 (el10 T10)
 (el11 T11)
 (el12 T12)
)
)
)
)
)
(declare-datatypes ((Tuple13 13)
)
 ((par (T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13)
 ((mk-tuple13 (el1 T1)
 (el2 T2)
 (el3 T3)
 (el4 T4)
 (el5 T5)
 (el6 T6)
 (el7 T7)
 (el8 T8)
 (el9 T9)
 (el10 T10)
 (el11 T11)
 (el12 T12)
 (el13 T13)
)
)
)
)
)
(declare-datatypes ((Tuple14 14)
)
 ((par (T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14)
 ((mk-tuple14 (el1 T1)
 (el2 T2)
 (el3 T3)
 (el4 T4)
 (el5 T5)
 (el6 T6)
 (el7 T7)
 (el8 T8)
 (el9 T9)
 (el10 T10)
 (el11 T11)
 (el12 T12)
 (el13 T13)
 (el14 T14)
)
)
)
)
)
(declare-datatypes ((Tuple15 15)
)
 ((par (T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15)
 ((mk-tuple15 (el1 T1)
 (el2 T2)
 (el3 T3)
 (el4 T4)
 (el5 T5)
 (el6 T6)
 (el7 T7)
 (el8 T8)
 (el9 T9)
 (el10 T10)
 (el11 T11)
 (el12 T12)
 (el13 T13)
 (el14 T14)
 (el15 T15)
)
)
)
)
)
(declare-datatypes ((Tuple16 16)
)
 ((par (T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16)
 ((mk-tuple16 (el1 T1)
 (el2 T2)
 (el3 T3)
 (el4 T4)
 (el5 T5)
 (el6 T6)
 (el7 T7)
 (el8 T8)
 (el9 T9)
 (el10 T10)
 (el11 T11)
 (el12 T12)
 (el13 T13)
 (el14 T14)
 (el15 T15)
 (el16 T16)
)
)
)
)
)
(declare-datatypes ((Tuple17 17)
)
 ((par (T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17)
 ((mk-tuple17 (el1 T1)
 (el2 T2)
 (el3 T3)
 (el4 T4)
 (el5 T5)
 (el6 T6)
 (el7 T7)
 (el8 T8)
 (el9 T9)
 (el10 T10)
 (el11 T11)
 (el12 T12)
 (el13 T13)
 (el14 T14)
 (el15 T15)
 (el16 T16)
 (el17 T17)
)
)
)
)
)
(declare-datatypes ((Tuple18 18)
)
 ((par (T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18)
 ((mk-tuple18 (el1 T1)
 (el2 T2)
 (el3 T3)
 (el4 T4)
 (el5 T5)
 (el6 T6)
 (el7 T7)
 (el8 T8)
 (el9 T9)
 (el10 T10)
 (el11 T11)
 (el12 T12)
 (el13 T13)
 (el14 T14)
 (el15 T15)
 (el16 T16)
 (el17 T17)
 (el18 T18)
)
)
)
)
)
(declare-datatypes ((Tuple19 19)
)
 ((par (T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19)
 ((mk-tuple19 (el1 T1)
 (el2 T2)
 (el3 T3)
 (el4 T4)
 (el5 T5)
 (el6 T6)
 (el7 T7)
 (el8 T8)
 (el9 T9)
 (el10 T10)
 (el11 T11)
 (el12 T12)
 (el13 T13)
 (el14 T14)
 (el15 T15)
 (el16 T16)
 (el17 T17)
 (el18 T18)
 (el19 T19)
)
)
)
)
)
(declare-datatypes ((Tuple20 20)
)
 ((par (T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20)
 ((mk-tuple20 (el1 T1)
 (el2 T2)
 (el3 T3)
 (el4 T4)
 (el5 T5)
 (el6 T6)
 (el7 T7)
 (el8 T8)
 (el9 T9)
 (el10 T10)
 (el11 T11)
 (el12 T12)
 (el13 T13)
 (el14 T14)
 (el15 T15)
 (el16 T16)
 (el17 T17)
 (el18 T18)
 (el19 T19)
 (el20 T20)
)
)
)
)
)
(declare-datatypes ((Tuple21 21)
)
 ((par (T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21)
 ((mk-tuple21 (el1 T1)
 (el2 T2)
 (el3 T3)
 (el4 T4)
 (el5 T5)
 (el6 T6)
 (el7 T7)
 (el8 T8)
 (el9 T9)
 (el10 T10)
 (el11 T11)
 (el12 T12)
 (el13 T13)
 (el14 T14)
 (el15 T15)
 (el16 T16)
 (el17 T17)
 (el18 T18)
 (el19 T19)
 (el20 T20)
 (el21 T21)
)
)
)
)
)
(declare-datatypes ((Tuple22 22)
)
 ((par (T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22)
 ((mk-tuple22 (el1 T1)
 (el2 T2)
 (el3 T3)
 (el4 T4)
 (el5 T5)
 (el6 T6)
 (el7 T7)
 (el8 T8)
 (el9 T9)
 (el10 T10)
 (el11 T11)
 (el12 T12)
 (el13 T13)
 (el14 T14)
 (el15 T15)
 (el16 T16)
 (el17 T17)
 (el18 T18)
 (el19 T19)
 (el20 T20)
 (el21 T21)
 (el22 T22)
)
)
)
)
)
(declare-datatypes ((Tuple23 23)
)
 ((par (T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23)
 ((mk-tuple23 (el1 T1)
 (el2 T2)
 (el3 T3)
 (el4 T4)
 (el5 T5)
 (el6 T6)
 (el7 T7)
 (el8 T8)
 (el9 T9)
 (el10 T10)
 (el11 T11)
 (el12 T12)
 (el13 T13)
 (el14 T14)
 (el15 T15)
 (el16 T16)
 (el17 T17)
 (el18 T18)
 (el19 T19)
 (el20 T20)
 (el21 T21)
 (el22 T22)
 (el23 T23)
)
)
)
)
)
(declare-datatypes ((Tuple24 24)
)
 ((par (T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24)
 ((mk-tuple24 (el1 T1)
 (el2 T2)
 (el3 T3)
 (el4 T4)
 (el5 T5)
 (el6 T6)
 (el7 T7)
 (el8 T8)
 (el9 T9)
 (el10 T10)
 (el11 T11)
 (el12 T12)
 (el13 T13)
 (el14 T14)
 (el15 T15)
 (el16 T16)
 (el17 T17)
 (el18 T18)
 (el19 T19)
 (el20 T20)
 (el21 T21)
 (el22 T22)
 (el23 T23)
 (el24 T24)
)
)
)
)
)
(declare-datatypes ((Tuple25 25)
)
 ((par (T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25)
 ((mk-tuple25 (el1 T1)
 (el2 T2)
 (el3 T3)
 (el4 T4)
 (el5 T5)
 (el6 T6)
 (el7 T7)
 (el8 T8)
 (el9 T9)
 (el10 T10)
 (el11 T11)
 (el12 T12)
 (el13 T13)
 (el14 T14)
 (el15 T15)
 (el16 T16)
 (el17 T17)
 (el18 T18)
 (el19 T19)
 (el20 T20)
 (el21 T21)
 (el22 T22)
 (el23 T23)
 (el24 T24)
 (el25 T25)
)
)
)
)
)
(declare-datatypes ((Tuple26 26)
)
 ((par (T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26)
 ((mk-tuple26 (el1 T1)
 (el2 T2)
 (el3 T3)
 (el4 T4)
 (el5 T5)
 (el6 T6)
 (el7 T7)
 (el8 T8)
 (el9 T9)
 (el10 T10)
 (el11 T11)
 (el12 T12)
 (el13 T13)
 (el14 T14)
 (el15 T15)
 (el16 T16)
 (el17 T17)
 (el18 T18)
 (el19 T19)
 (el20 T20)
 (el21 T21)
 (el22 T22)
 (el23 T23)
 (el24 T24)
 (el25 T25)
 (el26 T26)
)
)
)
)
)
(declare-datatypes ((Tuple27 27)
)
 ((par (T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27)
 ((mk-tuple27 (el1 T1)
 (el2 T2)
 (el3 T3)
 (el4 T4)
 (el5 T5)
 (el6 T6)
 (el7 T7)
 (el8 T8)
 (el9 T9)
 (el10 T10)
 (el11 T11)
 (el12 T12)
 (el13 T13)
 (el14 T14)
 (el15 T15)
 (el16 T16)
 (el17 T17)
 (el18 T18)
 (el19 T19)
 (el20 T20)
 (el21 T21)
 (el22 T22)
 (el23 T23)
 (el24 T24)
 (el25 T25)
 (el26 T26)
 (el27 T27)
)
)
)
)
)
(declare-datatypes ((Tuple28 28)
)
 ((par (T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28)
 ((mk-tuple28 (el1 T1)
 (el2 T2)
 (el3 T3)
 (el4 T4)
 (el5 T5)
 (el6 T6)
 (el7 T7)
 (el8 T8)
 (el9 T9)
 (el10 T10)
 (el11 T11)
 (el12 T12)
 (el13 T13)
 (el14 T14)
 (el15 T15)
 (el16 T16)
 (el17 T17)
 (el18 T18)
 (el19 T19)
 (el20 T20)
 (el21 T21)
 (el22 T22)
 (el23 T23)
 (el24 T24)
 (el25 T25)
 (el26 T26)
 (el27 T27)
 (el28 T28)
)
)
)
)
)
(declare-datatypes ((Tuple29 29)
)
 ((par (T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29)
 ((mk-tuple29 (el1 T1)
 (el2 T2)
 (el3 T3)
 (el4 T4)
 (el5 T5)
 (el6 T6)
 (el7 T7)
 (el8 T8)
 (el9 T9)
 (el10 T10)
 (el11 T11)
 (el12 T12)
 (el13 T13)
 (el14 T14)
 (el15 T15)
 (el16 T16)
 (el17 T17)
 (el18 T18)
 (el19 T19)
 (el20 T20)
 (el21 T21)
 (el22 T22)
 (el23 T23)
 (el24 T24)
 (el25 T25)
 (el26 T26)
 (el27 T27)
 (el28 T28)
 (el29 T29)
)
)
)
)
)
(declare-datatypes ((Tuple30 30)
)
 ((par (T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30)
 ((mk-tuple30 (el1 T1)
 (el2 T2)
 (el3 T3)
 (el4 T4)
 (el5 T5)
 (el6 T6)
 (el7 T7)
 (el8 T8)
 (el9 T9)
 (el10 T10)
 (el11 T11)
 (el12 T12)
 (el13 T13)
 (el14 T14)
 (el15 T15)
 (el16 T16)
 (el17 T17)
 (el18 T18)
 (el19 T19)
 (el20 T20)
 (el21 T21)
 (el22 T22)
 (el23 T23)
 (el24 T24)
 (el25 T25)
 (el26 T26)
 (el27 T27)
 (el28 T28)
 (el29 T29)
 (el30 T30)
)
)
)
)
)
(declare-datatypes ((Tuple31 31)
)
 ((par (T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31)
 ((mk-tuple31 (el1 T1)
 (el2 T2)
 (el3 T3)
 (el4 T4)
 (el5 T5)
 (el6 T6)
 (el7 T7)
 (el8 T8)
 (el9 T9)
 (el10 T10)
 (el11 T11)
 (el12 T12)
 (el13 T13)
 (el14 T14)
 (el15 T15)
 (el16 T16)
 (el17 T17)
 (el18 T18)
 (el19 T19)
 (el20 T20)
 (el21 T21)
 (el22 T22)
 (el23 T23)
 (el24 T24)
 (el25 T25)
 (el26 T26)
 (el27 T27)
 (el28 T28)
 (el29 T29)
 (el30 T30)
 (el31 T31)
)
)
)
)
)
(declare-datatype Empty ((mk-empty)
)
)
(declare-fun __sample-rand-Indcpamod0-Bits_n (Int Int)
 Bits_n)
(declare-fun __func-Indcpamod0-encm (Bits_n Bits_m Bits_n)
 Bits_p)
(declare-fun __func-Indcpamod0-encn (Bits_n Bits_n Bits_n)
 Bits_m)
(declare-datatype State_Indcpamod0_keys_top ((mk-state-Indcpamod0-keys_top (state-Indcpamod0-keys_top-T (Maybe (Array Bool (Maybe Bits_n)
)
)
)
 (state-Indcpamod0-keys_top-z (Maybe Bool)
)
 (state-Indcpamod0-keys_top-flag (Maybe Bool)
)
)
)
)
(declare-datatype State_Indcpamod0_enc ((mk-state-Indcpamod0-enc)
)
)
(declare-datatype CompositionState-Indcpamod0 ((mk-composition-state-Indcpamod0 (composition-pkgstate-Indcpamod0-keys_top State_Indcpamod0_keys_top)
 (composition-pkgstate-Indcpamod0-enc State_Indcpamod0_enc)
 (composition-param-Indcpamod0-m Int)
 (composition-param-Indcpamod0-n Int)
 (composition-param-Indcpamod0-p Int)
 (composition-param-Indcpamod0-zerom Bits_m)
 (composition-param-Indcpamod0-zeron Bits_n)
 (composition-rand-Indcpamod0-0 Int)
 (composition-rand-Indcpamod0-1 Int)
 (composition-rand-Indcpamod0-2 Int)
 (composition-rand-Indcpamod0-3 Int)
 (composition-rand-Indcpamod0-4 Int)
 (composition-rand-Indcpamod0-5 Int)
 (composition-rand-Indcpamod0-6 Int)
)
)
)
(declare-datatype Return-Indcpamod0-keys_top-GETKEYSIN ((mk-return-Indcpamod0-keys_top-GETKEYSIN (return-Indcpamod0-keys_top-GETKEYSIN-game-state CompositionState-Indcpamod0)
 (return-Indcpamod0-keys_top-GETKEYSIN-return-value-or-abort (ReturnValue (Array Bool (Maybe Bits_n)
)
)
)
)
)
)
(declare-datatype Return-Indcpamod0-keys_top-GETAIN ((mk-return-Indcpamod0-keys_top-GETAIN (return-Indcpamod0-keys_top-GETAIN-game-state CompositionState-Indcpamod0)
 (return-Indcpamod0-keys_top-GETAIN-return-value-or-abort (ReturnValue Bits_n)
)
)
)
)
(declare-datatype Return-Indcpamod0-keys_top-GETINAIN ((mk-return-Indcpamod0-keys_top-GETINAIN (return-Indcpamod0-keys_top-GETINAIN-game-state CompositionState-Indcpamod0)
 (return-Indcpamod0-keys_top-GETINAIN-return-value-or-abort (ReturnValue Bits_n)
)
)
)
)
(declare-datatype Return-Indcpamod0-keys_top-GETAOUT ((mk-return-Indcpamod0-keys_top-GETAOUT (return-Indcpamod0-keys_top-GETAOUT-game-state CompositionState-Indcpamod0)
 (return-Indcpamod0-keys_top-GETAOUT-return-value-or-abort (ReturnValue Bits_n)
)
)
)
)
(declare-datatype Return-Indcpamod0-keys_top-GETKEYSOUT ((mk-return-Indcpamod0-keys_top-GETKEYSOUT (return-Indcpamod0-keys_top-GETKEYSOUT-game-state CompositionState-Indcpamod0)
 (return-Indcpamod0-keys_top-GETKEYSOUT-return-value-or-abort (ReturnValue (Array Bool (Maybe Bits_n)
)
)
)
)
)
)
(declare-datatype Return-Indcpamod0-keys_top-GETBIT ((mk-return-Indcpamod0-keys_top-GETBIT (return-Indcpamod0-keys_top-GETBIT-game-state CompositionState-Indcpamod0)
 (return-Indcpamod0-keys_top-GETBIT-return-value-or-abort (ReturnValue Bool)
)
)
)
)
(declare-datatype Return-Indcpamod0-keys_top-SETBIT ((mk-return-Indcpamod0-keys_top-SETBIT (return-Indcpamod0-keys_top-SETBIT-game-state CompositionState-Indcpamod0)
 (return-Indcpamod0-keys_top-SETBIT-return-value-or-abort (ReturnValue Empty)
)
)
)
)
(declare-datatype Return-Indcpamod0-enc-ENCN ((mk-return-Indcpamod0-enc-ENCN (return-Indcpamod0-enc-ENCN-game-state CompositionState-Indcpamod0)
 (return-Indcpamod0-enc-ENCN-return-value-or-abort (ReturnValue Bits_m)
)
)
)
)
(declare-datatype Return-Indcpamod0-enc-ENCM ((mk-return-Indcpamod0-enc-ENCM (return-Indcpamod0-enc-ENCM-game-state CompositionState-Indcpamod0)
 (return-Indcpamod0-enc-ENCM-return-value-or-abort (ReturnValue Bits_p)
)
)
)
)
; Composition of Indcpamod0
(define-fun oracle-Indcpamod0-keys_top-GETKEYSIN ((__global_state CompositionState-Indcpamod0)
)
 Return-Indcpamod0-keys_top-GETKEYSIN (let ((__self_state (composition-pkgstate-Indcpamod0-keys_top __global_state)
)
)
 (ite (= (state-Indcpamod0-keys_top-flag __self_state)
 (mk-some true)
)
 (ite (= (state-Indcpamod0-keys_top-T __self_state)
 (as mk-none (Maybe (Array Bool (Maybe Bits_n)
)
)
)
)
 (mk-return-Indcpamod0-keys_top-GETKEYSIN __global_state (as mk-abort (ReturnValue (Array Bool (Maybe Bits_n)
)
)
)
)
 (let ((unwrap-1 (maybe-get (state-Indcpamod0-keys_top-T __self_state)
)
)
)
 (let ((Z unwrap-1)
)
 (let ((__global_state (mk-composition-state-Indcpamod0 __self_state (composition-pkgstate-Indcpamod0-enc __global_state)
 (composition-param-Indcpamod0-m __global_state)
 (composition-param-Indcpamod0-n __global_state)
 (composition-param-Indcpamod0-p __global_state)
 (composition-param-Indcpamod0-zerom __global_state)
 (composition-param-Indcpamod0-zeron __global_state)
 (composition-rand-Indcpamod0-0 __global_state)
 (composition-rand-Indcpamod0-1 __global_state)
 (composition-rand-Indcpamod0-2 __global_state)
 (composition-rand-Indcpamod0-3 __global_state)
 (composition-rand-Indcpamod0-4 __global_state)
 (composition-rand-Indcpamod0-5 __global_state)
 (composition-rand-Indcpamod0-6 __global_state)
)
)
)
 (mk-return-Indcpamod0-keys_top-GETKEYSIN __global_state (mk-return-value Z)
)
)
)
)
)
 (let ((__global_state (mk-composition-state-Indcpamod0 __self_state (composition-pkgstate-Indcpamod0-enc __global_state)
 (composition-param-Indcpamod0-m __global_state)
 (composition-param-Indcpamod0-n __global_state)
 (composition-param-Indcpamod0-p __global_state)
 (composition-param-Indcpamod0-zerom __global_state)
 (composition-param-Indcpamod0-zeron __global_state)
 (composition-rand-Indcpamod0-0 __global_state)
 (composition-rand-Indcpamod0-1 __global_state)
 (composition-rand-Indcpamod0-2 __global_state)
 (composition-rand-Indcpamod0-3 __global_state)
 (composition-rand-Indcpamod0-4 __global_state)
 (composition-rand-Indcpamod0-5 __global_state)
 (composition-rand-Indcpamod0-6 __global_state)
)
)
)
 (mk-return-Indcpamod0-keys_top-GETKEYSIN __global_state (as mk-abort (ReturnValue (Array Bool (Maybe Bits_n)
)
)
)
)
)
)
)
)
(define-fun oracle-Indcpamod0-keys_top-GETAIN ((__global_state CompositionState-Indcpamod0)
)
 Return-Indcpamod0-keys_top-GETAIN (let ((__self_state (composition-pkgstate-Indcpamod0-keys_top __global_state)
)
)
 (ite (= (state-Indcpamod0-keys_top-flag __self_state)
 (mk-some true)
)
 (ite (= (state-Indcpamod0-keys_top-T __self_state)
 (as mk-none (Maybe (Array Bool (Maybe Bits_n)
)
)
)
)
 (mk-return-Indcpamod0-keys_top-GETAIN __global_state (as mk-abort (ReturnValue Bits_n)
)
)
 (let ((unwrap-1 (maybe-get (state-Indcpamod0-keys_top-T __self_state)
)
)
)
 (let ((Z unwrap-1)
)
 (ite (= (state-Indcpamod0-keys_top-z __self_state)
 (as mk-none (Maybe Bool)
)
)
 (mk-return-Indcpamod0-keys_top-GETAIN __global_state (as mk-abort (ReturnValue Bits_n)
)
)
 (let ((unwrap-2 (maybe-get (state-Indcpamod0-keys_top-z __self_state)
)
)
)
 (let ((zz unwrap-2)
)
 (ite (= (select Z zz)
 (as mk-none (Maybe Bits_n)
)
)
 (mk-return-Indcpamod0-keys_top-GETAIN __global_state (as mk-abort (ReturnValue Bits_n)
)
)
 (let ((unwrap-3 (maybe-get (select Z zz)
)
)
)
 (let ((k unwrap-3)
)
 (let ((__global_state (mk-composition-state-Indcpamod0 __self_state (composition-pkgstate-Indcpamod0-enc __global_state)
 (composition-param-Indcpamod0-m __global_state)
 (composition-param-Indcpamod0-n __global_state)
 (composition-param-Indcpamod0-p __global_state)
 (composition-param-Indcpamod0-zerom __global_state)
 (composition-param-Indcpamod0-zeron __global_state)
 (composition-rand-Indcpamod0-0 __global_state)
 (composition-rand-Indcpamod0-1 __global_state)
 (composition-rand-Indcpamod0-2 __global_state)
 (composition-rand-Indcpamod0-3 __global_state)
 (composition-rand-Indcpamod0-4 __global_state)
 (composition-rand-Indcpamod0-5 __global_state)
 (composition-rand-Indcpamod0-6 __global_state)
)
)
)
 (mk-return-Indcpamod0-keys_top-GETAIN __global_state (mk-return-value k)
)
)
)
)
)
)
)
)
)
)
)
 (let ((__global_state (mk-composition-state-Indcpamod0 __self_state (composition-pkgstate-Indcpamod0-enc __global_state)
 (composition-param-Indcpamod0-m __global_state)
 (composition-param-Indcpamod0-n __global_state)
 (composition-param-Indcpamod0-p __global_state)
 (composition-param-Indcpamod0-zerom __global_state)
 (composition-param-Indcpamod0-zeron __global_state)
 (composition-rand-Indcpamod0-0 __global_state)
 (composition-rand-Indcpamod0-1 __global_state)
 (composition-rand-Indcpamod0-2 __global_state)
 (composition-rand-Indcpamod0-3 __global_state)
 (composition-rand-Indcpamod0-4 __global_state)
 (composition-rand-Indcpamod0-5 __global_state)
 (composition-rand-Indcpamod0-6 __global_state)
)
)
)
 (mk-return-Indcpamod0-keys_top-GETAIN __global_state (as mk-abort (ReturnValue Bits_n)
)
)
)
)
)
)
(define-fun oracle-Indcpamod0-keys_top-GETINAIN ((__global_state CompositionState-Indcpamod0)
)
 Return-Indcpamod0-keys_top-GETINAIN (let ((__self_state (composition-pkgstate-Indcpamod0-keys_top __global_state)
)
)
 (ite (= (state-Indcpamod0-keys_top-flag __self_state)
 (mk-some true)
)
 (ite (= (state-Indcpamod0-keys_top-T __self_state)
 (as mk-none (Maybe (Array Bool (Maybe Bits_n)
)
)
)
)
 (mk-return-Indcpamod0-keys_top-GETINAIN __global_state (as mk-abort (ReturnValue Bits_n)
)
)
 (let ((unwrap-1 (maybe-get (state-Indcpamod0-keys_top-T __self_state)
)
)
)
 (let ((Z unwrap-1)
)
 (ite (= (state-Indcpamod0-keys_top-z __self_state)
 (as mk-none (Maybe Bool)
)
)
 (mk-return-Indcpamod0-keys_top-GETINAIN __global_state (as mk-abort (ReturnValue Bits_n)
)
)
 (let ((unwrap-2 (maybe-get (state-Indcpamod0-keys_top-z __self_state)
)
)
)
 (let ((zz unwrap-2)
)
 (ite (= (select Z (not zz)
)
 (as mk-none (Maybe Bits_n)
)
)
 (mk-return-Indcpamod0-keys_top-GETINAIN __global_state (as mk-abort (ReturnValue Bits_n)
)
)
 (let ((unwrap-3 (maybe-get (select Z (not zz)
)
)
)
)
 (let ((k unwrap-3)
)
 (let ((__global_state (mk-composition-state-Indcpamod0 __self_state (composition-pkgstate-Indcpamod0-enc __global_state)
 (composition-param-Indcpamod0-m __global_state)
 (composition-param-Indcpamod0-n __global_state)
 (composition-param-Indcpamod0-p __global_state)
 (composition-param-Indcpamod0-zerom __global_state)
 (composition-param-Indcpamod0-zeron __global_state)
 (composition-rand-Indcpamod0-0 __global_state)
 (composition-rand-Indcpamod0-1 __global_state)
 (composition-rand-Indcpamod0-2 __global_state)
 (composition-rand-Indcpamod0-3 __global_state)
 (composition-rand-Indcpamod0-4 __global_state)
 (composition-rand-Indcpamod0-5 __global_state)
 (composition-rand-Indcpamod0-6 __global_state)
)
)
)
 (mk-return-Indcpamod0-keys_top-GETINAIN __global_state (mk-return-value k)
)
)
)
)
)
)
)
)
)
)
)
 (let ((__global_state (mk-composition-state-Indcpamod0 __self_state (composition-pkgstate-Indcpamod0-enc __global_state)
 (composition-param-Indcpamod0-m __global_state)
 (composition-param-Indcpamod0-n __global_state)
 (composition-param-Indcpamod0-p __global_state)
 (composition-param-Indcpamod0-zerom __global_state)
 (composition-param-Indcpamod0-zeron __global_state)
 (composition-rand-Indcpamod0-0 __global_state)
 (composition-rand-Indcpamod0-1 __global_state)
 (composition-rand-Indcpamod0-2 __global_state)
 (composition-rand-Indcpamod0-3 __global_state)
 (composition-rand-Indcpamod0-4 __global_state)
 (composition-rand-Indcpamod0-5 __global_state)
 (composition-rand-Indcpamod0-6 __global_state)
)
)
)
 (mk-return-Indcpamod0-keys_top-GETINAIN __global_state (as mk-abort (ReturnValue Bits_n)
)
)
)
)
)
)
(define-fun oracle-Indcpamod0-keys_top-GETAOUT ((__global_state CompositionState-Indcpamod0)
)
 Return-Indcpamod0-keys_top-GETAOUT (let ((__self_state (composition-pkgstate-Indcpamod0-keys_top __global_state)
)
)
 (ite (not (= (state-Indcpamod0-keys_top-z __self_state)
 (as mk-none (Maybe Bool)
)
)
)
 (let ((__self_state (mk-state-Indcpamod0-keys_top (state-Indcpamod0-keys_top-T __self_state)
 (state-Indcpamod0-keys_top-z __self_state)
 (mk-some true)
)
)
)
 (let ((Z ((as const (Array Bool (Maybe Bits_n)
)
)
 (as mk-none (Maybe Bits_n)
)
)
)
)
 (ite (= (state-Indcpamod0-keys_top-T __self_state)
 (as mk-none (Maybe (Array Bool (Maybe Bits_n)
)
)
)
)
 (let ((r (__sample-rand-Indcpamod0-Bits_n 1 (composition-rand-Indcpamod0-1 __global_state)
)
)
)
 (let ((__global_state (mk-composition-state-Indcpamod0 (composition-pkgstate-Indcpamod0-keys_top __global_state)
 (composition-pkgstate-Indcpamod0-enc __global_state)
 (composition-param-Indcpamod0-m __global_state)
 (composition-param-Indcpamod0-n __global_state)
 (composition-param-Indcpamod0-p __global_state)
 (composition-param-Indcpamod0-zerom __global_state)
 (composition-param-Indcpamod0-zeron __global_state)
 (composition-rand-Indcpamod0-0 __global_state)
 (+ 1 (composition-rand-Indcpamod0-1 __global_state)
)
 (composition-rand-Indcpamod0-2 __global_state)
 (composition-rand-Indcpamod0-3 __global_state)
 (composition-rand-Indcpamod0-4 __global_state)
 (composition-rand-Indcpamod0-5 __global_state)
 (composition-rand-Indcpamod0-6 __global_state)
)
)
)
 (let ((Z ((as const (Array Bool (Maybe Bits_n)
)
)
 (as mk-none (Maybe Bits_n)
)
)
)
)
 (let ((Z (store Z true (mk-some r)
)
)
)
 (let ((rr (__sample-rand-Indcpamod0-Bits_n 2 (composition-rand-Indcpamod0-2 __global_state)
)
)
)
 (let ((__global_state (mk-composition-state-Indcpamod0 (composition-pkgstate-Indcpamod0-keys_top __global_state)
 (composition-pkgstate-Indcpamod0-enc __global_state)
 (composition-param-Indcpamod0-m __global_state)
 (composition-param-Indcpamod0-n __global_state)
 (composition-param-Indcpamod0-p __global_state)
 (composition-param-Indcpamod0-zerom __global_state)
 (composition-param-Indcpamod0-zeron __global_state)
 (composition-rand-Indcpamod0-0 __global_state)
 (composition-rand-Indcpamod0-1 __global_state)
 (+ 1 (composition-rand-Indcpamod0-2 __global_state)
)
 (composition-rand-Indcpamod0-3 __global_state)
 (composition-rand-Indcpamod0-4 __global_state)
 (composition-rand-Indcpamod0-5 __global_state)
 (composition-rand-Indcpamod0-6 __global_state)
)
)
)
 (let ((Z (store Z false (mk-some rr)
)
)
)
 (let ((__self_state (mk-state-Indcpamod0-keys_top (mk-some Z)
 (state-Indcpamod0-keys_top-z __self_state)
 (state-Indcpamod0-keys_top-flag __self_state)
)
)
)
 (ite (= (state-Indcpamod0-keys_top-T __self_state)
 (as mk-none (Maybe (Array Bool (Maybe Bits_n)
)
)
)
)
 (mk-return-Indcpamod0-keys_top-GETAOUT __global_state (as mk-abort (ReturnValue Bits_n)
)
)
 (let ((unwrap-1 (maybe-get (state-Indcpamod0-keys_top-T __self_state)
)
)
)
 (let ((Z unwrap-1)
)
 (ite (= (state-Indcpamod0-keys_top-z __self_state)
 (as mk-none (Maybe Bool)
)
)
 (mk-return-Indcpamod0-keys_top-GETAOUT __global_state (as mk-abort (ReturnValue Bits_n)
)
)
 (let ((unwrap-2 (maybe-get (state-Indcpamod0-keys_top-z __self_state)
)
)
)
 (let ((zz unwrap-2)
)
 (ite (= (select Z zz)
 (as mk-none (Maybe Bits_n)
)
)
 (mk-return-Indcpamod0-keys_top-GETAOUT __global_state (as mk-abort (ReturnValue Bits_n)
)
)
 (let ((unwrap-3 (maybe-get (select Z zz)
)
)
)
 (let ((k unwrap-3)
)
 (let ((__global_state (mk-composition-state-Indcpamod0 __self_state (composition-pkgstate-Indcpamod0-enc __global_state)
 (composition-param-Indcpamod0-m __global_state)
 (composition-param-Indcpamod0-n __global_state)
 (composition-param-Indcpamod0-p __global_state)
 (composition-param-Indcpamod0-zerom __global_state)
 (composition-param-Indcpamod0-zeron __global_state)
 (composition-rand-Indcpamod0-0 __global_state)
 (composition-rand-Indcpamod0-1 __global_state)
 (composition-rand-Indcpamod0-2 __global_state)
 (composition-rand-Indcpamod0-3 __global_state)
 (composition-rand-Indcpamod0-4 __global_state)
 (composition-rand-Indcpamod0-5 __global_state)
 (composition-rand-Indcpamod0-6 __global_state)
)
)
)
 (mk-return-Indcpamod0-keys_top-GETAOUT __global_state (mk-return-value k)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
 (ite (= (state-Indcpamod0-keys_top-T __self_state)
 (as mk-none (Maybe (Array Bool (Maybe Bits_n)
)
)
)
)
 (mk-return-Indcpamod0-keys_top-GETAOUT __global_state (as mk-abort (ReturnValue Bits_n)
)
)
 (let ((unwrap-1 (maybe-get (state-Indcpamod0-keys_top-T __self_state)
)
)
)
 (let ((Z unwrap-1)
)
 (ite (= (state-Indcpamod0-keys_top-z __self_state)
 (as mk-none (Maybe Bool)
)
)
 (mk-return-Indcpamod0-keys_top-GETAOUT __global_state (as mk-abort (ReturnValue Bits_n)
)
)
 (let ((unwrap-2 (maybe-get (state-Indcpamod0-keys_top-z __self_state)
)
)
)
 (let ((zz unwrap-2)
)
 (ite (= (select Z zz)
 (as mk-none (Maybe Bits_n)
)
)
 (mk-return-Indcpamod0-keys_top-GETAOUT __global_state (as mk-abort (ReturnValue Bits_n)
)
)
 (let ((unwrap-3 (maybe-get (select Z zz)
)
)
)
 (let ((k unwrap-3)
)
 (let ((__global_state (mk-composition-state-Indcpamod0 __self_state (composition-pkgstate-Indcpamod0-enc __global_state)
 (composition-param-Indcpamod0-m __global_state)
 (composition-param-Indcpamod0-n __global_state)
 (composition-param-Indcpamod0-p __global_state)
 (composition-param-Indcpamod0-zerom __global_state)
 (composition-param-Indcpamod0-zeron __global_state)
 (composition-rand-Indcpamod0-0 __global_state)
 (composition-rand-Indcpamod0-1 __global_state)
 (composition-rand-Indcpamod0-2 __global_state)
 (composition-rand-Indcpamod0-3 __global_state)
 (composition-rand-Indcpamod0-4 __global_state)
 (composition-rand-Indcpamod0-5 __global_state)
 (composition-rand-Indcpamod0-6 __global_state)
)
)
)
 (mk-return-Indcpamod0-keys_top-GETAOUT __global_state (mk-return-value k)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
 (let ((__global_state (mk-composition-state-Indcpamod0 __self_state (composition-pkgstate-Indcpamod0-enc __global_state)
 (composition-param-Indcpamod0-m __global_state)
 (composition-param-Indcpamod0-n __global_state)
 (composition-param-Indcpamod0-p __global_state)
 (composition-param-Indcpamod0-zerom __global_state)
 (composition-param-Indcpamod0-zeron __global_state)
 (composition-rand-Indcpamod0-0 __global_state)
 (composition-rand-Indcpamod0-1 __global_state)
 (composition-rand-Indcpamod0-2 __global_state)
 (composition-rand-Indcpamod0-3 __global_state)
 (composition-rand-Indcpamod0-4 __global_state)
 (composition-rand-Indcpamod0-5 __global_state)
 (composition-rand-Indcpamod0-6 __global_state)
)
)
)
 (mk-return-Indcpamod0-keys_top-GETAOUT __global_state (as mk-abort (ReturnValue Bits_n)
)
)
)
)
)
)
(define-fun oracle-Indcpamod0-keys_top-GETKEYSOUT ((__global_state CompositionState-Indcpamod0)
)
 Return-Indcpamod0-keys_top-GETKEYSOUT (let ((__self_state (composition-pkgstate-Indcpamod0-keys_top __global_state)
)
)
 (ite (not (= (state-Indcpamod0-keys_top-flag __self_state)
 (mk-some true)
)
)
 (let ((__self_state (mk-state-Indcpamod0-keys_top (state-Indcpamod0-keys_top-T __self_state)
 (state-Indcpamod0-keys_top-z __self_state)
 (mk-some true)
)
)
)
 (let ((Z ((as const (Array Bool (Maybe Bits_n)
)
)
 (as mk-none (Maybe Bits_n)
)
)
)
)
 (ite (= (state-Indcpamod0-keys_top-T __self_state)
 (as mk-none (Maybe (Array Bool (Maybe Bits_n)
)
)
)
)
 (let ((r (__sample-rand-Indcpamod0-Bits_n 3 (composition-rand-Indcpamod0-3 __global_state)
)
)
)
 (let ((__global_state (mk-composition-state-Indcpamod0 (composition-pkgstate-Indcpamod0-keys_top __global_state)
 (composition-pkgstate-Indcpamod0-enc __global_state)
 (composition-param-Indcpamod0-m __global_state)
 (composition-param-Indcpamod0-n __global_state)
 (composition-param-Indcpamod0-p __global_state)
 (composition-param-Indcpamod0-zerom __global_state)
 (composition-param-Indcpamod0-zeron __global_state)
 (composition-rand-Indcpamod0-0 __global_state)
 (composition-rand-Indcpamod0-1 __global_state)
 (composition-rand-Indcpamod0-2 __global_state)
 (+ 1 (composition-rand-Indcpamod0-3 __global_state)
)
 (composition-rand-Indcpamod0-4 __global_state)
 (composition-rand-Indcpamod0-5 __global_state)
 (composition-rand-Indcpamod0-6 __global_state)
)
)
)
 (let ((Z ((as const (Array Bool (Maybe Bits_n)
)
)
 (as mk-none (Maybe Bits_n)
)
)
)
)
 (let ((Z (store Z true (mk-some r)
)
)
)
 (let ((rr (__sample-rand-Indcpamod0-Bits_n 4 (composition-rand-Indcpamod0-4 __global_state)
)
)
)
 (let ((__global_state (mk-composition-state-Indcpamod0 (composition-pkgstate-Indcpamod0-keys_top __global_state)
 (composition-pkgstate-Indcpamod0-enc __global_state)
 (composition-param-Indcpamod0-m __global_state)
 (composition-param-Indcpamod0-n __global_state)
 (composition-param-Indcpamod0-p __global_state)
 (composition-param-Indcpamod0-zerom __global_state)
 (composition-param-Indcpamod0-zeron __global_state)
 (composition-rand-Indcpamod0-0 __global_state)
 (composition-rand-Indcpamod0-1 __global_state)
 (composition-rand-Indcpamod0-2 __global_state)
 (composition-rand-Indcpamod0-3 __global_state)
 (+ 1 (composition-rand-Indcpamod0-4 __global_state)
)
 (composition-rand-Indcpamod0-5 __global_state)
 (composition-rand-Indcpamod0-6 __global_state)
)
)
)
 (let ((Z (store Z false (mk-some rr)
)
)
)
 (let ((__self_state (mk-state-Indcpamod0-keys_top (mk-some Z)
 (state-Indcpamod0-keys_top-z __self_state)
 (state-Indcpamod0-keys_top-flag __self_state)
)
)
)
 (ite (= (state-Indcpamod0-keys_top-T __self_state)
 (as mk-none (Maybe (Array Bool (Maybe Bits_n)
)
)
)
)
 (mk-return-Indcpamod0-keys_top-GETKEYSOUT __global_state (as mk-abort (ReturnValue (Array Bool (Maybe Bits_n)
)
)
)
)
 (let ((unwrap-1 (maybe-get (state-Indcpamod0-keys_top-T __self_state)
)
)
)
 (let ((Z unwrap-1)
)
 (let ((__global_state (mk-composition-state-Indcpamod0 __self_state (composition-pkgstate-Indcpamod0-enc __global_state)
 (composition-param-Indcpamod0-m __global_state)
 (composition-param-Indcpamod0-n __global_state)
 (composition-param-Indcpamod0-p __global_state)
 (composition-param-Indcpamod0-zerom __global_state)
 (composition-param-Indcpamod0-zeron __global_state)
 (composition-rand-Indcpamod0-0 __global_state)
 (composition-rand-Indcpamod0-1 __global_state)
 (composition-rand-Indcpamod0-2 __global_state)
 (composition-rand-Indcpamod0-3 __global_state)
 (composition-rand-Indcpamod0-4 __global_state)
 (composition-rand-Indcpamod0-5 __global_state)
 (composition-rand-Indcpamod0-6 __global_state)
)
)
)
 (mk-return-Indcpamod0-keys_top-GETKEYSOUT __global_state (mk-return-value Z)
)
)
)
)
)
)
)
)
)
)
)
)
)
 (ite (= (state-Indcpamod0-keys_top-T __self_state)
 (as mk-none (Maybe (Array Bool (Maybe Bits_n)
)
)
)
)
 (mk-return-Indcpamod0-keys_top-GETKEYSOUT __global_state (as mk-abort (ReturnValue (Array Bool (Maybe Bits_n)
)
)
)
)
 (let ((unwrap-1 (maybe-get (state-Indcpamod0-keys_top-T __self_state)
)
)
)
 (let ((Z unwrap-1)
)
 (let ((__global_state (mk-composition-state-Indcpamod0 __self_state (composition-pkgstate-Indcpamod0-enc __global_state)
 (composition-param-Indcpamod0-m __global_state)
 (composition-param-Indcpamod0-n __global_state)
 (composition-param-Indcpamod0-p __global_state)
 (composition-param-Indcpamod0-zerom __global_state)
 (composition-param-Indcpamod0-zeron __global_state)
 (composition-rand-Indcpamod0-0 __global_state)
 (composition-rand-Indcpamod0-1 __global_state)
 (composition-rand-Indcpamod0-2 __global_state)
 (composition-rand-Indcpamod0-3 __global_state)
 (composition-rand-Indcpamod0-4 __global_state)
 (composition-rand-Indcpamod0-5 __global_state)
 (composition-rand-Indcpamod0-6 __global_state)
)
)
)
 (mk-return-Indcpamod0-keys_top-GETKEYSOUT __global_state (mk-return-value Z)
)
)
)
)
)
)
)
)
 (let ((__global_state (mk-composition-state-Indcpamod0 __self_state (composition-pkgstate-Indcpamod0-enc __global_state)
 (composition-param-Indcpamod0-m __global_state)
 (composition-param-Indcpamod0-n __global_state)
 (composition-param-Indcpamod0-p __global_state)
 (composition-param-Indcpamod0-zerom __global_state)
 (composition-param-Indcpamod0-zeron __global_state)
 (composition-rand-Indcpamod0-0 __global_state)
 (composition-rand-Indcpamod0-1 __global_state)
 (composition-rand-Indcpamod0-2 __global_state)
 (composition-rand-Indcpamod0-3 __global_state)
 (composition-rand-Indcpamod0-4 __global_state)
 (composition-rand-Indcpamod0-5 __global_state)
 (composition-rand-Indcpamod0-6 __global_state)
)
)
)
 (mk-return-Indcpamod0-keys_top-GETKEYSOUT __global_state (as mk-abort (ReturnValue (Array Bool (Maybe Bits_n)
)
)
)
)
)
)
)
)
(define-fun oracle-Indcpamod0-keys_top-GETBIT ((__global_state CompositionState-Indcpamod0)
)
 Return-Indcpamod0-keys_top-GETBIT (let ((__self_state (composition-pkgstate-Indcpamod0-keys_top __global_state)
)
)
 (ite (not (= (state-Indcpamod0-keys_top-z __self_state)
 (as mk-none (Maybe Bool)
)
)
)
 (ite (= (state-Indcpamod0-keys_top-z __self_state)
 (as mk-none (Maybe Bool)
)
)
 (mk-return-Indcpamod0-keys_top-GETBIT __global_state (as mk-abort (ReturnValue Bool)
)
)
 (let ((unwrap-1 (maybe-get (state-Indcpamod0-keys_top-z __self_state)
)
)
)
 (let ((zz unwrap-1)
)
 (let ((__global_state (mk-composition-state-Indcpamod0 __self_state (composition-pkgstate-Indcpamod0-enc __global_state)
 (composition-param-Indcpamod0-m __global_state)
 (composition-param-Indcpamod0-n __global_state)
 (composition-param-Indcpamod0-p __global_state)
 (composition-param-Indcpamod0-zerom __global_state)
 (composition-param-Indcpamod0-zeron __global_state)
 (composition-rand-Indcpamod0-0 __global_state)
 (composition-rand-Indcpamod0-1 __global_state)
 (composition-rand-Indcpamod0-2 __global_state)
 (composition-rand-Indcpamod0-3 __global_state)
 (composition-rand-Indcpamod0-4 __global_state)
 (composition-rand-Indcpamod0-5 __global_state)
 (composition-rand-Indcpamod0-6 __global_state)
)
)
)
 (mk-return-Indcpamod0-keys_top-GETBIT __global_state (mk-return-value zz)
)
)
)
)
)
 (let ((__global_state (mk-composition-state-Indcpamod0 __self_state (composition-pkgstate-Indcpamod0-enc __global_state)
 (composition-param-Indcpamod0-m __global_state)
 (composition-param-Indcpamod0-n __global_state)
 (composition-param-Indcpamod0-p __global_state)
 (composition-param-Indcpamod0-zerom __global_state)
 (composition-param-Indcpamod0-zeron __global_state)
 (composition-rand-Indcpamod0-0 __global_state)
 (composition-rand-Indcpamod0-1 __global_state)
 (composition-rand-Indcpamod0-2 __global_state)
 (composition-rand-Indcpamod0-3 __global_state)
 (composition-rand-Indcpamod0-4 __global_state)
 (composition-rand-Indcpamod0-5 __global_state)
 (composition-rand-Indcpamod0-6 __global_state)
)
)
)
 (mk-return-Indcpamod0-keys_top-GETBIT __global_state (as mk-abort (ReturnValue Bool)
)
)
)
)
)
)
(define-fun oracle-Indcpamod0-keys_top-SETBIT ((__global_state CompositionState-Indcpamod0)
 (zz Bool)
)
 Return-Indcpamod0-keys_top-SETBIT (let ((__self_state (composition-pkgstate-Indcpamod0-keys_top __global_state)
)
)
 (ite (= (state-Indcpamod0-keys_top-z __self_state)
 (as mk-none (Maybe Bool)
)
)
 (let ((__self_state (mk-state-Indcpamod0-keys_top (state-Indcpamod0-keys_top-T __self_state)
 (mk-some zz)
 (state-Indcpamod0-keys_top-flag __self_state)
)
)
)
 (let ((__global_state (mk-composition-state-Indcpamod0 __self_state (composition-pkgstate-Indcpamod0-enc __global_state)
 (composition-param-Indcpamod0-m __global_state)
 (composition-param-Indcpamod0-n __global_state)
 (composition-param-Indcpamod0-p __global_state)
 (composition-param-Indcpamod0-zerom __global_state)
 (composition-param-Indcpamod0-zeron __global_state)
 (composition-rand-Indcpamod0-0 __global_state)
 (composition-rand-Indcpamod0-1 __global_state)
 (composition-rand-Indcpamod0-2 __global_state)
 (composition-rand-Indcpamod0-3 __global_state)
 (composition-rand-Indcpamod0-4 __global_state)
 (composition-rand-Indcpamod0-5 __global_state)
 (composition-rand-Indcpamod0-6 __global_state)
)
)
)
 (mk-return-Indcpamod0-keys_top-SETBIT __global_state (mk-return-value mk-empty)
)
)
)
 (let ((__global_state (mk-composition-state-Indcpamod0 __self_state (composition-pkgstate-Indcpamod0-enc __global_state)
 (composition-param-Indcpamod0-m __global_state)
 (composition-param-Indcpamod0-n __global_state)
 (composition-param-Indcpamod0-p __global_state)
 (composition-param-Indcpamod0-zerom __global_state)
 (composition-param-Indcpamod0-zeron __global_state)
 (composition-rand-Indcpamod0-0 __global_state)
 (composition-rand-Indcpamod0-1 __global_state)
 (composition-rand-Indcpamod0-2 __global_state)
 (composition-rand-Indcpamod0-3 __global_state)
 (composition-rand-Indcpamod0-4 __global_state)
 (composition-rand-Indcpamod0-5 __global_state)
 (composition-rand-Indcpamod0-6 __global_state)
)
)
)
 (mk-return-Indcpamod0-keys_top-SETBIT __global_state (as mk-abort (ReturnValue Empty)
)
)
)
)
)
)
(define-fun oracle-Indcpamod0-enc-ENCN ((__global_state CompositionState-Indcpamod0)
 (d Bool)
 (nzero Bits_n)
 (none Bits_n)
)
 Return-Indcpamod0-enc-ENCN (let ((__self_state (composition-pkgstate-Indcpamod0-enc __global_state)
)
)
 (let ((__ret (oracle-Indcpamod0-keys_top-GETKEYSIN __global_state)
)
)
 (ite (= __ret (mk-return-Indcpamod0-keys_top-GETKEYSIN __global_state (as mk-abort (ReturnValue (Array Bool (Maybe Bits_n)
)
)
)
)
)
 (let ((__global_state (return-Indcpamod0-keys_top-GETKEYSIN-game-state __ret)
)
)
 (let ((__global_state (mk-composition-state-Indcpamod0 (composition-pkgstate-Indcpamod0-keys_top __global_state)
 __self_state (composition-param-Indcpamod0-m __global_state)
 (composition-param-Indcpamod0-n __global_state)
 (composition-param-Indcpamod0-p __global_state)
 (composition-param-Indcpamod0-zerom __global_state)
 (composition-param-Indcpamod0-zeron __global_state)
 (composition-rand-Indcpamod0-0 __global_state)
 (composition-rand-Indcpamod0-1 __global_state)
 (composition-rand-Indcpamod0-2 __global_state)
 (composition-rand-Indcpamod0-3 __global_state)
 (composition-rand-Indcpamod0-4 __global_state)
 (composition-rand-Indcpamod0-5 __global_state)
 (composition-rand-Indcpamod0-6 __global_state)
)
)
)
 (mk-return-Indcpamod0-enc-ENCN __global_state (as mk-abort (ReturnValue Bits_m)
)
)
)
)
 (let ((__global_state (return-Indcpamod0-keys_top-GETKEYSIN-game-state __ret)
)
 (K (return-value (return-Indcpamod0-keys_top-GETKEYSIN-return-value-or-abort __ret)
)
)
)
 (let ((r (__sample-rand-Indcpamod0-Bits_n 5 (composition-rand-Indcpamod0-5 __global_state)
)
)
)
 (let ((__global_state (mk-composition-state-Indcpamod0 (composition-pkgstate-Indcpamod0-keys_top __global_state)
 (composition-pkgstate-Indcpamod0-enc __global_state)
 (composition-param-Indcpamod0-m __global_state)
 (composition-param-Indcpamod0-n __global_state)
 (composition-param-Indcpamod0-p __global_state)
 (composition-param-Indcpamod0-zerom __global_state)
 (composition-param-Indcpamod0-zeron __global_state)
 (composition-rand-Indcpamod0-0 __global_state)
 (composition-rand-Indcpamod0-1 __global_state)
 (composition-rand-Indcpamod0-2 __global_state)
 (composition-rand-Indcpamod0-3 __global_state)
 (composition-rand-Indcpamod0-4 __global_state)
 (+ 1 (composition-rand-Indcpamod0-5 __global_state)
)
 (composition-rand-Indcpamod0-6 __global_state)
)
)
)
 (ite (= (select K d)
 (as mk-none (Maybe Bits_n)
)
)
 (mk-return-Indcpamod0-enc-ENCN __global_state (as mk-abort (ReturnValue Bits_m)
)
)
 (let ((unwrap-1 (maybe-get (select K d)
)
)
)
 (let ((c (__func-Indcpamod0-encn unwrap-1 nzero r)
)
)
 (let ((__global_state (mk-composition-state-Indcpamod0 (composition-pkgstate-Indcpamod0-keys_top __global_state)
 __self_state (composition-param-Indcpamod0-m __global_state)
 (composition-param-Indcpamod0-n __global_state)
 (composition-param-Indcpamod0-p __global_state)
 (composition-param-Indcpamod0-zerom __global_state)
 (composition-param-Indcpamod0-zeron __global_state)
 (composition-rand-Indcpamod0-0 __global_state)
 (composition-rand-Indcpamod0-1 __global_state)
 (composition-rand-Indcpamod0-2 __global_state)
 (composition-rand-Indcpamod0-3 __global_state)
 (composition-rand-Indcpamod0-4 __global_state)
 (composition-rand-Indcpamod0-5 __global_state)
 (composition-rand-Indcpamod0-6 __global_state)
)
)
)
 (mk-return-Indcpamod0-enc-ENCN __global_state (mk-return-value c)
)
)
)
)
)
)
)
)
)
)
)
)
(define-fun oracle-Indcpamod0-enc-ENCM ((__global_state CompositionState-Indcpamod0)
 (d Bool)
 (mzero Bits_m)
 (mone Bits_m)
)
 Return-Indcpamod0-enc-ENCM (let ((__self_state (composition-pkgstate-Indcpamod0-enc __global_state)
)
)
 (let ((__ret (oracle-Indcpamod0-keys_top-GETKEYSIN __global_state)
)
)
 (ite (= __ret (mk-return-Indcpamod0-keys_top-GETKEYSIN __global_state (as mk-abort (ReturnValue (Array Bool (Maybe Bits_n)
)
)
)
)
)
 (let ((__global_state (return-Indcpamod0-keys_top-GETKEYSIN-game-state __ret)
)
)
 (let ((__global_state (mk-composition-state-Indcpamod0 (composition-pkgstate-Indcpamod0-keys_top __global_state)
 __self_state (composition-param-Indcpamod0-m __global_state)
 (composition-param-Indcpamod0-n __global_state)
 (composition-param-Indcpamod0-p __global_state)
 (composition-param-Indcpamod0-zerom __global_state)
 (composition-param-Indcpamod0-zeron __global_state)
 (composition-rand-Indcpamod0-0 __global_state)
 (composition-rand-Indcpamod0-1 __global_state)
 (composition-rand-Indcpamod0-2 __global_state)
 (composition-rand-Indcpamod0-3 __global_state)
 (composition-rand-Indcpamod0-4 __global_state)
 (composition-rand-Indcpamod0-5 __global_state)
 (composition-rand-Indcpamod0-6 __global_state)
)
)
)
 (mk-return-Indcpamod0-enc-ENCM __global_state (as mk-abort (ReturnValue Bits_p)
)
)
)
)
 (let ((__global_state (return-Indcpamod0-keys_top-GETKEYSIN-game-state __ret)
)
 (K (return-value (return-Indcpamod0-keys_top-GETKEYSIN-return-value-or-abort __ret)
)
)
)
 (let ((r (__sample-rand-Indcpamod0-Bits_n 6 (composition-rand-Indcpamod0-6 __global_state)
)
)
)
 (let ((__global_state (mk-composition-state-Indcpamod0 (composition-pkgstate-Indcpamod0-keys_top __global_state)
 (composition-pkgstate-Indcpamod0-enc __global_state)
 (composition-param-Indcpamod0-m __global_state)
 (composition-param-Indcpamod0-n __global_state)
 (composition-param-Indcpamod0-p __global_state)
 (composition-param-Indcpamod0-zerom __global_state)
 (composition-param-Indcpamod0-zeron __global_state)
 (composition-rand-Indcpamod0-0 __global_state)
 (composition-rand-Indcpamod0-1 __global_state)
 (composition-rand-Indcpamod0-2 __global_state)
 (composition-rand-Indcpamod0-3 __global_state)
 (composition-rand-Indcpamod0-4 __global_state)
 (composition-rand-Indcpamod0-5 __global_state)
 (+ 1 (composition-rand-Indcpamod0-6 __global_state)
)
)
)
)
 (ite (= (select K d)
 (as mk-none (Maybe Bits_n)
)
)
 (mk-return-Indcpamod0-enc-ENCM __global_state (as mk-abort (ReturnValue Bits_p)
)
)
 (let ((unwrap-1 (maybe-get (select K d)
)
)
)
 (let ((c (__func-Indcpamod0-encm unwrap-1 mzero r)
)
)
 (let ((__global_state (mk-composition-state-Indcpamod0 (composition-pkgstate-Indcpamod0-keys_top __global_state)
 __self_state (composition-param-Indcpamod0-m __global_state)
 (composition-param-Indcpamod0-n __global_state)
 (composition-param-Indcpamod0-p __global_state)
 (composition-param-Indcpamod0-zerom __global_state)
 (composition-param-Indcpamod0-zeron __global_state)
 (composition-rand-Indcpamod0-0 __global_state)
 (composition-rand-Indcpamod0-1 __global_state)
 (composition-rand-Indcpamod0-2 __global_state)
 (composition-rand-Indcpamod0-3 __global_state)
 (composition-rand-Indcpamod0-4 __global_state)
 (composition-rand-Indcpamod0-5 __global_state)
 (composition-rand-Indcpamod0-6 __global_state)
)
)
)
 (mk-return-Indcpamod0-enc-ENCM __global_state (mk-return-value c)
)
)
)
)
)
)
)
)
)
)
)
)
(declare-fun __sample-rand-Indcpamon0-Bits_n (Int Int)
 Bits_n)
(declare-fun __func-Indcpamon0-encm (Bits_n Bits_m Bits_n)
 Bits_p)
(declare-fun __func-Indcpamon0-encn (Bits_n Bits_n Bits_n)
 Bits_m)
(declare-datatype State_Indcpamon0_indcpamon0 ((mk-state-Indcpamon0-indcpamon0 (state-Indcpamon0-indcpamon0-k (Maybe Bits_n)
)
)
)
)
(declare-datatype State_Indcpamon0_red ((mk-state-Indcpamon0-red (state-Indcpamon0-red-k (Maybe Bits_n)
)
 (state-Indcpamon0-red-z (Maybe Bool)
)
 (state-Indcpamon0-red-flag (Maybe Bool)
)
)
)
)
(declare-datatype CompositionState-Indcpamon0 ((mk-composition-state-Indcpamon0 (composition-pkgstate-Indcpamon0-indcpamon0 State_Indcpamon0_indcpamon0)
 (composition-pkgstate-Indcpamon0-red State_Indcpamon0_red)
 (composition-param-Indcpamon0-m Int)
 (composition-param-Indcpamon0-n Int)
 (composition-param-Indcpamon0-p Int)
 (composition-param-Indcpamon0-zerom Bits_m)
 (composition-param-Indcpamon0-zeron Bits_n)
 (composition-rand-Indcpamon0-0 Int)
 (composition-rand-Indcpamon0-1 Int)
 (composition-rand-Indcpamon0-2 Int)
 (composition-rand-Indcpamon0-3 Int)
 (composition-rand-Indcpamon0-4 Int)
 (composition-rand-Indcpamon0-5 Int)
 (composition-rand-Indcpamon0-6 Int)
)
)
)
(declare-datatype Return-Indcpamon0-indcpamon0-SMP ((mk-return-Indcpamon0-indcpamon0-SMP (return-Indcpamon0-indcpamon0-SMP-game-state CompositionState-Indcpamon0)
 (return-Indcpamon0-indcpamon0-SMP-return-value-or-abort (ReturnValue Empty)
)
)
)
)
(declare-datatype Return-Indcpamon0-indcpamon0-ENCN ((mk-return-Indcpamon0-indcpamon0-ENCN (return-Indcpamon0-indcpamon0-ENCN-game-state CompositionState-Indcpamon0)
 (return-Indcpamon0-indcpamon0-ENCN-return-value-or-abort (ReturnValue Bits_m)
)
)
)
)
(declare-datatype Return-Indcpamon0-indcpamon0-ENCM ((mk-return-Indcpamon0-indcpamon0-ENCM (return-Indcpamon0-indcpamon0-ENCM-game-state CompositionState-Indcpamon0)
 (return-Indcpamon0-indcpamon0-ENCM-return-value-or-abort (ReturnValue Bits_p)
)
)
)
)
(declare-datatype Return-Indcpamon0-red-SETBIT ((mk-return-Indcpamon0-red-SETBIT (return-Indcpamon0-red-SETBIT-game-state CompositionState-Indcpamon0)
 (return-Indcpamon0-red-SETBIT-return-value-or-abort (ReturnValue Empty)
)
)
)
)
(declare-datatype Return-Indcpamon0-red-GETAOUT ((mk-return-Indcpamon0-red-GETAOUT (return-Indcpamon0-red-GETAOUT-game-state CompositionState-Indcpamon0)
 (return-Indcpamon0-red-GETAOUT-return-value-or-abort (ReturnValue Bits_n)
)
)
)
)
(declare-datatype Return-Indcpamon0-red-ENCN ((mk-return-Indcpamon0-red-ENCN (return-Indcpamon0-red-ENCN-game-state CompositionState-Indcpamon0)
 (return-Indcpamon0-red-ENCN-return-value-or-abort (ReturnValue Bits_m)
)
)
)
)
(declare-datatype Return-Indcpamon0-red-ENCM ((mk-return-Indcpamon0-red-ENCM (return-Indcpamon0-red-ENCM-game-state CompositionState-Indcpamon0)
 (return-Indcpamon0-red-ENCM-return-value-or-abort (ReturnValue Bits_p)
)
)
)
)
; Composition of Indcpamon0
(define-fun oracle-Indcpamon0-indcpamon0-SMP ((__global_state CompositionState-Indcpamon0)
)
 Return-Indcpamon0-indcpamon0-SMP (let ((__self_state (composition-pkgstate-Indcpamon0-indcpamon0 __global_state)
)
)
 (ite (= (state-Indcpamon0-indcpamon0-k __self_state)
 (as mk-none (Maybe Bits_n)
)
)
 (let ((k_ (__sample-rand-Indcpamon0-Bits_n 1 (composition-rand-Indcpamon0-1 __global_state)
)
)
)
 (let ((__global_state (mk-composition-state-Indcpamon0 (composition-pkgstate-Indcpamon0-indcpamon0 __global_state)
 (composition-pkgstate-Indcpamon0-red __global_state)
 (composition-param-Indcpamon0-m __global_state)
 (composition-param-Indcpamon0-n __global_state)
 (composition-param-Indcpamon0-p __global_state)
 (composition-param-Indcpamon0-zerom __global_state)
 (composition-param-Indcpamon0-zeron __global_state)
 (composition-rand-Indcpamon0-0 __global_state)
 (+ 1 (composition-rand-Indcpamon0-1 __global_state)
)
 (composition-rand-Indcpamon0-2 __global_state)
 (composition-rand-Indcpamon0-3 __global_state)
 (composition-rand-Indcpamon0-4 __global_state)
 (composition-rand-Indcpamon0-5 __global_state)
 (composition-rand-Indcpamon0-6 __global_state)
)
)
)
 (let ((__self_state (mk-state-Indcpamon0-indcpamon0 (mk-some k_)
)
)
)
 (let ((__global_state (mk-composition-state-Indcpamon0 __self_state (composition-pkgstate-Indcpamon0-red __global_state)
 (composition-param-Indcpamon0-m __global_state)
 (composition-param-Indcpamon0-n __global_state)
 (composition-param-Indcpamon0-p __global_state)
 (composition-param-Indcpamon0-zerom __global_state)
 (composition-param-Indcpamon0-zeron __global_state)
 (composition-rand-Indcpamon0-0 __global_state)
 (composition-rand-Indcpamon0-1 __global_state)
 (composition-rand-Indcpamon0-2 __global_state)
 (composition-rand-Indcpamon0-3 __global_state)
 (composition-rand-Indcpamon0-4 __global_state)
 (composition-rand-Indcpamon0-5 __global_state)
 (composition-rand-Indcpamon0-6 __global_state)
)
)
)
 (mk-return-Indcpamon0-indcpamon0-SMP __global_state (mk-return-value mk-empty)
)
)
)
)
)
 (let ((__global_state (mk-composition-state-Indcpamon0 __self_state (composition-pkgstate-Indcpamon0-red __global_state)
 (composition-param-Indcpamon0-m __global_state)
 (composition-param-Indcpamon0-n __global_state)
 (composition-param-Indcpamon0-p __global_state)
 (composition-param-Indcpamon0-zerom __global_state)
 (composition-param-Indcpamon0-zeron __global_state)
 (composition-rand-Indcpamon0-0 __global_state)
 (composition-rand-Indcpamon0-1 __global_state)
 (composition-rand-Indcpamon0-2 __global_state)
 (composition-rand-Indcpamon0-3 __global_state)
 (composition-rand-Indcpamon0-4 __global_state)
 (composition-rand-Indcpamon0-5 __global_state)
 (composition-rand-Indcpamon0-6 __global_state)
)
)
)
 (mk-return-Indcpamon0-indcpamon0-SMP __global_state (as mk-abort (ReturnValue Empty)
)
)
)
)
)
)
(define-fun oracle-Indcpamon0-indcpamon0-ENCN ((__global_state CompositionState-Indcpamon0)
 (nzero Bits_n)
 (none Bits_n)
)
 Return-Indcpamon0-indcpamon0-ENCN (let ((__self_state (composition-pkgstate-Indcpamon0-indcpamon0 __global_state)
)
)
 (ite (not (= (state-Indcpamon0-indcpamon0-k __self_state)
 (as mk-none (Maybe Bits_n)
)
)
)
 (let ((r (__sample-rand-Indcpamon0-Bits_n 2 (composition-rand-Indcpamon0-2 __global_state)
)
)
)
 (let ((__global_state (mk-composition-state-Indcpamon0 (composition-pkgstate-Indcpamon0-indcpamon0 __global_state)
 (composition-pkgstate-Indcpamon0-red __global_state)
 (composition-param-Indcpamon0-m __global_state)
 (composition-param-Indcpamon0-n __global_state)
 (composition-param-Indcpamon0-p __global_state)
 (composition-param-Indcpamon0-zerom __global_state)
 (composition-param-Indcpamon0-zeron __global_state)
 (composition-rand-Indcpamon0-0 __global_state)
 (composition-rand-Indcpamon0-1 __global_state)
 (+ 1 (composition-rand-Indcpamon0-2 __global_state)
)
 (composition-rand-Indcpamon0-3 __global_state)
 (composition-rand-Indcpamon0-4 __global_state)
 (composition-rand-Indcpamon0-5 __global_state)
 (composition-rand-Indcpamon0-6 __global_state)
)
)
)
 (ite (= (state-Indcpamon0-indcpamon0-k __self_state)
 (as mk-none (Maybe Bits_n)
)
)
 (mk-return-Indcpamon0-indcpamon0-ENCN __global_state (as mk-abort (ReturnValue Bits_m)
)
)
 (let ((unwrap-1 (maybe-get (state-Indcpamon0-indcpamon0-k __self_state)
)
)
)
 (let ((c (__func-Indcpamon0-encn unwrap-1 nzero r)
)
)
 (let ((__global_state (mk-composition-state-Indcpamon0 __self_state (composition-pkgstate-Indcpamon0-red __global_state)
 (composition-param-Indcpamon0-m __global_state)
 (composition-param-Indcpamon0-n __global_state)
 (composition-param-Indcpamon0-p __global_state)
 (composition-param-Indcpamon0-zerom __global_state)
 (composition-param-Indcpamon0-zeron __global_state)
 (composition-rand-Indcpamon0-0 __global_state)
 (composition-rand-Indcpamon0-1 __global_state)
 (composition-rand-Indcpamon0-2 __global_state)
 (composition-rand-Indcpamon0-3 __global_state)
 (composition-rand-Indcpamon0-4 __global_state)
 (composition-rand-Indcpamon0-5 __global_state)
 (composition-rand-Indcpamon0-6 __global_state)
)
)
)
 (mk-return-Indcpamon0-indcpamon0-ENCN __global_state (mk-return-value c)
)
)
)
)
)
)
)
 (let ((__global_state (mk-composition-state-Indcpamon0 __self_state (composition-pkgstate-Indcpamon0-red __global_state)
 (composition-param-Indcpamon0-m __global_state)
 (composition-param-Indcpamon0-n __global_state)
 (composition-param-Indcpamon0-p __global_state)
 (composition-param-Indcpamon0-zerom __global_state)
 (composition-param-Indcpamon0-zeron __global_state)
 (composition-rand-Indcpamon0-0 __global_state)
 (composition-rand-Indcpamon0-1 __global_state)
 (composition-rand-Indcpamon0-2 __global_state)
 (composition-rand-Indcpamon0-3 __global_state)
 (composition-rand-Indcpamon0-4 __global_state)
 (composition-rand-Indcpamon0-5 __global_state)
 (composition-rand-Indcpamon0-6 __global_state)
)
)
)
 (mk-return-Indcpamon0-indcpamon0-ENCN __global_state (as mk-abort (ReturnValue Bits_m)
)
)
)
)
)
)
(define-fun oracle-Indcpamon0-indcpamon0-ENCM ((__global_state CompositionState-Indcpamon0)
 (mzero Bits_m)
 (mone Bits_m)
)
 Return-Indcpamon0-indcpamon0-ENCM (let ((__self_state (composition-pkgstate-Indcpamon0-indcpamon0 __global_state)
)
)
 (ite (not (= (state-Indcpamon0-indcpamon0-k __self_state)
 (as mk-none (Maybe Bits_n)
)
)
)
 (let ((r (__sample-rand-Indcpamon0-Bits_n 3 (composition-rand-Indcpamon0-3 __global_state)
)
)
)
 (let ((__global_state (mk-composition-state-Indcpamon0 (composition-pkgstate-Indcpamon0-indcpamon0 __global_state)
 (composition-pkgstate-Indcpamon0-red __global_state)
 (composition-param-Indcpamon0-m __global_state)
 (composition-param-Indcpamon0-n __global_state)
 (composition-param-Indcpamon0-p __global_state)
 (composition-param-Indcpamon0-zerom __global_state)
 (composition-param-Indcpamon0-zeron __global_state)
 (composition-rand-Indcpamon0-0 __global_state)
 (composition-rand-Indcpamon0-1 __global_state)
 (composition-rand-Indcpamon0-2 __global_state)
 (+ 1 (composition-rand-Indcpamon0-3 __global_state)
)
 (composition-rand-Indcpamon0-4 __global_state)
 (composition-rand-Indcpamon0-5 __global_state)
 (composition-rand-Indcpamon0-6 __global_state)
)
)
)
 (ite (= (state-Indcpamon0-indcpamon0-k __self_state)
 (as mk-none (Maybe Bits_n)
)
)
 (mk-return-Indcpamon0-indcpamon0-ENCM __global_state (as mk-abort (ReturnValue Bits_p)
)
)
 (let ((unwrap-1 (maybe-get (state-Indcpamon0-indcpamon0-k __self_state)
)
)
)
 (let ((c (__func-Indcpamon0-encm unwrap-1 mzero r)
)
)
 (let ((__global_state (mk-composition-state-Indcpamon0 __self_state (composition-pkgstate-Indcpamon0-red __global_state)
 (composition-param-Indcpamon0-m __global_state)
 (composition-param-Indcpamon0-n __global_state)
 (composition-param-Indcpamon0-p __global_state)
 (composition-param-Indcpamon0-zerom __global_state)
 (composition-param-Indcpamon0-zeron __global_state)
 (composition-rand-Indcpamon0-0 __global_state)
 (composition-rand-Indcpamon0-1 __global_state)
 (composition-rand-Indcpamon0-2 __global_state)
 (composition-rand-Indcpamon0-3 __global_state)
 (composition-rand-Indcpamon0-4 __global_state)
 (composition-rand-Indcpamon0-5 __global_state)
 (composition-rand-Indcpamon0-6 __global_state)
)
)
)
 (mk-return-Indcpamon0-indcpamon0-ENCM __global_state (mk-return-value c)
)
)
)
)
)
)
)
 (let ((__global_state (mk-composition-state-Indcpamon0 __self_state (composition-pkgstate-Indcpamon0-red __global_state)
 (composition-param-Indcpamon0-m __global_state)
 (composition-param-Indcpamon0-n __global_state)
 (composition-param-Indcpamon0-p __global_state)
 (composition-param-Indcpamon0-zerom __global_state)
 (composition-param-Indcpamon0-zeron __global_state)
 (composition-rand-Indcpamon0-0 __global_state)
 (composition-rand-Indcpamon0-1 __global_state)
 (composition-rand-Indcpamon0-2 __global_state)
 (composition-rand-Indcpamon0-3 __global_state)
 (composition-rand-Indcpamon0-4 __global_state)
 (composition-rand-Indcpamon0-5 __global_state)
 (composition-rand-Indcpamon0-6 __global_state)
)
)
)
 (mk-return-Indcpamon0-indcpamon0-ENCM __global_state (as mk-abort (ReturnValue Bits_p)
)
)
)
)
)
)
(define-fun oracle-Indcpamon0-red-SETBIT ((__global_state CompositionState-Indcpamon0)
 (zz Bool)
)
 Return-Indcpamon0-red-SETBIT (let ((__self_state (composition-pkgstate-Indcpamon0-red __global_state)
)
)
 (ite (= (state-Indcpamon0-red-z __self_state)
 (as mk-none (Maybe Bool)
)
)
 (let ((__self_state (mk-state-Indcpamon0-red (state-Indcpamon0-red-k __self_state)
 (mk-some zz)
 (state-Indcpamon0-red-flag __self_state)
)
)
)
 (let ((__global_state (mk-composition-state-Indcpamon0 (composition-pkgstate-Indcpamon0-indcpamon0 __global_state)
 __self_state (composition-param-Indcpamon0-m __global_state)
 (composition-param-Indcpamon0-n __global_state)
 (composition-param-Indcpamon0-p __global_state)
 (composition-param-Indcpamon0-zerom __global_state)
 (composition-param-Indcpamon0-zeron __global_state)
 (composition-rand-Indcpamon0-0 __global_state)
 (composition-rand-Indcpamon0-1 __global_state)
 (composition-rand-Indcpamon0-2 __global_state)
 (composition-rand-Indcpamon0-3 __global_state)
 (composition-rand-Indcpamon0-4 __global_state)
 (composition-rand-Indcpamon0-5 __global_state)
 (composition-rand-Indcpamon0-6 __global_state)
)
)
)
 (mk-return-Indcpamon0-red-SETBIT __global_state (mk-return-value mk-empty)
)
)
)
 (let ((__global_state (mk-composition-state-Indcpamon0 (composition-pkgstate-Indcpamon0-indcpamon0 __global_state)
 __self_state (composition-param-Indcpamon0-m __global_state)
 (composition-param-Indcpamon0-n __global_state)
 (composition-param-Indcpamon0-p __global_state)
 (composition-param-Indcpamon0-zerom __global_state)
 (composition-param-Indcpamon0-zeron __global_state)
 (composition-rand-Indcpamon0-0 __global_state)
 (composition-rand-Indcpamon0-1 __global_state)
 (composition-rand-Indcpamon0-2 __global_state)
 (composition-rand-Indcpamon0-3 __global_state)
 (composition-rand-Indcpamon0-4 __global_state)
 (composition-rand-Indcpamon0-5 __global_state)
 (composition-rand-Indcpamon0-6 __global_state)
)
)
)
 (mk-return-Indcpamon0-red-SETBIT __global_state (as mk-abort (ReturnValue Empty)
)
)
)
)
)
)
(define-fun oracle-Indcpamon0-red-GETAOUT ((__global_state CompositionState-Indcpamon0)
)
 Return-Indcpamon0-red-GETAOUT (let ((__self_state (composition-pkgstate-Indcpamon0-red __global_state)
)
)
 (ite (not (= (state-Indcpamon0-red-z __self_state)
 (as mk-none (Maybe Bool)
)
)
)
 (let ((__self_state (mk-state-Indcpamon0-red (state-Indcpamon0-red-k __self_state)
 (state-Indcpamon0-red-z __self_state)
 (mk-some true)
)
)
)
 (ite (= (state-Indcpamon0-red-k __self_state)
 (as mk-none (Maybe Bits_n)
)
)
 (let ((k_ (__sample-rand-Indcpamon0-Bits_n 4 (composition-rand-Indcpamon0-4 __global_state)
)
)
)
 (let ((__global_state (mk-composition-state-Indcpamon0 (composition-pkgstate-Indcpamon0-indcpamon0 __global_state)
 (composition-pkgstate-Indcpamon0-red __global_state)
 (composition-param-Indcpamon0-m __global_state)
 (composition-param-Indcpamon0-n __global_state)
 (composition-param-Indcpamon0-p __global_state)
 (composition-param-Indcpamon0-zerom __global_state)
 (composition-param-Indcpamon0-zeron __global_state)
 (composition-rand-Indcpamon0-0 __global_state)
 (composition-rand-Indcpamon0-1 __global_state)
 (composition-rand-Indcpamon0-2 __global_state)
 (composition-rand-Indcpamon0-3 __global_state)
 (+ 1 (composition-rand-Indcpamon0-4 __global_state)
)
 (composition-rand-Indcpamon0-5 __global_state)
 (composition-rand-Indcpamon0-6 __global_state)
)
)
)
 (let ((__self_state (mk-state-Indcpamon0-red (mk-some k_)
 (state-Indcpamon0-red-z __self_state)
 (state-Indcpamon0-red-flag __self_state)
)
)
)
 (let ((__ret (oracle-Indcpamon0-indcpamon0-SMP __global_state)
)
)
 (ite (= __ret (mk-return-Indcpamon0-indcpamon0-SMP __global_state (as mk-abort (ReturnValue Empty)
)
)
)
 (let ((__global_state (return-Indcpamon0-indcpamon0-SMP-game-state __ret)
)
)
 (let ((__global_state (mk-composition-state-Indcpamon0 (composition-pkgstate-Indcpamon0-indcpamon0 __global_state)
 __self_state (composition-param-Indcpamon0-m __global_state)
 (composition-param-Indcpamon0-n __global_state)
 (composition-param-Indcpamon0-p __global_state)
 (composition-param-Indcpamon0-zerom __global_state)
 (composition-param-Indcpamon0-zeron __global_state)
 (composition-rand-Indcpamon0-0 __global_state)
 (composition-rand-Indcpamon0-1 __global_state)
 (composition-rand-Indcpamon0-2 __global_state)
 (composition-rand-Indcpamon0-3 __global_state)
 (composition-rand-Indcpamon0-4 __global_state)
 (composition-rand-Indcpamon0-5 __global_state)
 (composition-rand-Indcpamon0-6 __global_state)
)
)
)
 (mk-return-Indcpamon0-red-GETAOUT __global_state (as mk-abort (ReturnValue Bits_n)
)
)
)
)
 (let ((__global_state (return-Indcpamon0-indcpamon0-SMP-game-state __ret)
)
)
 (ite (= (state-Indcpamon0-red-k __self_state)
 (as mk-none (Maybe Bits_n)
)
)
 (mk-return-Indcpamon0-red-GETAOUT __global_state (as mk-abort (ReturnValue Bits_n)
)
)
 (let ((unwrap-1 (maybe-get (state-Indcpamon0-red-k __self_state)
)
)
)
 (let ((k_ unwrap-1)
)
 (let ((__global_state (mk-composition-state-Indcpamon0 (composition-pkgstate-Indcpamon0-indcpamon0 __global_state)
 __self_state (composition-param-Indcpamon0-m __global_state)
 (composition-param-Indcpamon0-n __global_state)
 (composition-param-Indcpamon0-p __global_state)
 (composition-param-Indcpamon0-zerom __global_state)
 (composition-param-Indcpamon0-zeron __global_state)
 (composition-rand-Indcpamon0-0 __global_state)
 (composition-rand-Indcpamon0-1 __global_state)
 (composition-rand-Indcpamon0-2 __global_state)
 (composition-rand-Indcpamon0-3 __global_state)
 (composition-rand-Indcpamon0-4 __global_state)
 (composition-rand-Indcpamon0-5 __global_state)
 (composition-rand-Indcpamon0-6 __global_state)
)
)
)
 (mk-return-Indcpamon0-red-GETAOUT __global_state (mk-return-value k_)
)
)
)
)
)
)
)
)
)
)
)
 (ite (= (state-Indcpamon0-red-k __self_state)
 (as mk-none (Maybe Bits_n)
)
)
 (mk-return-Indcpamon0-red-GETAOUT __global_state (as mk-abort (ReturnValue Bits_n)
)
)
 (let ((unwrap-1 (maybe-get (state-Indcpamon0-red-k __self_state)
)
)
)
 (let ((k_ unwrap-1)
)
 (let ((__global_state (mk-composition-state-Indcpamon0 (composition-pkgstate-Indcpamon0-indcpamon0 __global_state)
 __self_state (composition-param-Indcpamon0-m __global_state)
 (composition-param-Indcpamon0-n __global_state)
 (composition-param-Indcpamon0-p __global_state)
 (composition-param-Indcpamon0-zerom __global_state)
 (composition-param-Indcpamon0-zeron __global_state)
 (composition-rand-Indcpamon0-0 __global_state)
 (composition-rand-Indcpamon0-1 __global_state)
 (composition-rand-Indcpamon0-2 __global_state)
 (composition-rand-Indcpamon0-3 __global_state)
 (composition-rand-Indcpamon0-4 __global_state)
 (composition-rand-Indcpamon0-5 __global_state)
 (composition-rand-Indcpamon0-6 __global_state)
)
)
)
 (mk-return-Indcpamon0-red-GETAOUT __global_state (mk-return-value k_)
)
)
)
)
)
)
)
 (let ((__global_state (mk-composition-state-Indcpamon0 (composition-pkgstate-Indcpamon0-indcpamon0 __global_state)
 __self_state (composition-param-Indcpamon0-m __global_state)
 (composition-param-Indcpamon0-n __global_state)
 (composition-param-Indcpamon0-p __global_state)
 (composition-param-Indcpamon0-zerom __global_state)
 (composition-param-Indcpamon0-zeron __global_state)
 (composition-rand-Indcpamon0-0 __global_state)
 (composition-rand-Indcpamon0-1 __global_state)
 (composition-rand-Indcpamon0-2 __global_state)
 (composition-rand-Indcpamon0-3 __global_state)
 (composition-rand-Indcpamon0-4 __global_state)
 (composition-rand-Indcpamon0-5 __global_state)
 (composition-rand-Indcpamon0-6 __global_state)
)
)
)
 (mk-return-Indcpamon0-red-GETAOUT __global_state (as mk-abort (ReturnValue Bits_n)
)
)
)
)
)
)
(define-fun oracle-Indcpamon0-red-ENCN ((__global_state CompositionState-Indcpamon0)
 (d Bool)
 (nzero Bits_n)
 (none Bits_n)
)
 Return-Indcpamon0-red-ENCN (let ((__self_state (composition-pkgstate-Indcpamon0-red __global_state)
)
)
 (ite (= (state-Indcpamon0-red-flag __self_state)
 (mk-some true)
)
 (let ((r (__sample-rand-Indcpamon0-Bits_n 5 (composition-rand-Indcpamon0-5 __global_state)
)
)
)
 (let ((__global_state (mk-composition-state-Indcpamon0 (composition-pkgstate-Indcpamon0-indcpamon0 __global_state)
 (composition-pkgstate-Indcpamon0-red __global_state)
 (composition-param-Indcpamon0-m __global_state)
 (composition-param-Indcpamon0-n __global_state)
 (composition-param-Indcpamon0-p __global_state)
 (composition-param-Indcpamon0-zerom __global_state)
 (composition-param-Indcpamon0-zeron __global_state)
 (composition-rand-Indcpamon0-0 __global_state)
 (composition-rand-Indcpamon0-1 __global_state)
 (composition-rand-Indcpamon0-2 __global_state)
 (composition-rand-Indcpamon0-3 __global_state)
 (composition-rand-Indcpamon0-4 __global_state)
 (+ 1 (composition-rand-Indcpamon0-5 __global_state)
)
 (composition-rand-Indcpamon0-6 __global_state)
)
)
)
 (ite (= (state-Indcpamon0-red-k __self_state)
 (as mk-none (Maybe Bits_n)
)
)
 (mk-return-Indcpamon0-red-ENCN __global_state (as mk-abort (ReturnValue Bits_m)
)
)
 (let ((unwrap-1 (maybe-get (state-Indcpamon0-red-k __self_state)
)
)
)
 (let ((c (__func-Indcpamon0-encn unwrap-1 nzero r)
)
)
 (ite (not (= (state-Indcpamon0-red-z __self_state)
 (mk-some d)
)
)
 (let ((__ret (oracle-Indcpamon0-indcpamon0-ENCN __global_state nzero none)
)
)
 (ite (= __ret (mk-return-Indcpamon0-indcpamon0-ENCN __global_state (as mk-abort (ReturnValue Bits_m)
)
)
)
 (let ((__global_state (return-Indcpamon0-indcpamon0-ENCN-game-state __ret)
)
)
 (let ((__global_state (mk-composition-state-Indcpamon0 (composition-pkgstate-Indcpamon0-indcpamon0 __global_state)
 __self_state (composition-param-Indcpamon0-m __global_state)
 (composition-param-Indcpamon0-n __global_state)
 (composition-param-Indcpamon0-p __global_state)
 (composition-param-Indcpamon0-zerom __global_state)
 (composition-param-Indcpamon0-zeron __global_state)
 (composition-rand-Indcpamon0-0 __global_state)
 (composition-rand-Indcpamon0-1 __global_state)
 (composition-rand-Indcpamon0-2 __global_state)
 (composition-rand-Indcpamon0-3 __global_state)
 (composition-rand-Indcpamon0-4 __global_state)
 (composition-rand-Indcpamon0-5 __global_state)
 (composition-rand-Indcpamon0-6 __global_state)
)
)
)
 (mk-return-Indcpamon0-red-ENCN __global_state (as mk-abort (ReturnValue Bits_m)
)
)
)
)
 (let ((__global_state (return-Indcpamon0-indcpamon0-ENCN-game-state __ret)
)
 (c (return-value (return-Indcpamon0-indcpamon0-ENCN-return-value-or-abort __ret)
)
)
)
 (let ((__global_state (mk-composition-state-Indcpamon0 (composition-pkgstate-Indcpamon0-indcpamon0 __global_state)
 __self_state (composition-param-Indcpamon0-m __global_state)
 (composition-param-Indcpamon0-n __global_state)
 (composition-param-Indcpamon0-p __global_state)
 (composition-param-Indcpamon0-zerom __global_state)
 (composition-param-Indcpamon0-zeron __global_state)
 (composition-rand-Indcpamon0-0 __global_state)
 (composition-rand-Indcpamon0-1 __global_state)
 (composition-rand-Indcpamon0-2 __global_state)
 (composition-rand-Indcpamon0-3 __global_state)
 (composition-rand-Indcpamon0-4 __global_state)
 (composition-rand-Indcpamon0-5 __global_state)
 (composition-rand-Indcpamon0-6 __global_state)
)
)
)
 (mk-return-Indcpamon0-red-ENCN __global_state (mk-return-value c)
)
)
)
)
)
 (let ((__global_state (mk-composition-state-Indcpamon0 (composition-pkgstate-Indcpamon0-indcpamon0 __global_state)
 __self_state (composition-param-Indcpamon0-m __global_state)
 (composition-param-Indcpamon0-n __global_state)
 (composition-param-Indcpamon0-p __global_state)
 (composition-param-Indcpamon0-zerom __global_state)
 (composition-param-Indcpamon0-zeron __global_state)
 (composition-rand-Indcpamon0-0 __global_state)
 (composition-rand-Indcpamon0-1 __global_state)
 (composition-rand-Indcpamon0-2 __global_state)
 (composition-rand-Indcpamon0-3 __global_state)
 (composition-rand-Indcpamon0-4 __global_state)
 (composition-rand-Indcpamon0-5 __global_state)
 (composition-rand-Indcpamon0-6 __global_state)
)
)
)
 (mk-return-Indcpamon0-red-ENCN __global_state (mk-return-value c)
)
)
)
)
)
)
)
)
 (let ((__global_state (mk-composition-state-Indcpamon0 (composition-pkgstate-Indcpamon0-indcpamon0 __global_state)
 __self_state (composition-param-Indcpamon0-m __global_state)
 (composition-param-Indcpamon0-n __global_state)
 (composition-param-Indcpamon0-p __global_state)
 (composition-param-Indcpamon0-zerom __global_state)
 (composition-param-Indcpamon0-zeron __global_state)
 (composition-rand-Indcpamon0-0 __global_state)
 (composition-rand-Indcpamon0-1 __global_state)
 (composition-rand-Indcpamon0-2 __global_state)
 (composition-rand-Indcpamon0-3 __global_state)
 (composition-rand-Indcpamon0-4 __global_state)
 (composition-rand-Indcpamon0-5 __global_state)
 (composition-rand-Indcpamon0-6 __global_state)
)
)
)
 (mk-return-Indcpamon0-red-ENCN __global_state (as mk-abort (ReturnValue Bits_m)
)
)
)
)
)
)
(define-fun oracle-Indcpamon0-red-ENCM ((__global_state CompositionState-Indcpamon0)
 (d Bool)
 (mzero Bits_m)
 (mone Bits_m)
)
 Return-Indcpamon0-red-ENCM (let ((__self_state (composition-pkgstate-Indcpamon0-red __global_state)
)
)
 (ite (= (state-Indcpamon0-red-flag __self_state)
 (mk-some true)
)
 (let ((r (__sample-rand-Indcpamon0-Bits_n 6 (composition-rand-Indcpamon0-6 __global_state)
)
)
)
 (let ((__global_state (mk-composition-state-Indcpamon0 (composition-pkgstate-Indcpamon0-indcpamon0 __global_state)
 (composition-pkgstate-Indcpamon0-red __global_state)
 (composition-param-Indcpamon0-m __global_state)
 (composition-param-Indcpamon0-n __global_state)
 (composition-param-Indcpamon0-p __global_state)
 (composition-param-Indcpamon0-zerom __global_state)
 (composition-param-Indcpamon0-zeron __global_state)
 (composition-rand-Indcpamon0-0 __global_state)
 (composition-rand-Indcpamon0-1 __global_state)
 (composition-rand-Indcpamon0-2 __global_state)
 (composition-rand-Indcpamon0-3 __global_state)
 (composition-rand-Indcpamon0-4 __global_state)
 (composition-rand-Indcpamon0-5 __global_state)
 (+ 1 (composition-rand-Indcpamon0-6 __global_state)
)
)
)
)
 (ite (= (state-Indcpamon0-red-k __self_state)
 (as mk-none (Maybe Bits_n)
)
)
 (mk-return-Indcpamon0-red-ENCM __global_state (as mk-abort (ReturnValue Bits_p)
)
)
 (let ((unwrap-1 (maybe-get (state-Indcpamon0-red-k __self_state)
)
)
)
 (let ((c (__func-Indcpamon0-encm unwrap-1 mzero r)
)
)
 (ite (not (= (state-Indcpamon0-red-z __self_state)
 (mk-some d)
)
)
 (let ((__ret (oracle-Indcpamon0-indcpamon0-ENCM __global_state mzero mone)
)
)
 (ite (= __ret (mk-return-Indcpamon0-indcpamon0-ENCM __global_state (as mk-abort (ReturnValue Bits_p)
)
)
)
 (let ((__global_state (return-Indcpamon0-indcpamon0-ENCM-game-state __ret)
)
)
 (let ((__global_state (mk-composition-state-Indcpamon0 (composition-pkgstate-Indcpamon0-indcpamon0 __global_state)
 __self_state (composition-param-Indcpamon0-m __global_state)
 (composition-param-Indcpamon0-n __global_state)
 (composition-param-Indcpamon0-p __global_state)
 (composition-param-Indcpamon0-zerom __global_state)
 (composition-param-Indcpamon0-zeron __global_state)
 (composition-rand-Indcpamon0-0 __global_state)
 (composition-rand-Indcpamon0-1 __global_state)
 (composition-rand-Indcpamon0-2 __global_state)
 (composition-rand-Indcpamon0-3 __global_state)
 (composition-rand-Indcpamon0-4 __global_state)
 (composition-rand-Indcpamon0-5 __global_state)
 (composition-rand-Indcpamon0-6 __global_state)
)
)
)
 (mk-return-Indcpamon0-red-ENCM __global_state (as mk-abort (ReturnValue Bits_p)
)
)
)
)
 (let ((__global_state (return-Indcpamon0-indcpamon0-ENCM-game-state __ret)
)
 (c (return-value (return-Indcpamon0-indcpamon0-ENCM-return-value-or-abort __ret)
)
)
)
 (let ((__global_state (mk-composition-state-Indcpamon0 (composition-pkgstate-Indcpamon0-indcpamon0 __global_state)
 __self_state (composition-param-Indcpamon0-m __global_state)
 (composition-param-Indcpamon0-n __global_state)
 (composition-param-Indcpamon0-p __global_state)
 (composition-param-Indcpamon0-zerom __global_state)
 (composition-param-Indcpamon0-zeron __global_state)
 (composition-rand-Indcpamon0-0 __global_state)
 (composition-rand-Indcpamon0-1 __global_state)
 (composition-rand-Indcpamon0-2 __global_state)
 (composition-rand-Indcpamon0-3 __global_state)
 (composition-rand-Indcpamon0-4 __global_state)
 (composition-rand-Indcpamon0-5 __global_state)
 (composition-rand-Indcpamon0-6 __global_state)
)
)
)
 (mk-return-Indcpamon0-red-ENCM __global_state (mk-return-value c)
)
)
)
)
)
 (let ((__global_state (mk-composition-state-Indcpamon0 (composition-pkgstate-Indcpamon0-indcpamon0 __global_state)
 __self_state (composition-param-Indcpamon0-m __global_state)
 (composition-param-Indcpamon0-n __global_state)
 (composition-param-Indcpamon0-p __global_state)
 (composition-param-Indcpamon0-zerom __global_state)
 (composition-param-Indcpamon0-zeron __global_state)
 (composition-rand-Indcpamon0-0 __global_state)
 (composition-rand-Indcpamon0-1 __global_state)
 (composition-rand-Indcpamon0-2 __global_state)
 (composition-rand-Indcpamon0-3 __global_state)
 (composition-rand-Indcpamon0-4 __global_state)
 (composition-rand-Indcpamon0-5 __global_state)
 (composition-rand-Indcpamon0-6 __global_state)
)
)
)
 (mk-return-Indcpamon0-red-ENCM __global_state (mk-return-value c)
)
)
)
)
)
)
)
)
 (let ((__global_state (mk-composition-state-Indcpamon0 (composition-pkgstate-Indcpamon0-indcpamon0 __global_state)
 __self_state (composition-param-Indcpamon0-m __global_state)
 (composition-param-Indcpamon0-n __global_state)
 (composition-param-Indcpamon0-p __global_state)
 (composition-param-Indcpamon0-zerom __global_state)
 (composition-param-Indcpamon0-zeron __global_state)
 (composition-rand-Indcpamon0-0 __global_state)
 (composition-rand-Indcpamon0-1 __global_state)
 (composition-rand-Indcpamon0-2 __global_state)
 (composition-rand-Indcpamon0-3 __global_state)
 (composition-rand-Indcpamon0-4 __global_state)
 (composition-rand-Indcpamon0-5 __global_state)
 (composition-rand-Indcpamon0-6 __global_state)
)
)
)
 (mk-return-Indcpamon0-red-ENCM __global_state (as mk-abort (ReturnValue Bits_p)
)
)
)
)
)
)
(declare-const game-state-Indcpamod0_inst-old CompositionState-Indcpamod0)
(declare-const game-state-Indcpamon0_inst-old CompositionState-Indcpamon0)
(declare-const arg-SETBIT-zz Bool)
(declare-const arg-ENCN-d Bool)
(declare-const arg-ENCN-nzero Bits_n)
(declare-const arg-ENCN-none Bits_n)
(declare-const arg-ENCM-d Bool)
(declare-const arg-ENCM-mzero Bits_m)
(declare-const arg-ENCM-mone Bits_m)
(declare-const return-Indcpamod0_inst-GETAOUT Return-Indcpamod0-keys_top-GETAOUT)
(assert (= return-Indcpamod0_inst-GETAOUT (oracle-Indcpamod0-keys_top-GETAOUT game-state-Indcpamod0_inst-old)
)
)
(declare-const return-value-Indcpamod0_inst-keys_top-GETAOUT (ReturnValue Bits_n)
)
(assert (= return-value-Indcpamod0_inst-keys_top-GETAOUT (return-Indcpamod0-keys_top-GETAOUT-return-value-or-abort return-Indcpamod0_inst-GETAOUT)
)
)
(declare-const game-state-Indcpamod0_inst-new-GETAOUT CompositionState-Indcpamod0)
(assert (= game-state-Indcpamod0_inst-new-GETAOUT (return-Indcpamod0-keys_top-GETAOUT-game-state return-Indcpamod0_inst-GETAOUT)
)
)
(declare-const return-Indcpamod0_inst-SETBIT Return-Indcpamod0-keys_top-SETBIT)
(assert (= return-Indcpamod0_inst-SETBIT (oracle-Indcpamod0-keys_top-SETBIT game-state-Indcpamod0_inst-old arg-SETBIT-zz)
)
)
(declare-const return-value-Indcpamod0_inst-keys_top-SETBIT (ReturnValue Empty)
)
(assert (= return-value-Indcpamod0_inst-keys_top-SETBIT (return-Indcpamod0-keys_top-SETBIT-return-value-or-abort return-Indcpamod0_inst-SETBIT)
)
)
(declare-const game-state-Indcpamod0_inst-new-SETBIT CompositionState-Indcpamod0)
(assert (= game-state-Indcpamod0_inst-new-SETBIT (return-Indcpamod0-keys_top-SETBIT-game-state return-Indcpamod0_inst-SETBIT)
)
)
(declare-const return-Indcpamod0_inst-ENCN Return-Indcpamod0-enc-ENCN)
(assert (= return-Indcpamod0_inst-ENCN (oracle-Indcpamod0-enc-ENCN game-state-Indcpamod0_inst-old arg-ENCN-d arg-ENCN-nzero arg-ENCN-none)
)
)
(declare-const return-value-Indcpamod0_inst-enc-ENCN (ReturnValue Bits_m)
)
(assert (= return-value-Indcpamod0_inst-enc-ENCN (return-Indcpamod0-enc-ENCN-return-value-or-abort return-Indcpamod0_inst-ENCN)
)
)
(declare-const game-state-Indcpamod0_inst-new-ENCN CompositionState-Indcpamod0)
(assert (= game-state-Indcpamod0_inst-new-ENCN (return-Indcpamod0-enc-ENCN-game-state return-Indcpamod0_inst-ENCN)
)
)
(declare-const return-Indcpamod0_inst-ENCM Return-Indcpamod0-enc-ENCM)
(assert (= return-Indcpamod0_inst-ENCM (oracle-Indcpamod0-enc-ENCM game-state-Indcpamod0_inst-old arg-ENCM-d arg-ENCM-mzero arg-ENCM-mone)
)
)
(declare-const return-value-Indcpamod0_inst-enc-ENCM (ReturnValue Bits_p)
)
(assert (= return-value-Indcpamod0_inst-enc-ENCM (return-Indcpamod0-enc-ENCM-return-value-or-abort return-Indcpamod0_inst-ENCM)
)
)
(declare-const game-state-Indcpamod0_inst-new-ENCM CompositionState-Indcpamod0)
(assert (= game-state-Indcpamod0_inst-new-ENCM (return-Indcpamod0-enc-ENCM-game-state return-Indcpamod0_inst-ENCM)
)
)
(declare-const return-Indcpamon0_inst-GETAOUT Return-Indcpamon0-red-GETAOUT)
(assert (= return-Indcpamon0_inst-GETAOUT (oracle-Indcpamon0-red-GETAOUT game-state-Indcpamon0_inst-old)
)
)
(declare-const return-value-Indcpamon0_inst-red-GETAOUT (ReturnValue Bits_n)
)
(assert (= return-value-Indcpamon0_inst-red-GETAOUT (return-Indcpamon0-red-GETAOUT-return-value-or-abort return-Indcpamon0_inst-GETAOUT)
)
)
(declare-const game-state-Indcpamon0_inst-new-GETAOUT CompositionState-Indcpamon0)
(assert (= game-state-Indcpamon0_inst-new-GETAOUT (return-Indcpamon0-red-GETAOUT-game-state return-Indcpamon0_inst-GETAOUT)
)
)
(declare-const return-Indcpamon0_inst-SETBIT Return-Indcpamon0-red-SETBIT)
(assert (= return-Indcpamon0_inst-SETBIT (oracle-Indcpamon0-red-SETBIT game-state-Indcpamon0_inst-old arg-SETBIT-zz)
)
)
(declare-const return-value-Indcpamon0_inst-red-SETBIT (ReturnValue Empty)
)
(assert (= return-value-Indcpamon0_inst-red-SETBIT (return-Indcpamon0-red-SETBIT-return-value-or-abort return-Indcpamon0_inst-SETBIT)
)
)
(declare-const game-state-Indcpamon0_inst-new-SETBIT CompositionState-Indcpamon0)
(assert (= game-state-Indcpamon0_inst-new-SETBIT (return-Indcpamon0-red-SETBIT-game-state return-Indcpamon0_inst-SETBIT)
)
)
(declare-const return-Indcpamon0_inst-ENCN Return-Indcpamon0-red-ENCN)
(assert (= return-Indcpamon0_inst-ENCN (oracle-Indcpamon0-red-ENCN game-state-Indcpamon0_inst-old arg-ENCN-d arg-ENCN-nzero arg-ENCN-none)
)
)
(declare-const return-value-Indcpamon0_inst-red-ENCN (ReturnValue Bits_m)
)
(assert (= return-value-Indcpamon0_inst-red-ENCN (return-Indcpamon0-red-ENCN-return-value-or-abort return-Indcpamon0_inst-ENCN)
)
)
(declare-const game-state-Indcpamon0_inst-new-ENCN CompositionState-Indcpamon0)
(assert (= game-state-Indcpamon0_inst-new-ENCN (return-Indcpamon0-red-ENCN-game-state return-Indcpamon0_inst-ENCN)
)
)
(declare-const return-Indcpamon0_inst-ENCM Return-Indcpamon0-red-ENCM)
(assert (= return-Indcpamon0_inst-ENCM (oracle-Indcpamon0-red-ENCM game-state-Indcpamon0_inst-old arg-ENCM-d arg-ENCM-mzero arg-ENCM-mone)
)
)
(declare-const return-value-Indcpamon0_inst-red-ENCM (ReturnValue Bits_p)
)
(assert (= return-value-Indcpamon0_inst-red-ENCM (return-Indcpamon0-red-ENCM-return-value-or-abort return-Indcpamon0_inst-ENCM)
)
)
(declare-const game-state-Indcpamon0_inst-new-ENCM CompositionState-Indcpamon0)
(assert (= game-state-Indcpamon0_inst-new-ENCM (return-Indcpamon0-red-ENCM-game-state return-Indcpamon0_inst-ENCM)
)
)
(declare-const randctr-left-1 Int)
(assert (= randctr-left-1 (composition-rand-Indcpamod0-1 game-state-Indcpamod0_inst-old)
)
)
(declare-const randval-left-1 Bits_n)
(assert (= randval-left-1 (__sample-rand-Indcpamod0-Bits_n 1 (+ 0 randctr-left-1)
)
)
)
(declare-const randctr-left-2 Int)
(assert (= randctr-left-2 (composition-rand-Indcpamod0-2 game-state-Indcpamod0_inst-old)
)
)
(declare-const randval-left-2 Bits_n)
(assert (= randval-left-2 (__sample-rand-Indcpamod0-Bits_n 2 (+ 0 randctr-left-2)
)
)
)
(declare-const randctr-left-3 Int)
(assert (= randctr-left-3 (composition-rand-Indcpamod0-3 game-state-Indcpamod0_inst-old)
)
)
(declare-const randval-left-3 Bits_n)
(assert (= randval-left-3 (__sample-rand-Indcpamod0-Bits_n 3 (+ 0 randctr-left-3)
)
)
)
(declare-const randctr-left-4 Int)
(assert (= randctr-left-4 (composition-rand-Indcpamod0-4 game-state-Indcpamod0_inst-old)
)
)
(declare-const randval-left-4 Bits_n)
(assert (= randval-left-4 (__sample-rand-Indcpamod0-Bits_n 4 (+ 0 randctr-left-4)
)
)
)
(declare-const randctr-left-5 Int)
(assert (= randctr-left-5 (composition-rand-Indcpamod0-5 game-state-Indcpamod0_inst-old)
)
)
(declare-const randval-left-5 Bits_n)
(assert (= randval-left-5 (__sample-rand-Indcpamod0-Bits_n 5 (+ 0 randctr-left-5)
)
)
)
(declare-const randctr-left-6 Int)
(assert (= randctr-left-6 (composition-rand-Indcpamod0-6 game-state-Indcpamod0_inst-old)
)
)
(declare-const randval-left-6 Bits_n)
(assert (= randval-left-6 (__sample-rand-Indcpamod0-Bits_n 6 (+ 0 randctr-left-6)
)
)
)
(declare-const randctr-right-1 Int)
(assert (= randctr-right-1 (composition-rand-Indcpamon0-1 game-state-Indcpamon0_inst-old)
)
)
(declare-const randval-right-1 Bits_n)
(assert (= randval-right-1 (__sample-rand-Indcpamon0-Bits_n 1 (+ 0 randctr-right-1)
)
)
)
(declare-const randctr-right-2 Int)
(assert (= randctr-right-2 (composition-rand-Indcpamon0-2 game-state-Indcpamon0_inst-old)
)
)
(declare-const randval-right-2 Bits_n)
(assert (= randval-right-2 (__sample-rand-Indcpamon0-Bits_n 2 (+ 0 randctr-right-2)
)
)
)
(declare-const randctr-right-3 Int)
(assert (= randctr-right-3 (composition-rand-Indcpamon0-3 game-state-Indcpamon0_inst-old)
)
)
(declare-const randval-right-3 Bits_n)
(assert (= randval-right-3 (__sample-rand-Indcpamon0-Bits_n 3 (+ 0 randctr-right-3)
)
)
)
(declare-const randctr-right-4 Int)
(assert (= randctr-right-4 (composition-rand-Indcpamon0-4 game-state-Indcpamon0_inst-old)
)
)
(declare-const randval-right-4 Bits_n)
(assert (= randval-right-4 (__sample-rand-Indcpamon0-Bits_n 4 (+ 0 randctr-right-4)
)
)
)
(declare-const randctr-right-5 Int)
(assert (= randctr-right-5 (composition-rand-Indcpamon0-5 game-state-Indcpamon0_inst-old)
)
)
(declare-const randval-right-5 Bits_n)
(assert (= randval-right-5 (__sample-rand-Indcpamon0-Bits_n 5 (+ 0 randctr-right-5)
)
)
)
(declare-const randctr-right-6 Int)
(assert (= randctr-right-6 (composition-rand-Indcpamon0-6 game-state-Indcpamon0_inst-old)
)
)
(declare-const randval-right-6 Bits_n)
(assert (= randval-right-6 (__sample-rand-Indcpamon0-Bits_n 6 (+ 0 randctr-right-6)
)
)
)
(define-fun get-rand-ctr-Indcpamod0 ((sample-id Int)
)
 Int (ite (= sample-id 6)
 (composition-rand-Indcpamod0-6 game-state-Indcpamod0_inst-old)
 (ite (= sample-id 5)
 (composition-rand-Indcpamod0-5 game-state-Indcpamod0_inst-old)
 (ite (= sample-id 4)
 (composition-rand-Indcpamod0-4 game-state-Indcpamod0_inst-old)
 (ite (= sample-id 3)
 (composition-rand-Indcpamod0-3 game-state-Indcpamod0_inst-old)
 (ite (= sample-id 2)
 (composition-rand-Indcpamod0-2 game-state-Indcpamod0_inst-old)
 (ite (= sample-id 1)
 (composition-rand-Indcpamod0-1 game-state-Indcpamod0_inst-old)
 (ite (= sample-id 0)
 (composition-rand-Indcpamod0-0 game-state-Indcpamod0_inst-old)
 0)
)
)
)
)
)
)
)
(define-fun get-rand-ctr-Indcpamon0 ((sample-id Int)
)
 Int (ite (= sample-id 6)
 (composition-rand-Indcpamon0-6 game-state-Indcpamon0_inst-old)
 (ite (= sample-id 5)
 (composition-rand-Indcpamon0-5 game-state-Indcpamon0_inst-old)
 (ite (= sample-id 4)
 (composition-rand-Indcpamon0-4 game-state-Indcpamon0_inst-old)
 (ite (= sample-id 3)
 (composition-rand-Indcpamon0-3 game-state-Indcpamon0_inst-old)
 (ite (= sample-id 2)
 (composition-rand-Indcpamon0-2 game-state-Indcpamon0_inst-old)
 (ite (= sample-id 1)
 (composition-rand-Indcpamon0-1 game-state-Indcpamon0_inst-old)
 (ite (= sample-id 0)
 (composition-rand-Indcpamon0-0 game-state-Indcpamon0_inst-old)
 0)
)
)
)
)
)
)
)
(define-fun rand-is-eq ((sample-id-left Int)
 (sample-id-right Int)
 (sample-ctr-left Int)
 (sample-ctr-right Int)
)
 Bool (ite (and (or (= 1 sample-id-left)
 (= 2 sample-id-left)
 (= 3 sample-id-left)
 (= 4 sample-id-left)
 (= 5 sample-id-left)
 (= 6 sample-id-left)
)
 (or (= 1 sample-id-right)
 (= 2 sample-id-right)
 (= 3 sample-id-right)
 (= 4 sample-id-right)
 (= 5 sample-id-right)
 (= 6 sample-id-right)
)
)
 (= (__sample-rand-Indcpamod0-Bits_n sample-id-left sample-ctr-left)
 (__sample-rand-Indcpamon0-Bits_n sample-id-right sample-ctr-right)
)
 false)
)
(push 1)
;;;;;;;;;;;;;;;;;
;
; left  = mod
; right = mon
;
;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;   Randomness mapping
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define-fun randomness-mapping-SETBIT (
        (ctr-mod     Int)
        (ctr-mon     Int) 
        (id-mod      Int)
        (id-mon      Int) 
        (new-mod Int)
        (new-mon Int))         
         Bool
false
)


(define-fun randomness-mapping-GETAOUT (
        (ctr-mod     Int)
        (ctr-mon     Int) 
        (id-mod      Int)
        (id-mon      Int) 
        (new-mod Int)
        (new-mon Int)) 
        Bool

;
; mon = right
; red samples with index 4 k_ ~ z
; SMP verwendet counter 1 to sample k_ ~ not z
;
; mod = left
; top key package samples r with index 1 for true
;                        rr with index 2 for false
;

(and
(=>
; if z = true
(=
; z

(state-Indcpamon0-red-z
  (composition-pkgstate-Indcpamon0-red 
    game-state-Indcpamon0_inst-old))
(mk-some true))

; then
(or

;(=  randval-left-GETA-1  ; r at true
;    randval-right-GETA-4 ; k_ at z=true
;)

(and     (= id-mod 1) 
         (= id-mon 4) 
         (= ctr-mod new-mod)
         (= ctr-mon new-mon)
)

;(=  randval-left-GETA-2 ; rr at false
;   randval-right-GETA-1 ; k_ at not z = false
;)

(and     (= id-mod 2) 
         (= id-mon 1) 
         (= ctr-mod new-mod)
         (= ctr-mon new-mon)
)))

(=>
; if z = false
(=
; z
(state-Indcpamon0-red-z
(composition-pkgstate-Indcpamon0-red
game-state-Indcpamon0_inst-old)) 
(mk-some false))

; then
(or
(and     (= id-mod 1) 
         (= id-mon 1) 
         (= ctr-mod new-mod)
         (= ctr-mod new-mod)
)
(and     (= id-mod 2) 
         (= id-mon 4) 
         (= ctr-mod new-mod)
         (= ctr-mod new-mod)
)
;(=  randval-left-GETA-1 ; r at true
;   randval-right-GETA-1 ; k_ at not z
;)
;(=  randval-left-GETA-2 ; rr at false
;   randval-right-GETA-4 ; k_ at z
;)
)
)
)
)

(define-fun randomness-mapping-GETKEYSIN (
        (ctr-mod     Int)
        (ctr-mon     Int) 
        (id-mod      Int)
        (id-mon      Int) 
        (new-mod Int)
        (new-mon Int)) 
        Bool
false
)

(define-fun randomness-mapping-ENCN (
        (ctr-mod     Int)
        (ctr-mon     Int) 
        (id-mod      Int)
        (id-mon      Int) 
        (new-mod Int)
        (new-mon Int)
) Bool
(and
(= id-mod 5)
(= id-mon 2)
(= ctr-mod new-mod)
(= ctr-mon new-mon)
))

(define-fun randomness-mapping-ENCM (
;(= randval-left-ENCN-6 randval-right-ENCN-3)
        (ctr-mod     Int)
        (ctr-mon     Int) 
        (id-mod      Int)
        (id-mon      Int) 
        (new-mod Int)
        (new-mon Int)) Bool
(and
(= id-mod 6)
(= id-mon 3)
(= ctr-mod new-mod)
(= ctr-mon new-mon)
)        
)



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;   Datatypes to extract key package state
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(declare-datatype
  State_keys
  (
    (mk-state-keys
      (state-keys-T    (Maybe (Array Bool (Maybe Bits_n))))
      (state-keys-z    (Maybe Bool))
      (state-keys-flag (Maybe Bool)))))

(define-fun project-State_Indcpamod0_keys_top ((in State_Indcpamod0_keys_top)) State_keys
  (mk-state-keys (state-Indcpamod0-keys_top-T    in)
                 (state-Indcpamod0-keys_top-z    in)
                 (state-Indcpamod0-keys_top-flag in)))



(define-fun project-keys-State_Indcpamon0_indcpamon0 ((in CompositionState-Indcpamon0)) State_keys
(let ((red-state (composition-pkgstate-Indcpamon0-red        in))
      (ind-state (composition-pkgstate-Indcpamon0-indcpamon0 in))
     )
(let ((ka    (state-Indcpamon0-red-k        red-state))
      (kina  (state-Indcpamon0-indcpamon0-k ind-state))
      (z     (state-Indcpamon0-red-z        red-state))
      (flag  (state-Indcpamon0-red-flag     red-state)))
(let ((Z (ite (or (not (= ka   (as mk-none (Maybe Bits_n))))
                  (not (= kina (as mk-none (Maybe Bits_n))))
              )
              (mk-some (store (store
                 ;initialize empty table 
                 ((as const (Array Bool (Maybe Bits_n))) (as mk-none (Maybe Bits_n))) 
                      (maybe-get z)  ka) 
                 (not (maybe-get z)) kina))
                 (as mk-none (Maybe (Array Bool (Maybe Bits_n))))
)))
     (mk-state-keys Z z flag)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;   Well-definedness of tables
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;If T h != none => T h b != none (for both b=0 and b=1)

(define-fun well-defined ((T (Maybe (Array Bool (Maybe Bits_n))))) Bool
    (or
      (= T (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
      (forall ((b Bool))
        (not
          (= (select (maybe-get T) b) (as mk-none (Maybe Bits_n))
    )
))))

; captures the possible states which a Key package can be in when
; the "top" queries are GETKEYS queries 
;
(define-fun well-defined-Key-bool ((key-state State_keys)) Bool
(let ((T    (state-keys-T    key-state))
      (flag (state-keys-flag key-state))
      (z    (state-keys-z    key-state)))

(and

; T = none or for b=0,1: T b != none
(well-defined T)

;flag is either none or true
(or
    (= flag (as mk-none (Maybe Bool)))
    (= flag (   mk-some        true)))

;flag = true <=> T != none
(=
     (= flag (mk-some true))
(not (= T (as mk-none (Maybe (Array Bool (Maybe Bits_n))))))
)

;flag = true => z != none
(=>
     (= flag (mk-some true))
(not (= z (as mk-none (Maybe Bool)))))
)

))

; captures the possible states which a Key package can be in when
; the "top" queries are GETA and SETBIT queries 
;
(define-fun well-defined-Key-active ((key-state State_keys)) Bool
(let ((T    (state-keys-T    key-state))
      (flag (state-keys-flag key-state))
      (z    (state-keys-z    key-state)))

(and

;If T h != none => T h b != none (for both b=0 and b=1)
(well-defined T)

(and
(or
  (= flag (as mk-none (Maybe Bool)))
  (= flag (   mk-some        true )))

 ;flag has been set  => bit has been set
(=> (=  (mk-some true ) flag)  
                    (or (=  (mk-some true ) z)
                        (=  (mk-some false) z)
                    ))
; key has been set => flag has been set
(=> (not            (= T (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
                    )
                    (= flag (mk-some true)))
))))

(define-fun well-defined-Key-debug ((key-state State_keys)) Bool
(let ((T    (state-keys-T    key-state))
      (flag (state-keys-flag key-state))
      (z    (state-keys-z    key-state)))

(and true

;T != none or for b=0,1 T b != none
(well-defined T)
(not (= T (as mk-none (Maybe (Array Bool (Maybe Bits_n))))))
(not (= z (as mk-none (Maybe Bool))))
(= flag (mk-some true))

)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Invariant
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun invariant-ENCN
    ((state-left CompositionState-Indcpamod0)
	 (state-right CompositionState-Indcpamon0))
    Bool
  (let ((top-key-package-left  (project-State_Indcpamod0_keys_top      (composition-pkgstate-Indcpamod0-keys_top state-left)))
        (top-key-package-right (project-keys-State_Indcpamon0_indcpamon0     state-right)))
    (and
      ;top key package states are equal
      (= top-key-package-left top-key-package-right)

      ;top key package state is "good"
      (well-defined-Key-debug top-key-package-left )
      (well-defined-Key-debug top-key-package-right)

      ;the functions left and right are the same
      (forall ((k Bits_n)(x Bits_n)(r Bits_n))
        (= (__func-Indcpamon0-encn k x r) (__func-Indcpamod0-encn  k x r))))))


;;;   (define-fun invariant-ENCN          (
;;;           (state-left  (Array Int CompositionState-Indcpamod0 ))
;;;           (state-right (Array Int CompositionState-Indcpamon0))
;;;           (state-length-left  Int) ;old index
;;;           (state-length-right Int) ;old index
;;;           (state-left-new  Return_Indcpamod0_enc_ENCN)
;;;           (state-right-new Return_Indcpamon0_red_ENCN)
;;;           (d Bool)
;;;           (nzero Bits_n)
;;;           (none  Bits_n))
;;;       Bool
;;;      (let
;;;   
;;;   ; state of the key packages
;;;   (
;;;   (top-key-package-left  (project-State_Indcpamod0_keys_top      (composition-pkgstate-Indcpamod0-keys_top     (select state-left  state-length-left))))
;;;   (top-key-package-right (project-keys-State_Indcpamon0_indcpamon0   (select state-right state-length-right)))  ;(composition-pkgstate-Indcpamon0-indcpamon0    (select state-right state-length-right))))
;;;   )
;;;   
;;;   
;;; 
;;; 
;;; 
;;; (and
;;; ;top key package states are equal
;;; (= top-key-package-left top-key-package-right)
;;; 
;;; 
;;; ;top key package state is "good"
;;; (well-defined-Key-debug top-key-package-left )
;;; (well-defined-Key-debug top-key-package-right)
;;; 
;;; ;the functions left and right are the same
;;; (forall ((k Bits_n)(x Bits_n)(r Bits_n))
;;; (= (__func-Indcpamon0-encn k x r) (__func-Indcpamod0-encn  k x r))
;;; )
;;; )))


(define-fun invariant-ENCN-post          (
        (state-left  CompositionState-Indcpamod0 )
        (state-right CompositionState-Indcpamon0)
        (state-left-new  Return-Indcpamod0-enc-ENCN)
        (state-right-new Return-Indcpamon0-red-ENCN)
        (d Bool)
        (nzero Bits_n)
        (none  Bits_n))
    Bool
(let (
      (state-left-nov  (return-Indcpamod0-enc-ENCN-game-state    state-left-new))
      (state-right-nov (return-Indcpamon0-red-ENCN-game-state        state-right-new))
     )

    (let

; state of the key packages
(
(top-key-package-left  (project-State_Indcpamod0_keys_top      (composition-pkgstate-Indcpamod0-keys_top     state-left-nov  )))
(top-key-package-right (project-keys-State_Indcpamon0_indcpamon0  state-right-nov )))   ; ((;;(composition-pkgstate-Indcpamon0-indcpamon0    state-right-nov )))

(and
;top key package states are equal
(= top-key-package-left top-key-package-right)


;top key package state is "good"
(  well-defined-Key-active top-key-package-left )
(  well-defined-Key-active top-key-package-right)
))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Invariant stuff
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define-fun invariant-SETBIT      (
        (state-left  CompositionState-Indcpamod0 )
        (state-right CompositionState-Indcpamon0)
)
    Bool
    (let

; state of the key packages
(
(top-key-package-left  (project-State_Indcpamod0_keys_top      (composition-pkgstate-Indcpamod0-keys_top     state-left )))
(top-key-package-right (project-keys-State_Indcpamon0_indcpamon0   state-right ))  ;((;;(composition-pkgstate-Indcpamon0-indcpamon0    (select state-right state-length-right))))
)

(and
;top key package states are equal
(= top-key-package-left top-key-package-right)


;top key package state is "good"
(well-defined-Key-active top-key-package-left )
(well-defined-Key-active top-key-package-right)

)))




(define-fun invariant-GETAOUT      (
        (state-left  CompositionState-Indcpamod0 )
        (state-right CompositionState-Indcpamon0)
        ;(state-left-new  Return-Indcpamod0-keys_top-GETAOUT)
        ;(state-right-new Return-Indcpamon0-red-GETAOUT)
        )
    Bool
    (let

; state of the key packages
(
(top-key-package-left  (project-State_Indcpamod0_keys_top      (composition-pkgstate-Indcpamod0-keys_top      state-left )))
(top-key-package-right (project-keys-State_Indcpamon0_indcpamon0  state-right )) ;  (((composition-pkgstate-Indcpamon0-indcpamon0    (select state-right state-length-right))))
)

(and
;top key package states are equal
(= top-key-package-left top-key-package-right)


;top key package state is "good"
(well-defined-Key-active top-key-package-left )
(well-defined-Key-active top-key-package-right)

)))







;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;    aborts equal
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun aborts-equal-ENCN          (
        (state-left  CompositionState-Indcpamod0)
        (state-right CompositionState-Indcpamon0)
        (state-left-NEU Return-Indcpamod0-enc-ENCN)      ; also contains new index    
        (state-right-NEU Return-Indcpamon0-red-ENCN) ; also contains new index
        (d Bool)
        (nzero Bits_n)
        (none  Bits_n))
        Bool


(= (= (return-Indcpamod0-enc-ENCN-return-value-or-abort     state-left-NEU) (as mk-abort (ReturnValue Bits_m)))
   (= (return-Indcpamon0-red-ENCN-return-value-or-abort     state-right-NEU) (as mk-abort (ReturnValue Bits_m)))))



(define-fun aborts-equal-SETBIT          (
        (state-left  CompositionState-Indcpamod0)
        (state-right CompositionState-Indcpamon0)
        (state-left-NEU Return-Indcpamod0-keys_top-SETBIT)      ; also contains new index    
        (state-right-NEU Return-Indcpamon0-red-SETBIT) ; also contains new index
        (zz Bool))
        Bool


(= (= (return-Indcpamod0-keys_top-SETBIT-return-value-or-abort     state-left-NEU) (as mk-abort (ReturnValue Empty)))
   (= (return-Indcpamon0-red-SETBIT-return-value-or-abort     state-right-NEU) (as mk-abort (ReturnValue Empty)))))

(define-fun aborts-equal-GETAOUT          (
        (state-left  CompositionState-Indcpamod0)
        (state-right CompositionState-Indcpamon0)
        (state-left-NEU Return-Indcpamod0-keys_top-GETAOUT)      ; also contains new index    
        (state-right-NEU Return-Indcpamon0-red-GETAOUT)          ; also contains new index
        )
        Bool



(= (= (return-Indcpamod0-keys_top-GETAOUT-return-value-or-abort     state-left-NEU) (as mk-abort (ReturnValue Bits_n)))
   (= (return-Indcpamon0-red-GETAOUT-return-value-or-abort     state-right-NEU) (as mk-abort (ReturnValue Bits_n)))))



; no-abort

(define-fun no-abort-ENCN          (
        (state-left  CompositionState-Indcpamod0)
        (state-right CompositionState-Indcpamon0)
        (state-left-NEU  Return-Indcpamod0-enc-ENCN)  ; also contains new index    
        (state-right-NEU Return-Indcpamon0-red-ENCN) ; also contains new index
        (d Bool)
        (nzero Bits_n)
        (none  Bits_n))
        Bool


(and (not (= (return-Indcpamod0-enc-ENCN-return-value-or-abort     state-left-NEU) (as mk-abort (ReturnValue Bits_m))))
     (not (= (return-Indcpamon0-red-ENCN-return-value-or-abort     state-right-NEU) (as mk-abort (ReturnValue Bits_m))))))


(define-fun left-abort-ENCN          (
        (state-left   CompositionState-Indcpamod0)
        (state-right  CompositionState-Indcpamon0)
        (state-left-NEU  Return-Indcpamod0-enc-ENCN)  ; also contains new index    
        (state-right-NEU Return-Indcpamon0-red-ENCN) ; also contains new index
        (d Bool)
        (nzero Bits_n)
        (none  Bits_n))
        Bool

(= (return-Indcpamod0-enc-ENCN-return-value-or-abort     state-left-NEU) (as mk-abort (ReturnValue Bits_m))))

(define-fun right-abort-ENCN          (
        (state-left  CompositionState-Indcpamod0)
        (state-right CompositionState-Indcpamon0)
        (state-left-NEU  Return-Indcpamod0-enc-ENCN)  ; also contains new index    
        (state-right-NEU Return-Indcpamon0-red-ENCN) ; also contains new index
        (d Bool)
        (nzero Bits_n)
        (none  Bits_n))
        Bool
(= (return-Indcpamon0-red-ENCN-return-value-or-abort     state-right-NEU) (as mk-abort (ReturnValue Bits_m))))


(define-fun no-abort-SETBIT          (
        (state-left  CompositionState-Indcpamod0)
        (state-right CompositionState-Indcpamon0)
        (state-left-NEU  Return-Indcpamod0-keys_top-SETBIT)  ; also contains new index    
        (state-right-NEU Return-Indcpamon0-red-SETBIT) ; also contains new index
        (zz Bool))
        Bool

(and (not (= (return-Indcpamod0-keys_top-SETBIT-return-value-or-abort     state-left-NEU) (as mk-abort (ReturnValue Empty))))
     (not (= (return-Indcpamon0-red-SETBIT-return-value-or-abort     state-right-NEU) (as mk-abort (ReturnValue Empty))))))

(define-fun no-abort-GETAOUT          (
        (state-left  CompositionState-Indcpamod0)
        (state-right CompositionState-Indcpamon0)
        (state-left-NEU  Return-Indcpamod0-keys_top-GETAOUT)  ; also contains new index    
        (state-right-NEU Return-Indcpamon0-red-GETAOUT) ; also contains new index
        )
        Bool

(and (not (= (return-Indcpamod0-keys_top-GETAOUT-return-value-or-abort     state-left-NEU) (as mk-abort (ReturnValue Bits_n))))
     (not (= (return-Indcpamon0-red-GETAOUT-return-value-or-abort     state-right-NEU) (as mk-abort (ReturnValue Bits_n))))))


(define-fun left-abort-GETAOUT          (
        (state-left   CompositionState-Indcpamod0)
        (state-right  CompositionState-Indcpamon0)
        (state-left-NEU  Return-Indcpamod0-keys_top-GETAOUT)  ; also contains new index    
        (state-right-NEU Return-Indcpamon0-red-GETAOUT) ; also contains new index
        )
        Bool

(= (return-Indcpamod0-keys_top-GETAOUT-return-value-or-abort     state-left-NEU) (as mk-abort (ReturnValue Bits_n))))


(define-fun right-abort-GETAOUT          (
        (state-left   CompositionState-Indcpamod0)
        (state-right  CompositionState-Indcpamon0)
        (state-left-NEU  Return-Indcpamod0-keys_top-GETAOUT)  ; also contains new index    
        (state-right-NEU Return-Indcpamon0-red-GETAOUT) ; also contains new index
        )
        Bool

(= (return-Indcpamon0-red-GETAOUT-return-value-or-abort     state-right-NEU) (as mk-abort (ReturnValue Bits_n))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;    State lemmas Indcpamod0
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;    State lemmas Indcpamon0
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Same Output 
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(define-fun same-output-ENCN          (
        (state-left CompositionState-Indcpamod0)
        (state-right CompositionState-Indcpamon0)
        (state-left-NEU Return-Indcpamod0-enc-ENCN)
        (state-right-NEU Return-Indcpamon0-red-ENCN)
        (d Bool)
        (nzero Bits_n)
        (none  Bits_n))
        Bool
(=
(return-Indcpamod0-enc-ENCN-return-value-or-abort return-Indcpamod0_inst-ENCN)
(return-Indcpamon0-red-ENCN-return-value-or-abort return-Indcpamon0_inst-ENCN)
)
)


(define-fun same-output-SETBIT          (
        (state-left  CompositionState-Indcpamod0)
        (state-right CompositionState-Indcpamon0)
        (state-left-NEU Return-Indcpamod0-keys_top-SETBIT)
        (state-right-NEU Return-Indcpamon0-red-SETBIT)
        (zz Bool))
        Bool
(=
(return-Indcpamod0-keys_top-SETBIT-return-value-or-abort return-Indcpamod0_inst-SETBIT)
(return-Indcpamon0-red-SETBIT-return-value-or-abort return-Indcpamon0_inst-SETBIT)
)
)

(define-fun same-output-GETAOUT          (
        (state-left   CompositionState-Indcpamod0)
        (state-right  CompositionState-Indcpamon0)
        (state-left-NEU Return-Indcpamod0-keys_top-GETAOUT)
        (state-right-NEU Return-Indcpamon0-red-GETAOUT)
        )
        Bool
(=
(return-Indcpamod0-keys_top-GETAOUT-return-value-or-abort return-Indcpamod0_inst-GETAOUT)
(return-Indcpamon0-red-GETAOUT-return-value-or-abort return-Indcpamon0_inst-GETAOUT)
)
)
(check-sat)
(push 1)(assert (not (=> (and (forall ((randmap-sample-id-left Int)
 (randmap-sample-ctr-left Int)
 (randmap-sample-id-right Int)
 (randmap-sample-ctr-right Int)
)
 (=> (randomness-mapping-GETAOUT (get-rand-ctr-Indcpamod0 randmap-sample-id-left)
 (get-rand-ctr-Indcpamon0 randmap-sample-id-right)
 randmap-sample-id-left randmap-sample-id-right randmap-sample-ctr-left randmap-sample-ctr-right)
 (rand-is-eq randmap-sample-id-left randmap-sample-id-right randmap-sample-ctr-left randmap-sample-ctr-right)
)
)
 (invariant-GETAOUT game-state-Indcpamod0_inst-old game-state-Indcpamon0_inst-old)
 (no-abort-GETAOUT game-state-Indcpamod0_inst-old game-state-Indcpamon0_inst-old return-Indcpamod0_inst-GETAOUT return-Indcpamon0_inst-GETAOUT)
)
 (same-output-GETAOUT game-state-Indcpamod0_inst-old game-state-Indcpamon0_inst-old return-Indcpamod0_inst-GETAOUT return-Indcpamon0_inst-GETAOUT)
)
)
)
(check-sat)
(pop 1)(push 1)(assert (not (=> (and (forall ((randmap-sample-id-left Int)
 (randmap-sample-ctr-left Int)
 (randmap-sample-id-right Int)
 (randmap-sample-ctr-right Int)
)
 (=> (randomness-mapping-GETAOUT (get-rand-ctr-Indcpamod0 randmap-sample-id-left)
 (get-rand-ctr-Indcpamon0 randmap-sample-id-right)
 randmap-sample-id-left randmap-sample-id-right randmap-sample-ctr-left randmap-sample-ctr-right)
 (rand-is-eq randmap-sample-id-left randmap-sample-id-right randmap-sample-ctr-left randmap-sample-ctr-right)
)
)
 (invariant-GETAOUT game-state-Indcpamod0_inst-old game-state-Indcpamon0_inst-old)
 (no-abort-GETAOUT game-state-Indcpamod0_inst-old game-state-Indcpamon0_inst-old return-Indcpamod0_inst-GETAOUT return-Indcpamon0_inst-GETAOUT)
)
 (invariant-GETAOUT game-state-Indcpamod0_inst-new-GETAOUT game-state-Indcpamon0_inst-new-GETAOUT)
)
)
)
(check-sat)
(pop 1)(push 1)(assert (not (=> (and (forall ((randmap-sample-id-left Int)
 (randmap-sample-ctr-left Int)
 (randmap-sample-id-right Int)
 (randmap-sample-ctr-right Int)
)
 (=> (randomness-mapping-GETAOUT (get-rand-ctr-Indcpamod0 randmap-sample-id-left)
 (get-rand-ctr-Indcpamon0 randmap-sample-id-right)
 randmap-sample-id-left randmap-sample-id-right randmap-sample-ctr-left randmap-sample-ctr-right)
 (rand-is-eq randmap-sample-id-left randmap-sample-id-right randmap-sample-ctr-left randmap-sample-ctr-right)
)
)
 (invariant-GETAOUT game-state-Indcpamod0_inst-old game-state-Indcpamon0_inst-old)
)
 (aborts-equal-GETAOUT game-state-Indcpamod0_inst-old game-state-Indcpamon0_inst-old return-Indcpamod0_inst-GETAOUT return-Indcpamon0_inst-GETAOUT)
)
)
)
(check-sat)
(pop 1)(pop 1)(push 1)
;;;;;;;;;;;;;;;;;
;
; left  = mod
; right = mon
;
;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;   Randomness mapping
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define-fun randomness-mapping-SETBIT (
        (ctr-mod     Int)
        (ctr-mon     Int) 
        (id-mod      Int)
        (id-mon      Int) 
        (new-mod Int)
        (new-mon Int))         
         Bool
false
)


(define-fun randomness-mapping-GETAOUT (
        (ctr-mod     Int)
        (ctr-mon     Int) 
        (id-mod      Int)
        (id-mon      Int) 
        (new-mod Int)
        (new-mon Int)) 
        Bool

;
; mon = right
; red samples with index 4 k_ ~ z
; SMP verwendet counter 1 to sample k_ ~ not z
;
; mod = left
; top key package samples r with index 1 for true
;                        rr with index 2 for false
;

(and
(=>
; if z = true
(=
; z

(state-Indcpamon0-red-z
  (composition-pkgstate-Indcpamon0-red 
    game-state-Indcpamon0_inst-old))
(mk-some true))

; then
(or

;(=  randval-left-GETA-1  ; r at true
;    randval-right-GETA-4 ; k_ at z=true
;)

(and     (= id-mod 1) 
         (= id-mon 4) 
         (= ctr-mod new-mod)
         (= ctr-mon new-mon)
)

;(=  randval-left-GETA-2 ; rr at false
;   randval-right-GETA-1 ; k_ at not z = false
;)

(and     (= id-mod 2) 
         (= id-mon 1) 
         (= ctr-mod new-mod)
         (= ctr-mon new-mon)
)))

(=>
; if z = false
(=
; z
(state-Indcpamon0-red-z
(composition-pkgstate-Indcpamon0-red
game-state-Indcpamon0_inst-old)) 
(mk-some false))

; then
(or
(and     (= id-mod 1) 
         (= id-mon 1) 
         (= ctr-mod new-mod)
         (= ctr-mod new-mod)
)
(and     (= id-mod 2) 
         (= id-mon 4) 
         (= ctr-mod new-mod)
         (= ctr-mod new-mod)
)
;(=  randval-left-GETA-1 ; r at true
;   randval-right-GETA-1 ; k_ at not z
;)
;(=  randval-left-GETA-2 ; rr at false
;   randval-right-GETA-4 ; k_ at z
;)
)
)
)
)

(define-fun randomness-mapping-GETKEYSIN (
        (ctr-mod     Int)
        (ctr-mon     Int) 
        (id-mod      Int)
        (id-mon      Int) 
        (new-mod Int)
        (new-mon Int)) 
        Bool
false
)

(define-fun randomness-mapping-ENCN (
        (ctr-mod     Int)
        (ctr-mon     Int) 
        (id-mod      Int)
        (id-mon      Int) 
        (new-mod Int)
        (new-mon Int)
) Bool
(and
(= id-mod 5)
(= id-mon 2)
(= ctr-mod new-mod)
(= ctr-mon new-mon)
))

(define-fun randomness-mapping-ENCM (
;(= randval-left-ENCN-6 randval-right-ENCN-3)
        (ctr-mod     Int)
        (ctr-mon     Int) 
        (id-mod      Int)
        (id-mon      Int) 
        (new-mod Int)
        (new-mon Int)) Bool
(and
(= id-mod 6)
(= id-mon 3)
(= ctr-mod new-mod)
(= ctr-mon new-mon)
)        
)



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;   Datatypes to extract key package state
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(declare-datatype
  State_keys
  (
    (mk-state-keys
      (state-keys-T    (Maybe (Array Bool (Maybe Bits_n))))
      (state-keys-z    (Maybe Bool))
      (state-keys-flag (Maybe Bool)))))

(define-fun project-State_Indcpamod0_keys_top ((in State_Indcpamod0_keys_top)) State_keys
  (mk-state-keys (state-Indcpamod0-keys_top-T    in)
                 (state-Indcpamod0-keys_top-z    in)
                 (state-Indcpamod0-keys_top-flag in)))



(define-fun project-keys-State_Indcpamon0_indcpamon0 ((in CompositionState-Indcpamon0)) State_keys
(let ((red-state (composition-pkgstate-Indcpamon0-red        in))
      (ind-state (composition-pkgstate-Indcpamon0-indcpamon0 in))
     )
(let ((ka    (state-Indcpamon0-red-k        red-state))
      (kina  (state-Indcpamon0-indcpamon0-k ind-state))
      (z     (state-Indcpamon0-red-z        red-state))
      (flag  (state-Indcpamon0-red-flag     red-state)))
(let ((Z (ite (or (not (= ka   (as mk-none (Maybe Bits_n))))
                  (not (= kina (as mk-none (Maybe Bits_n))))
              )
              (mk-some (store (store
                 ;initialize empty table 
                 ((as const (Array Bool (Maybe Bits_n))) (as mk-none (Maybe Bits_n))) 
                      (maybe-get z)  ka) 
                 (not (maybe-get z)) kina))
                 (as mk-none (Maybe (Array Bool (Maybe Bits_n))))
)))
     (mk-state-keys Z z flag)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;   Well-definedness of tables
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;If T h != none => T h b != none (for both b=0 and b=1)

(define-fun well-defined ((T (Maybe (Array Bool (Maybe Bits_n))))) Bool
    (or
      (= T (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
      (forall ((b Bool))
        (not
          (= (select (maybe-get T) b) (as mk-none (Maybe Bits_n))
    )
))))

; captures the possible states which a Key package can be in when
; the "top" queries are GETKEYS queries 
;
(define-fun well-defined-Key-bool ((key-state State_keys)) Bool
(let ((T    (state-keys-T    key-state))
      (flag (state-keys-flag key-state))
      (z    (state-keys-z    key-state)))

(and

; T = none or for b=0,1: T b != none
(well-defined T)

;flag is either none or true
(or
    (= flag (as mk-none (Maybe Bool)))
    (= flag (   mk-some        true)))

;flag = true <=> T != none
(=
     (= flag (mk-some true))
(not (= T (as mk-none (Maybe (Array Bool (Maybe Bits_n))))))
)

;flag = true => z != none
(=>
     (= flag (mk-some true))
(not (= z (as mk-none (Maybe Bool)))))
)

))

; captures the possible states which a Key package can be in when
; the "top" queries are GETA and SETBIT queries 
;
(define-fun well-defined-Key-active ((key-state State_keys)) Bool
(let ((T    (state-keys-T    key-state))
      (flag (state-keys-flag key-state))
      (z    (state-keys-z    key-state)))

(and

;If T h != none => T h b != none (for both b=0 and b=1)
(well-defined T)

(and
(or
  (= flag (as mk-none (Maybe Bool)))
  (= flag (   mk-some        true )))

 ;flag has been set  => bit has been set
(=> (=  (mk-some true ) flag)  
                    (or (=  (mk-some true ) z)
                        (=  (mk-some false) z)
                    ))
; key has been set => flag has been set
(=> (not            (= T (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
                    )
                    (= flag (mk-some true)))
))))

(define-fun well-defined-Key-debug ((key-state State_keys)) Bool
(let ((T    (state-keys-T    key-state))
      (flag (state-keys-flag key-state))
      (z    (state-keys-z    key-state)))

(and true

;T != none or for b=0,1 T b != none
(well-defined T)
(not (= T (as mk-none (Maybe (Array Bool (Maybe Bits_n))))))
(not (= z (as mk-none (Maybe Bool))))
(= flag (mk-some true))

)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Invariant
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun invariant-ENCN
    ((state-left CompositionState-Indcpamod0)
	 (state-right CompositionState-Indcpamon0))
    Bool
  (let ((top-key-package-left  (project-State_Indcpamod0_keys_top      (composition-pkgstate-Indcpamod0-keys_top state-left)))
        (top-key-package-right (project-keys-State_Indcpamon0_indcpamon0     state-right)))
    (and
      ;top key package states are equal
      (= top-key-package-left top-key-package-right)

      ;top key package state is "good"
      (well-defined-Key-debug top-key-package-left )
      (well-defined-Key-debug top-key-package-right)

      ;the functions left and right are the same
      (forall ((k Bits_n)(x Bits_n)(r Bits_n))
        (= (__func-Indcpamon0-encn k x r) (__func-Indcpamod0-encn  k x r))))))


;;;   (define-fun invariant-ENCN          (
;;;           (state-left  (Array Int CompositionState-Indcpamod0 ))
;;;           (state-right (Array Int CompositionState-Indcpamon0))
;;;           (state-length-left  Int) ;old index
;;;           (state-length-right Int) ;old index
;;;           (state-left-new  Return_Indcpamod0_enc_ENCN)
;;;           (state-right-new Return_Indcpamon0_red_ENCN)
;;;           (d Bool)
;;;           (nzero Bits_n)
;;;           (none  Bits_n))
;;;       Bool
;;;      (let
;;;   
;;;   ; state of the key packages
;;;   (
;;;   (top-key-package-left  (project-State_Indcpamod0_keys_top      (composition-pkgstate-Indcpamod0-keys_top     (select state-left  state-length-left))))
;;;   (top-key-package-right (project-keys-State_Indcpamon0_indcpamon0   (select state-right state-length-right)))  ;(composition-pkgstate-Indcpamon0-indcpamon0    (select state-right state-length-right))))
;;;   )
;;;   
;;;   
;;; 
;;; 
;;; 
;;; (and
;;; ;top key package states are equal
;;; (= top-key-package-left top-key-package-right)
;;; 
;;; 
;;; ;top key package state is "good"
;;; (well-defined-Key-debug top-key-package-left )
;;; (well-defined-Key-debug top-key-package-right)
;;; 
;;; ;the functions left and right are the same
;;; (forall ((k Bits_n)(x Bits_n)(r Bits_n))
;;; (= (__func-Indcpamon0-encn k x r) (__func-Indcpamod0-encn  k x r))
;;; )
;;; )))


(define-fun invariant-ENCN-post          (
        (state-left  CompositionState-Indcpamod0 )
        (state-right CompositionState-Indcpamon0)
        (state-left-new  Return-Indcpamod0-enc-ENCN)
        (state-right-new Return-Indcpamon0-red-ENCN)
        (d Bool)
        (nzero Bits_n)
        (none  Bits_n))
    Bool
(let (
      (state-left-nov  (return-Indcpamod0-enc-ENCN-game-state    state-left-new))
      (state-right-nov (return-Indcpamon0-red-ENCN-game-state        state-right-new))
     )

    (let

; state of the key packages
(
(top-key-package-left  (project-State_Indcpamod0_keys_top      (composition-pkgstate-Indcpamod0-keys_top     state-left-nov  )))
(top-key-package-right (project-keys-State_Indcpamon0_indcpamon0  state-right-nov )))   ; ((;;(composition-pkgstate-Indcpamon0-indcpamon0    state-right-nov )))

(and
;top key package states are equal
(= top-key-package-left top-key-package-right)


;top key package state is "good"
(  well-defined-Key-active top-key-package-left )
(  well-defined-Key-active top-key-package-right)
))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Invariant stuff
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define-fun invariant-SETBIT      (
        (state-left  CompositionState-Indcpamod0 )
        (state-right CompositionState-Indcpamon0)
)
    Bool
    (let

; state of the key packages
(
(top-key-package-left  (project-State_Indcpamod0_keys_top      (composition-pkgstate-Indcpamod0-keys_top     state-left )))
(top-key-package-right (project-keys-State_Indcpamon0_indcpamon0   state-right ))  ;((;;(composition-pkgstate-Indcpamon0-indcpamon0    (select state-right state-length-right))))
)

(and
;top key package states are equal
(= top-key-package-left top-key-package-right)


;top key package state is "good"
(well-defined-Key-active top-key-package-left )
(well-defined-Key-active top-key-package-right)

)))




(define-fun invariant-GETAOUT      (
        (state-left  CompositionState-Indcpamod0 )
        (state-right CompositionState-Indcpamon0)
        ;(state-left-new  Return-Indcpamod0-keys_top-GETAOUT)
        ;(state-right-new Return-Indcpamon0-red-GETAOUT)
        )
    Bool
    (let

; state of the key packages
(
(top-key-package-left  (project-State_Indcpamod0_keys_top      (composition-pkgstate-Indcpamod0-keys_top      state-left )))
(top-key-package-right (project-keys-State_Indcpamon0_indcpamon0  state-right )) ;  (((composition-pkgstate-Indcpamon0-indcpamon0    (select state-right state-length-right))))
)

(and
;top key package states are equal
(= top-key-package-left top-key-package-right)


;top key package state is "good"
(well-defined-Key-active top-key-package-left )
(well-defined-Key-active top-key-package-right)

)))







;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;    aborts equal
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun aborts-equal-ENCN          (
        (state-left  CompositionState-Indcpamod0)
        (state-right CompositionState-Indcpamon0)
        (state-left-NEU Return-Indcpamod0-enc-ENCN)      ; also contains new index    
        (state-right-NEU Return-Indcpamon0-red-ENCN) ; also contains new index
        (d Bool)
        (nzero Bits_n)
        (none  Bits_n))
        Bool


(= (= (return-Indcpamod0-enc-ENCN-return-value-or-abort     state-left-NEU) (as mk-abort (ReturnValue Bits_m)))
   (= (return-Indcpamon0-red-ENCN-return-value-or-abort     state-right-NEU) (as mk-abort (ReturnValue Bits_m)))))



(define-fun aborts-equal-SETBIT          (
        (state-left  CompositionState-Indcpamod0)
        (state-right CompositionState-Indcpamon0)
        (state-left-NEU Return-Indcpamod0-keys_top-SETBIT)      ; also contains new index    
        (state-right-NEU Return-Indcpamon0-red-SETBIT) ; also contains new index
        (zz Bool))
        Bool


(= (= (return-Indcpamod0-keys_top-SETBIT-return-value-or-abort     state-left-NEU) (as mk-abort (ReturnValue Empty)))
   (= (return-Indcpamon0-red-SETBIT-return-value-or-abort     state-right-NEU) (as mk-abort (ReturnValue Empty)))))

(define-fun aborts-equal-GETAOUT          (
        (state-left  CompositionState-Indcpamod0)
        (state-right CompositionState-Indcpamon0)
        (state-left-NEU Return-Indcpamod0-keys_top-GETAOUT)      ; also contains new index    
        (state-right-NEU Return-Indcpamon0-red-GETAOUT)          ; also contains new index
        )
        Bool



(= (= (return-Indcpamod0-keys_top-GETAOUT-return-value-or-abort     state-left-NEU) (as mk-abort (ReturnValue Bits_n)))
   (= (return-Indcpamon0-red-GETAOUT-return-value-or-abort     state-right-NEU) (as mk-abort (ReturnValue Bits_n)))))



; no-abort

(define-fun no-abort-ENCN          (
        (state-left  CompositionState-Indcpamod0)
        (state-right CompositionState-Indcpamon0)
        (state-left-NEU  Return-Indcpamod0-enc-ENCN)  ; also contains new index    
        (state-right-NEU Return-Indcpamon0-red-ENCN) ; also contains new index
        (d Bool)
        (nzero Bits_n)
        (none  Bits_n))
        Bool


(and (not (= (return-Indcpamod0-enc-ENCN-return-value-or-abort     state-left-NEU) (as mk-abort (ReturnValue Bits_m))))
     (not (= (return-Indcpamon0-red-ENCN-return-value-or-abort     state-right-NEU) (as mk-abort (ReturnValue Bits_m))))))


(define-fun left-abort-ENCN          (
        (state-left   CompositionState-Indcpamod0)
        (state-right  CompositionState-Indcpamon0)
        (state-left-NEU  Return-Indcpamod0-enc-ENCN)  ; also contains new index    
        (state-right-NEU Return-Indcpamon0-red-ENCN) ; also contains new index
        (d Bool)
        (nzero Bits_n)
        (none  Bits_n))
        Bool

(= (return-Indcpamod0-enc-ENCN-return-value-or-abort     state-left-NEU) (as mk-abort (ReturnValue Bits_m))))

(define-fun right-abort-ENCN          (
        (state-left  CompositionState-Indcpamod0)
        (state-right CompositionState-Indcpamon0)
        (state-left-NEU  Return-Indcpamod0-enc-ENCN)  ; also contains new index    
        (state-right-NEU Return-Indcpamon0-red-ENCN) ; also contains new index
        (d Bool)
        (nzero Bits_n)
        (none  Bits_n))
        Bool
(= (return-Indcpamon0-red-ENCN-return-value-or-abort     state-right-NEU) (as mk-abort (ReturnValue Bits_m))))


(define-fun no-abort-SETBIT          (
        (state-left  CompositionState-Indcpamod0)
        (state-right CompositionState-Indcpamon0)
        (state-left-NEU  Return-Indcpamod0-keys_top-SETBIT)  ; also contains new index    
        (state-right-NEU Return-Indcpamon0-red-SETBIT) ; also contains new index
        (zz Bool))
        Bool

(and (not (= (return-Indcpamod0-keys_top-SETBIT-return-value-or-abort     state-left-NEU) (as mk-abort (ReturnValue Empty))))
     (not (= (return-Indcpamon0-red-SETBIT-return-value-or-abort     state-right-NEU) (as mk-abort (ReturnValue Empty))))))

(define-fun no-abort-GETAOUT          (
        (state-left  CompositionState-Indcpamod0)
        (state-right CompositionState-Indcpamon0)
        (state-left-NEU  Return-Indcpamod0-keys_top-GETAOUT)  ; also contains new index    
        (state-right-NEU Return-Indcpamon0-red-GETAOUT) ; also contains new index
        )
        Bool

(and (not (= (return-Indcpamod0-keys_top-GETAOUT-return-value-or-abort     state-left-NEU) (as mk-abort (ReturnValue Bits_n))))
     (not (= (return-Indcpamon0-red-GETAOUT-return-value-or-abort     state-right-NEU) (as mk-abort (ReturnValue Bits_n))))))


(define-fun left-abort-GETAOUT          (
        (state-left   CompositionState-Indcpamod0)
        (state-right  CompositionState-Indcpamon0)
        (state-left-NEU  Return-Indcpamod0-keys_top-GETAOUT)  ; also contains new index    
        (state-right-NEU Return-Indcpamon0-red-GETAOUT) ; also contains new index
        )
        Bool

(= (return-Indcpamod0-keys_top-GETAOUT-return-value-or-abort     state-left-NEU) (as mk-abort (ReturnValue Bits_n))))


(define-fun right-abort-GETAOUT          (
        (state-left   CompositionState-Indcpamod0)
        (state-right  CompositionState-Indcpamon0)
        (state-left-NEU  Return-Indcpamod0-keys_top-GETAOUT)  ; also contains new index    
        (state-right-NEU Return-Indcpamon0-red-GETAOUT) ; also contains new index
        )
        Bool

(= (return-Indcpamon0-red-GETAOUT-return-value-or-abort     state-right-NEU) (as mk-abort (ReturnValue Bits_n))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;    State lemmas Indcpamod0
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;    State lemmas Indcpamon0
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Same Output 
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(define-fun same-output-ENCN          (
        (state-left CompositionState-Indcpamod0)
        (state-right CompositionState-Indcpamon0)
        (state-left-NEU Return-Indcpamod0-enc-ENCN)
        (state-right-NEU Return-Indcpamon0-red-ENCN)
        (d Bool)
        (nzero Bits_n)
        (none  Bits_n))
        Bool
(=
(return-Indcpamod0-enc-ENCN-return-value-or-abort return-Indcpamod0_inst-ENCN)
(return-Indcpamon0-red-ENCN-return-value-or-abort return-Indcpamon0_inst-ENCN)
)
)


(define-fun same-output-SETBIT          (
        (state-left  CompositionState-Indcpamod0)
        (state-right CompositionState-Indcpamon0)
        (state-left-NEU Return-Indcpamod0-keys_top-SETBIT)
        (state-right-NEU Return-Indcpamon0-red-SETBIT)
        (zz Bool))
        Bool
(=
(return-Indcpamod0-keys_top-SETBIT-return-value-or-abort return-Indcpamod0_inst-SETBIT)
(return-Indcpamon0-red-SETBIT-return-value-or-abort return-Indcpamon0_inst-SETBIT)
)
)

(define-fun same-output-GETAOUT          (
        (state-left   CompositionState-Indcpamod0)
        (state-right  CompositionState-Indcpamon0)
        (state-left-NEU Return-Indcpamod0-keys_top-GETAOUT)
        (state-right-NEU Return-Indcpamon0-red-GETAOUT)
        )
        Bool
(=
(return-Indcpamod0-keys_top-GETAOUT-return-value-or-abort return-Indcpamod0_inst-GETAOUT)
(return-Indcpamon0-red-GETAOUT-return-value-or-abort return-Indcpamon0_inst-GETAOUT)
)
)
(check-sat)
(push 1)(assert (not (=> (and (forall ((randmap-sample-id-left Int)
 (randmap-sample-ctr-left Int)
 (randmap-sample-id-right Int)
 (randmap-sample-ctr-right Int)
)
 (=> (randomness-mapping-SETBIT (get-rand-ctr-Indcpamod0 randmap-sample-id-left)
 (get-rand-ctr-Indcpamon0 randmap-sample-id-right)
 randmap-sample-id-left randmap-sample-id-right randmap-sample-ctr-left randmap-sample-ctr-right)
 (rand-is-eq randmap-sample-id-left randmap-sample-id-right randmap-sample-ctr-left randmap-sample-ctr-right)
)
)
 (invariant-SETBIT game-state-Indcpamod0_inst-old game-state-Indcpamon0_inst-old)
)
 (aborts-equal-SETBIT game-state-Indcpamod0_inst-old game-state-Indcpamon0_inst-old return-Indcpamod0_inst-SETBIT return-Indcpamon0_inst-SETBIT arg-SETBIT-zz)
)
)
)
(check-sat)
(pop 1)(push 1)(assert (not (=> (and (forall ((randmap-sample-id-left Int)
 (randmap-sample-ctr-left Int)
 (randmap-sample-id-right Int)
 (randmap-sample-ctr-right Int)
)
 (=> (randomness-mapping-SETBIT (get-rand-ctr-Indcpamod0 randmap-sample-id-left)
 (get-rand-ctr-Indcpamon0 randmap-sample-id-right)
 randmap-sample-id-left randmap-sample-id-right randmap-sample-ctr-left randmap-sample-ctr-right)
 (rand-is-eq randmap-sample-id-left randmap-sample-id-right randmap-sample-ctr-left randmap-sample-ctr-right)
)
)
 (invariant-SETBIT game-state-Indcpamod0_inst-old game-state-Indcpamon0_inst-old)
 (no-abort-SETBIT game-state-Indcpamod0_inst-old game-state-Indcpamon0_inst-old return-Indcpamod0_inst-SETBIT return-Indcpamon0_inst-SETBIT arg-SETBIT-zz)
)
 (invariant-SETBIT game-state-Indcpamod0_inst-new-SETBIT game-state-Indcpamon0_inst-new-SETBIT)
)
)
)
(check-sat)
(pop 1)(push 1)(assert (not (=> (and (forall ((randmap-sample-id-left Int)
 (randmap-sample-ctr-left Int)
 (randmap-sample-id-right Int)
 (randmap-sample-ctr-right Int)
)
 (=> (randomness-mapping-SETBIT (get-rand-ctr-Indcpamod0 randmap-sample-id-left)
 (get-rand-ctr-Indcpamon0 randmap-sample-id-right)
 randmap-sample-id-left randmap-sample-id-right randmap-sample-ctr-left randmap-sample-ctr-right)
 (rand-is-eq randmap-sample-id-left randmap-sample-id-right randmap-sample-ctr-left randmap-sample-ctr-right)
)
)
 (invariant-SETBIT game-state-Indcpamod0_inst-old game-state-Indcpamon0_inst-old)
 (no-abort-SETBIT game-state-Indcpamod0_inst-old game-state-Indcpamon0_inst-old return-Indcpamod0_inst-SETBIT return-Indcpamon0_inst-SETBIT arg-SETBIT-zz)
)
 (same-output-SETBIT game-state-Indcpamod0_inst-old game-state-Indcpamon0_inst-old return-Indcpamod0_inst-SETBIT return-Indcpamon0_inst-SETBIT arg-SETBIT-zz)
)
)
)
(check-sat)
(pop 1)(pop 1)(push 1)
;;;;;;;;;;;;;;;;;
;
; left  = mod
; right = mon
;
;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;   Randomness mapping
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define-fun randomness-mapping-SETBIT (
        (ctr-mod     Int)
        (ctr-mon     Int) 
        (id-mod      Int)
        (id-mon      Int) 
        (new-mod Int)
        (new-mon Int))         
         Bool
false
)


(define-fun randomness-mapping-GETAOUT (
        (ctr-mod     Int)
        (ctr-mon     Int) 
        (id-mod      Int)
        (id-mon      Int) 
        (new-mod Int)
        (new-mon Int)) 
        Bool

;
; mon = right
; red samples with index 4 k_ ~ z
; SMP verwendet counter 1 to sample k_ ~ not z
;
; mod = left
; top key package samples r with index 1 for true
;                        rr with index 2 for false
;

(and
(=>
; if z = true
(=
; z

(state-Indcpamon0-red-z
  (composition-pkgstate-Indcpamon0-red 
    game-state-Indcpamon0_inst-old))
(mk-some true))

; then
(or

;(=  randval-left-GETA-1  ; r at true
;    randval-right-GETA-4 ; k_ at z=true
;)

(and     (= id-mod 1) 
         (= id-mon 4) 
         (= ctr-mod new-mod)
         (= ctr-mon new-mon)
)

;(=  randval-left-GETA-2 ; rr at false
;   randval-right-GETA-1 ; k_ at not z = false
;)

(and     (= id-mod 2) 
         (= id-mon 1) 
         (= ctr-mod new-mod)
         (= ctr-mon new-mon)
)))

(=>
; if z = false
(=
; z
(state-Indcpamon0-red-z
(composition-pkgstate-Indcpamon0-red
game-state-Indcpamon0_inst-old)) 
(mk-some false))

; then
(or
(and     (= id-mod 1) 
         (= id-mon 1) 
         (= ctr-mod new-mod)
         (= ctr-mod new-mod)
)
(and     (= id-mod 2) 
         (= id-mon 4) 
         (= ctr-mod new-mod)
         (= ctr-mod new-mod)
)
;(=  randval-left-GETA-1 ; r at true
;   randval-right-GETA-1 ; k_ at not z
;)
;(=  randval-left-GETA-2 ; rr at false
;   randval-right-GETA-4 ; k_ at z
;)
)
)
)
)

(define-fun randomness-mapping-GETKEYSIN (
        (ctr-mod     Int)
        (ctr-mon     Int) 
        (id-mod      Int)
        (id-mon      Int) 
        (new-mod Int)
        (new-mon Int)) 
        Bool
false
)

(define-fun randomness-mapping-ENCN (
        (ctr-mod     Int)
        (ctr-mon     Int) 
        (id-mod      Int)
        (id-mon      Int) 
        (new-mod Int)
        (new-mon Int)
) Bool
(and
(= id-mod 5)
(= id-mon 2)
(= ctr-mod new-mod)
(= ctr-mon new-mon)
))

(define-fun randomness-mapping-ENCM (
;(= randval-left-ENCN-6 randval-right-ENCN-3)
        (ctr-mod     Int)
        (ctr-mon     Int) 
        (id-mod      Int)
        (id-mon      Int) 
        (new-mod Int)
        (new-mon Int)) Bool
(and
(= id-mod 6)
(= id-mon 3)
(= ctr-mod new-mod)
(= ctr-mon new-mon)
)        
)



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;   Datatypes to extract key package state
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(declare-datatype
  State_keys
  (
    (mk-state-keys
      (state-keys-T    (Maybe (Array Bool (Maybe Bits_n))))
      (state-keys-z    (Maybe Bool))
      (state-keys-flag (Maybe Bool)))))

(define-fun project-State_Indcpamod0_keys_top ((in State_Indcpamod0_keys_top)) State_keys
  (mk-state-keys (state-Indcpamod0-keys_top-T    in)
                 (state-Indcpamod0-keys_top-z    in)
                 (state-Indcpamod0-keys_top-flag in)))



(define-fun project-keys-State_Indcpamon0_indcpamon0 ((in CompositionState-Indcpamon0)) State_keys
(let ((red-state (composition-pkgstate-Indcpamon0-red        in))
      (ind-state (composition-pkgstate-Indcpamon0-indcpamon0 in))
     )
(let ((ka    (state-Indcpamon0-red-k        red-state))
      (kina  (state-Indcpamon0-indcpamon0-k ind-state))
      (z     (state-Indcpamon0-red-z        red-state))
      (flag  (state-Indcpamon0-red-flag     red-state)))
(let ((Z (ite (or (not (= ka   (as mk-none (Maybe Bits_n))))
                  (not (= kina (as mk-none (Maybe Bits_n))))
              )
              (mk-some (store (store
                 ;initialize empty table 
                 ((as const (Array Bool (Maybe Bits_n))) (as mk-none (Maybe Bits_n))) 
                      (maybe-get z)  ka) 
                 (not (maybe-get z)) kina))
                 (as mk-none (Maybe (Array Bool (Maybe Bits_n))))
)))
     (mk-state-keys Z z flag)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;   Well-definedness of tables
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;If T h != none => T h b != none (for both b=0 and b=1)

(define-fun well-defined ((T (Maybe (Array Bool (Maybe Bits_n))))) Bool
    (or
      (= T (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
      (forall ((b Bool))
        (not
          (= (select (maybe-get T) b) (as mk-none (Maybe Bits_n))
    )
))))

; captures the possible states which a Key package can be in when
; the "top" queries are GETKEYS queries 
;
(define-fun well-defined-Key-bool ((key-state State_keys)) Bool
(let ((T    (state-keys-T    key-state))
      (flag (state-keys-flag key-state))
      (z    (state-keys-z    key-state)))

(and

; T = none or for b=0,1: T b != none
(well-defined T)

;flag is either none or true
(or
    (= flag (as mk-none (Maybe Bool)))
    (= flag (   mk-some        true)))

;flag = true <=> T != none
(=
     (= flag (mk-some true))
(not (= T (as mk-none (Maybe (Array Bool (Maybe Bits_n))))))
)

;flag = true => z != none
(=>
     (= flag (mk-some true))
(not (= z (as mk-none (Maybe Bool)))))
)

))

; captures the possible states which a Key package can be in when
; the "top" queries are GETA and SETBIT queries 
;
(define-fun well-defined-Key-active ((key-state State_keys)) Bool
(let ((T    (state-keys-T    key-state))
      (flag (state-keys-flag key-state))
      (z    (state-keys-z    key-state)))

(and

;If T h != none => T h b != none (for both b=0 and b=1)
(well-defined T)

(and
(or
  (= flag (as mk-none (Maybe Bool)))
  (= flag (   mk-some        true )))

 ;flag has been set  => bit has been set
(=> (=  (mk-some true ) flag)  
                    (or (=  (mk-some true ) z)
                        (=  (mk-some false) z)
                    ))
; key has been set => flag has been set
(=> (not            (= T (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
                    )
                    (= flag (mk-some true)))
))))

(define-fun well-defined-Key-debug ((key-state State_keys)) Bool
(let ((T    (state-keys-T    key-state))
      (flag (state-keys-flag key-state))
      (z    (state-keys-z    key-state)))

(and true

;T != none or for b=0,1 T b != none
(well-defined T)
(not (= T (as mk-none (Maybe (Array Bool (Maybe Bits_n))))))
(not (= z (as mk-none (Maybe Bool))))
(= flag (mk-some true))

)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Invariant
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun invariant-ENCN
    ((state-left CompositionState-Indcpamod0)
	 (state-right CompositionState-Indcpamon0))
    Bool
  (let ((top-key-package-left  (project-State_Indcpamod0_keys_top      (composition-pkgstate-Indcpamod0-keys_top state-left)))
        (top-key-package-right (project-keys-State_Indcpamon0_indcpamon0     state-right)))
    (and
      ;top key package states are equal
      (= top-key-package-left top-key-package-right)

      ;top key package state is "good"
      (well-defined-Key-debug top-key-package-left )
      (well-defined-Key-debug top-key-package-right)

      ;the functions left and right are the same
      (forall ((k Bits_n)(x Bits_n)(r Bits_n))
        (= (__func-Indcpamon0-encn k x r) (__func-Indcpamod0-encn  k x r))))))


;;;   (define-fun invariant-ENCN          (
;;;           (state-left  (Array Int CompositionState-Indcpamod0 ))
;;;           (state-right (Array Int CompositionState-Indcpamon0))
;;;           (state-length-left  Int) ;old index
;;;           (state-length-right Int) ;old index
;;;           (state-left-new  Return_Indcpamod0_enc_ENCN)
;;;           (state-right-new Return_Indcpamon0_red_ENCN)
;;;           (d Bool)
;;;           (nzero Bits_n)
;;;           (none  Bits_n))
;;;       Bool
;;;      (let
;;;   
;;;   ; state of the key packages
;;;   (
;;;   (top-key-package-left  (project-State_Indcpamod0_keys_top      (composition-pkgstate-Indcpamod0-keys_top     (select state-left  state-length-left))))
;;;   (top-key-package-right (project-keys-State_Indcpamon0_indcpamon0   (select state-right state-length-right)))  ;(composition-pkgstate-Indcpamon0-indcpamon0    (select state-right state-length-right))))
;;;   )
;;;   
;;;   
;;; 
;;; 
;;; 
;;; (and
;;; ;top key package states are equal
;;; (= top-key-package-left top-key-package-right)
;;; 
;;; 
;;; ;top key package state is "good"
;;; (well-defined-Key-debug top-key-package-left )
;;; (well-defined-Key-debug top-key-package-right)
;;; 
;;; ;the functions left and right are the same
;;; (forall ((k Bits_n)(x Bits_n)(r Bits_n))
;;; (= (__func-Indcpamon0-encn k x r) (__func-Indcpamod0-encn  k x r))
;;; )
;;; )))


(define-fun invariant-ENCN-post          (
        (state-left  CompositionState-Indcpamod0 )
        (state-right CompositionState-Indcpamon0)
        (state-left-new  Return-Indcpamod0-enc-ENCN)
        (state-right-new Return-Indcpamon0-red-ENCN)
        (d Bool)
        (nzero Bits_n)
        (none  Bits_n))
    Bool
(let (
      (state-left-nov  (return-Indcpamod0-enc-ENCN-game-state    state-left-new))
      (state-right-nov (return-Indcpamon0-red-ENCN-game-state        state-right-new))
     )

    (let

; state of the key packages
(
(top-key-package-left  (project-State_Indcpamod0_keys_top      (composition-pkgstate-Indcpamod0-keys_top     state-left-nov  )))
(top-key-package-right (project-keys-State_Indcpamon0_indcpamon0  state-right-nov )))   ; ((;;(composition-pkgstate-Indcpamon0-indcpamon0    state-right-nov )))

(and
;top key package states are equal
(= top-key-package-left top-key-package-right)


;top key package state is "good"
(  well-defined-Key-active top-key-package-left )
(  well-defined-Key-active top-key-package-right)
))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Invariant stuff
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define-fun invariant-SETBIT      (
        (state-left  CompositionState-Indcpamod0 )
        (state-right CompositionState-Indcpamon0)
)
    Bool
    (let

; state of the key packages
(
(top-key-package-left  (project-State_Indcpamod0_keys_top      (composition-pkgstate-Indcpamod0-keys_top     state-left )))
(top-key-package-right (project-keys-State_Indcpamon0_indcpamon0   state-right ))  ;((;;(composition-pkgstate-Indcpamon0-indcpamon0    (select state-right state-length-right))))
)

(and
;top key package states are equal
(= top-key-package-left top-key-package-right)


;top key package state is "good"
(well-defined-Key-active top-key-package-left )
(well-defined-Key-active top-key-package-right)

)))




(define-fun invariant-GETAOUT      (
        (state-left  CompositionState-Indcpamod0 )
        (state-right CompositionState-Indcpamon0)
        ;(state-left-new  Return-Indcpamod0-keys_top-GETAOUT)
        ;(state-right-new Return-Indcpamon0-red-GETAOUT)
        )
    Bool
    (let

; state of the key packages
(
(top-key-package-left  (project-State_Indcpamod0_keys_top      (composition-pkgstate-Indcpamod0-keys_top      state-left )))
(top-key-package-right (project-keys-State_Indcpamon0_indcpamon0  state-right )) ;  (((composition-pkgstate-Indcpamon0-indcpamon0    (select state-right state-length-right))))
)

(and
;top key package states are equal
(= top-key-package-left top-key-package-right)


;top key package state is "good"
(well-defined-Key-active top-key-package-left )
(well-defined-Key-active top-key-package-right)

)))







;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;    aborts equal
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun aborts-equal-ENCN          (
        (state-left  CompositionState-Indcpamod0)
        (state-right CompositionState-Indcpamon0)
        (state-left-NEU Return-Indcpamod0-enc-ENCN)      ; also contains new index    
        (state-right-NEU Return-Indcpamon0-red-ENCN) ; also contains new index
        (d Bool)
        (nzero Bits_n)
        (none  Bits_n))
        Bool


(= (= (return-Indcpamod0-enc-ENCN-return-value-or-abort     state-left-NEU) (as mk-abort (ReturnValue Bits_m)))
   (= (return-Indcpamon0-red-ENCN-return-value-or-abort     state-right-NEU) (as mk-abort (ReturnValue Bits_m)))))



(define-fun aborts-equal-SETBIT          (
        (state-left  CompositionState-Indcpamod0)
        (state-right CompositionState-Indcpamon0)
        (state-left-NEU Return-Indcpamod0-keys_top-SETBIT)      ; also contains new index    
        (state-right-NEU Return-Indcpamon0-red-SETBIT) ; also contains new index
        (zz Bool))
        Bool


(= (= (return-Indcpamod0-keys_top-SETBIT-return-value-or-abort     state-left-NEU) (as mk-abort (ReturnValue Empty)))
   (= (return-Indcpamon0-red-SETBIT-return-value-or-abort     state-right-NEU) (as mk-abort (ReturnValue Empty)))))

(define-fun aborts-equal-GETAOUT          (
        (state-left  CompositionState-Indcpamod0)
        (state-right CompositionState-Indcpamon0)
        (state-left-NEU Return-Indcpamod0-keys_top-GETAOUT)      ; also contains new index    
        (state-right-NEU Return-Indcpamon0-red-GETAOUT)          ; also contains new index
        )
        Bool



(= (= (return-Indcpamod0-keys_top-GETAOUT-return-value-or-abort     state-left-NEU) (as mk-abort (ReturnValue Bits_n)))
   (= (return-Indcpamon0-red-GETAOUT-return-value-or-abort     state-right-NEU) (as mk-abort (ReturnValue Bits_n)))))



; no-abort

(define-fun no-abort-ENCN          (
        (state-left  CompositionState-Indcpamod0)
        (state-right CompositionState-Indcpamon0)
        (state-left-NEU  Return-Indcpamod0-enc-ENCN)  ; also contains new index    
        (state-right-NEU Return-Indcpamon0-red-ENCN) ; also contains new index
        (d Bool)
        (nzero Bits_n)
        (none  Bits_n))
        Bool


(and (not (= (return-Indcpamod0-enc-ENCN-return-value-or-abort     state-left-NEU) (as mk-abort (ReturnValue Bits_m))))
     (not (= (return-Indcpamon0-red-ENCN-return-value-or-abort     state-right-NEU) (as mk-abort (ReturnValue Bits_m))))))


(define-fun left-abort-ENCN          (
        (state-left   CompositionState-Indcpamod0)
        (state-right  CompositionState-Indcpamon0)
        (state-left-NEU  Return-Indcpamod0-enc-ENCN)  ; also contains new index    
        (state-right-NEU Return-Indcpamon0-red-ENCN) ; also contains new index
        (d Bool)
        (nzero Bits_n)
        (none  Bits_n))
        Bool

(= (return-Indcpamod0-enc-ENCN-return-value-or-abort     state-left-NEU) (as mk-abort (ReturnValue Bits_m))))

(define-fun right-abort-ENCN          (
        (state-left  CompositionState-Indcpamod0)
        (state-right CompositionState-Indcpamon0)
        (state-left-NEU  Return-Indcpamod0-enc-ENCN)  ; also contains new index    
        (state-right-NEU Return-Indcpamon0-red-ENCN) ; also contains new index
        (d Bool)
        (nzero Bits_n)
        (none  Bits_n))
        Bool
(= (return-Indcpamon0-red-ENCN-return-value-or-abort     state-right-NEU) (as mk-abort (ReturnValue Bits_m))))


(define-fun no-abort-SETBIT          (
        (state-left  CompositionState-Indcpamod0)
        (state-right CompositionState-Indcpamon0)
        (state-left-NEU  Return-Indcpamod0-keys_top-SETBIT)  ; also contains new index    
        (state-right-NEU Return-Indcpamon0-red-SETBIT) ; also contains new index
        (zz Bool))
        Bool

(and (not (= (return-Indcpamod0-keys_top-SETBIT-return-value-or-abort     state-left-NEU) (as mk-abort (ReturnValue Empty))))
     (not (= (return-Indcpamon0-red-SETBIT-return-value-or-abort     state-right-NEU) (as mk-abort (ReturnValue Empty))))))

(define-fun no-abort-GETAOUT          (
        (state-left  CompositionState-Indcpamod0)
        (state-right CompositionState-Indcpamon0)
        (state-left-NEU  Return-Indcpamod0-keys_top-GETAOUT)  ; also contains new index    
        (state-right-NEU Return-Indcpamon0-red-GETAOUT) ; also contains new index
        )
        Bool

(and (not (= (return-Indcpamod0-keys_top-GETAOUT-return-value-or-abort     state-left-NEU) (as mk-abort (ReturnValue Bits_n))))
     (not (= (return-Indcpamon0-red-GETAOUT-return-value-or-abort     state-right-NEU) (as mk-abort (ReturnValue Bits_n))))))


(define-fun left-abort-GETAOUT          (
        (state-left   CompositionState-Indcpamod0)
        (state-right  CompositionState-Indcpamon0)
        (state-left-NEU  Return-Indcpamod0-keys_top-GETAOUT)  ; also contains new index    
        (state-right-NEU Return-Indcpamon0-red-GETAOUT) ; also contains new index
        )
        Bool

(= (return-Indcpamod0-keys_top-GETAOUT-return-value-or-abort     state-left-NEU) (as mk-abort (ReturnValue Bits_n))))


(define-fun right-abort-GETAOUT          (
        (state-left   CompositionState-Indcpamod0)
        (state-right  CompositionState-Indcpamon0)
        (state-left-NEU  Return-Indcpamod0-keys_top-GETAOUT)  ; also contains new index    
        (state-right-NEU Return-Indcpamon0-red-GETAOUT) ; also contains new index
        )
        Bool

(= (return-Indcpamon0-red-GETAOUT-return-value-or-abort     state-right-NEU) (as mk-abort (ReturnValue Bits_n))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;    State lemmas Indcpamod0
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;    State lemmas Indcpamon0
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Same Output 
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(define-fun same-output-ENCN          (
        (state-left CompositionState-Indcpamod0)
        (state-right CompositionState-Indcpamon0)
        (state-left-NEU Return-Indcpamod0-enc-ENCN)
        (state-right-NEU Return-Indcpamon0-red-ENCN)
        (d Bool)
        (nzero Bits_n)
        (none  Bits_n))
        Bool
(=
(return-Indcpamod0-enc-ENCN-return-value-or-abort return-Indcpamod0_inst-ENCN)
(return-Indcpamon0-red-ENCN-return-value-or-abort return-Indcpamon0_inst-ENCN)
)
)


(define-fun same-output-SETBIT          (
        (state-left  CompositionState-Indcpamod0)
        (state-right CompositionState-Indcpamon0)
        (state-left-NEU Return-Indcpamod0-keys_top-SETBIT)
        (state-right-NEU Return-Indcpamon0-red-SETBIT)
        (zz Bool))
        Bool
(=
(return-Indcpamod0-keys_top-SETBIT-return-value-or-abort return-Indcpamod0_inst-SETBIT)
(return-Indcpamon0-red-SETBIT-return-value-or-abort return-Indcpamon0_inst-SETBIT)
)
)

(define-fun same-output-GETAOUT          (
        (state-left   CompositionState-Indcpamod0)
        (state-right  CompositionState-Indcpamon0)
        (state-left-NEU Return-Indcpamod0-keys_top-GETAOUT)
        (state-right-NEU Return-Indcpamon0-red-GETAOUT)
        )
        Bool
(=
(return-Indcpamod0-keys_top-GETAOUT-return-value-or-abort return-Indcpamod0_inst-GETAOUT)
(return-Indcpamon0-red-GETAOUT-return-value-or-abort return-Indcpamon0_inst-GETAOUT)
)
)
(check-sat)
(push 1)(assert (not (=> (and (forall ((randmap-sample-id-left Int)
 (randmap-sample-ctr-left Int)
 (randmap-sample-id-right Int)
 (randmap-sample-ctr-right Int)
)
 (=> (randomness-mapping-ENCN (get-rand-ctr-Indcpamod0 randmap-sample-id-left)
 (get-rand-ctr-Indcpamon0 randmap-sample-id-right)
 randmap-sample-id-left randmap-sample-id-right randmap-sample-ctr-left randmap-sample-ctr-right)
 (rand-is-eq randmap-sample-id-left randmap-sample-id-right randmap-sample-ctr-left randmap-sample-ctr-right)
)
)
 (invariant-ENCN game-state-Indcpamod0_inst-old game-state-Indcpamon0_inst-old)
 (no-abort-ENCN game-state-Indcpamod0_inst-old game-state-Indcpamon0_inst-old return-Indcpamod0_inst-ENCN return-Indcpamon0_inst-ENCN arg-ENCN-d arg-ENCN-nzero arg-ENCN-none)
)
 (same-output-ENCN game-state-Indcpamod0_inst-old game-state-Indcpamon0_inst-old return-Indcpamod0_inst-ENCN return-Indcpamon0_inst-ENCN arg-ENCN-d arg-ENCN-nzero arg-ENCN-none)
)
)
)
(check-sat)
