; DH (Gks0) = Z

(assert 
    (= 
        (<<func-proof-log_package_parameters>> 0 true false false false) ; Gks0 is 0, is_dh = true, is_psk = is_internal = is_output = false
        (mk-tuple2 0 0) ; pattern = 0 (Z) and mapping = 0
    )
)

; DH (Gks0Map) = Zinf

(assert 
    (= 
        (<<func-proof-log_package_parameters>> 1 true false false false) ; Gks0Map is 1, is_dh = true, is_psk = is_internal = is_output = false
        (mk-tuple2 0 2) ; pattern = 0 (Z) and mapping = infinity
    )
)

; PSK (Gks0) = A

(assert 
    (= 
        (<<func-proof-log_package_parameters>> 0 false true false false) ; Gks0 is 0, is_dh = false, is_psk = true, is_internal = is_output = false
        (mk-tuple2 1 0) ; pattern = 1 (A) and mapping = 0
    )
)

; PSK (Gks0Map) = A1

(assert 
    (= 
        (<<func-proof-log_package_parameters>> 1 false true false false) ; Gks0Map is 1, is_dh = false, is_psk = true, is_internal = is_output = false
        (mk-tuple2 1 1) ; pattern = 1 (A) and mapping = 1
    )
)

; Internal keys (Gks0) = Z

(assert 
    (= 
        (<<func-proof-log_package_parameters>> 0 false false true false) ; Gks0 is 0, is_dh = false, is_psk = false, is_internal = true, is_output = false
        (mk-tuple2 0 0) ; pattern = 0 (Z) and mapping = 0
    )
)

; Internal keys (Gks0Map) = Z

(assert 
    (= 
        (<<func-proof-log_package_parameters>> 1 false false true false) ; Gks0Map is 1, is_dh = false, is_psk = false, is_internal = true, is_output = false
        (mk-tuple2 0 0) ; pattern = 0 (Z) and mapping = 0
    )
)

; Output keys (Gks0) = Z

(assert 
    (= 
        (<<func-proof-log_package_parameters>> 0 false false false true) ; Gks0 is 0, is_dh = false, is_psk = false, is_internal = false, is_output = true
        (mk-tuple2 0 0) ; pattern = 0 (Z) and mapping = 0
    )
)

; Output keys (Gks0Map) = Z

(assert 
    (= 
        (<<func-proof-log_package_parameters>> 1 false false false true) ; Gks0Map is 1, is_dh = false, is_psk = false, is_internal = false, is_output = true
        (mk-tuple2 0 0) ; pattern = 0 (Z) and mapping = 0
    )
)

; (forall ((X Bits_*) (Y Bits_*)) (= (type (mk_dh_handle X Y)) 1)) gives unknown
(assert
    (= 
        (<<func-proof-type>> (<<func-proof-mk_dh_handle>> <arg-DHEXP-X> <arg-DHEXP-Y>))
        1
    )
)

(declare-const KEY_psk Int)(assert (= KEY_psk 0))(assert (= (<<func-proof-get_psk>> 0) 0))
(declare-const KEY_hs Int)(assert (= KEY_hs 1))(assert (= (<<func-proof-get_hs>> 0) 1))
(declare-const KEY_es Int)(assert (= KEY_es 2))(assert (= (<<func-proof-get_es>> 0) 2))
(declare-const KEY_as Int)(assert (= KEY_as 3))(assert (= (<<func-proof-get_as>> 0) 3))
(declare-const KEY_rm Int)(assert (= KEY_rm 4))(assert (= (<<func-proof-get_rm>> 0) 4))
(declare-const KEY_esalt Int)(assert (= KEY_esalt 5))(assert (= (<<func-proof-get_esalt>> 0) 5))
(declare-const KEY_hsalt Int)(assert (= KEY_hsalt 6))(assert (= (<<func-proof-get_hsalt>> 0) 6))
(declare-const KEY_bind Int)(assert (= KEY_bind 7))(assert (= (<<func-proof-get_bind>> 0) 7))
(declare-const KEY_binder Int)(assert (= KEY_binder 8))(assert (= (<<func-proof-get_binder>> 0) 8))
(declare-const KEY_eem Int)(assert (= KEY_eem 9))(assert (= (<<func-proof-get_eem>> 0) 9))
(declare-const KEY_cet Int)(assert (= KEY_cet 10))(assert (= (<<func-proof-get_cet>> 0) 10))
(declare-const KEY_sht Int)(assert (= KEY_sht 11))(assert (= (<<func-proof-get_sht>> 0) 11))
(declare-const KEY_cht Int)(assert (= KEY_cht 12))(assert (= (<<func-proof-get_cht>> 0) 12))
(declare-const KEY_cat Int)(assert (= KEY_cat 13))(assert (= (<<func-proof-get_cat>> 0) 13))
(declare-const KEY_sat Int)(assert (= KEY_sat 14))(assert (= (<<func-proof-get_sat>> 0) 14))
(declare-const KEY_eam Int)(assert (= KEY_eam 15))(assert (= (<<func-proof-get_eam>> 0) 15))
(declare-const KEY_dh Int)(assert (= KEY_dh 16))(assert (= (<<func-proof-get_dh>> 0) 16))
(declare-const KEY_0ikm Int)(assert (= KEY_0ikm 17))(assert (= (<<func-proof-get_0ikm>> 0) 17))
(declare-const KEY_0salt Int)(assert (= KEY_0salt 18))(assert (= (<<func-proof-get_0salt>> 0) 18))

; TLS-like key schedule syntax concrete parents
; specifies base keys (dh, 0salt, 0ikm)
; specifies xtr keys (es, hs, as)
; specifies parent of psk
; considers psk as the root key from which all keys except base keys are derived

(assert 
    (=
        (<<func-proof-parents>> KEY_hs)
        (mk-tuple2 (mk-some KEY_esalt) (mk-some KEY_dh))
    )
)

(assert 
    (=
        (<<func-proof-parents>> KEY_es)
        (mk-tuple2 (mk-some KEY_0salt) (mk-some KEY_psk))
    )
)

(assert 
    (=
        (<<func-proof-parents>> KEY_as)
        (mk-tuple2 (mk-some KEY_hsalt) (mk-some KEY_0ikm))
    )
)

(assert 
    (=
        (<<func-proof-parents>> KEY_psk)
        (mk-tuple2 (mk-some KEY_rm) (as mk-none (Maybe Int)))
    )
)

(assert 
    (=
        (<<func-proof-parents>> KEY_dh)
        (mk-tuple2 (as mk-none (Maybe Int)) (as mk-none (Maybe Int)))
    )
)

(assert 
    (=
        (<<func-proof-parents>> KEY_0ikm)
        (mk-tuple2 (as mk-none (Maybe Int)) (as mk-none (Maybe Int)))
    )
)

(assert 
    (=
        (<<func-proof-parents>> KEY_0salt)
        (mk-tuple2 (as mk-none (Maybe Int)) (as mk-none (Maybe Int)))
    )
)

; TLS-like key schedule syntax ther rules:
; 1. should have only one loop containing psk modelign resumption
; 2. other keys have only one parent (xpd keys)

(assert 
    (=
        (<<func-proof-parents>> KEY_rm)
        (mk-tuple2 (mk-some KEY_as) (as mk-none (Maybe Int)))
    )
)

(assert 
    (=
        (<<func-proof-parents>> KEY_esalt)
        (mk-tuple2 (mk-some KEY_es) (as mk-none (Maybe Int)))
    )
)

(assert 
    (=
        (<<func-proof-parents>> KEY_hsalt)
        (mk-tuple2 (mk-some KEY_hs) (as mk-none (Maybe Int)))
    )
)

(assert 
    (=
        (<<func-proof-parents>> KEY_bind)
        (mk-tuple2 (mk-some KEY_es) (as mk-none (Maybe Int)))
    )
)

(assert 
    (=
        (<<func-proof-parents>> KEY_binder)
        (mk-tuple2 (mk-some KEY_bind) (as mk-none (Maybe Int)))
    )
)

(assert 
    (=
        (<<func-proof-parents>> KEY_eem)
        (mk-tuple2 (mk-some KEY_es) (as mk-none (Maybe Int)))
    )
)

(assert 
    (=
        (<<func-proof-parents>> KEY_cet)
        (mk-tuple2 (mk-some KEY_es) (as mk-none (Maybe Int)))
    )
)

(assert 
    (=
        (<<func-proof-parents>> KEY_sht)
        (mk-tuple2 (mk-some KEY_hs) (as mk-none (Maybe Int)))
    )
)

(assert 
    (=
        (<<func-proof-parents>> KEY_cht)
        (mk-tuple2 (mk-some KEY_hs) (as mk-none (Maybe Int)))
    )
)

(assert 
    (=
        (<<func-proof-parents>> KEY_cat)
        (mk-tuple2 (mk-some KEY_as) (as mk-none (Maybe Int)))
    )
)

(assert 
    (=
        (<<func-proof-parents>> KEY_sat)
        (mk-tuple2 (mk-some KEY_as) (as mk-none (Maybe Int)))
    )
)

(assert 
    (=
        (<<func-proof-parents>> KEY_eam)
        (mk-tuple2 (mk-some KEY_as) (as mk-none (Maybe Int)))
    )
)