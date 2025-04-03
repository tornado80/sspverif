(assert 
    (= 
        (<<func-proof-log_package_parameters>> 0 true false false false) ; Gks0 is 0, is_dh = true, is_psk = is_internal = is_output = false
        (mk-tuple2 0 0) ; pattern = 0 (Z) and mapping = 0
    )
)

(assert 
    (= 
        (<<func-proof-log_package_parameters>> 1 true false false false) ; Gks0Map is 1, is_dh = true, is_psk = is_internal = is_output = false
        (mk-tuple2 0 2) ; pattern = 0 (Z) and mapping = infinity
    )
)

(assert 
    (= 
        (<<func-proof-log_package_parameters>> 0 false true false false) ; Gks0 is 0, is_dh = false, is_psk = true, is_internal = is_output = false
        (mk-tuple2 1 0) ; pattern = 1 (A) and mapping = 0
    )
)

(assert 
    (= 
        (<<func-proof-log_package_parameters>> 1 false true false false) ; Gks0Map is 1, is_dh = false, is_psk = true, is_internal = is_output = false
        (mk-tuple2 1 1) ; pattern = 1 (A) and mapping = 1
    )
)