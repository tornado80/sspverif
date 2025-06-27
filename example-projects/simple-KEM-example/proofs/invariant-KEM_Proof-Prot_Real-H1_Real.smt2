(define-fun invariant ( 
  (prot    <GameState_Prot_<$<!isideal_kem_cpa_security!>$>>)
  (h1      <GameState_H1_<$<!isideal_kem_cpa_security!><!false!>$>>)
) Bool
; BEGIN FUNCTION BODY
  (let 
    (
      (prot.prot   (<game-Prot-<$<!isideal_kem_cpa_security!>$>-pkgstate-Prot>   prot    ))
      (h1.corr_kem (<game-H1-<$<!isideal_kem_cpa_security!><!false!>$>-pkgstate-Corr_KEM> h1      ))
      (h1.corr_red (<game-H1-<$<!isideal_kem_cpa_security!><!false!>$>-pkgstate-Corr_reduction> h1))
    )
    ; BEGIN LET DEFINITION USAGE
    (and 
      (= (<pkg-state-Prot-<$<!isideal_kem_cpa_security!>$>-SENTCTXT>           prot.prot)
         (<pkg-state-Corr_reduction-<$<!isideal_kem_cpa_security!>$>-SENTCTXT> h1.corr_red))
      (= (<pkg-state-Prot-<$<!isideal_kem_cpa_security!>$>-SENTKEY>            prot.prot)
         (<pkg-state-Corr_reduction-<$<!isideal_kem_cpa_security!>$>-SENTKEY>  h1.corr_red))
      (= (<pkg-state-Prot-<$<!isideal_kem_cpa_security!>$>-RECEIVEDCTXT>       prot.prot)
         (<pkg-state-Corr_reduction-<$<!isideal_kem_cpa_security!>$>-RECEIVEDCTXT> h1.corr_red))
      (= (<pkg-state-Prot-<$<!isideal_kem_cpa_security!>$>-RECEIVEDKEY>        prot.prot)
         (<pkg-state-Corr_reduction-<$<!isideal_kem_cpa_security!>$>-RECEIVEDKEY> h1.corr_red))
      (= (<pkg-state-Prot-<$<!isideal_kem_cpa_security!>$>-TESTED>             prot.prot)
         (<pkg-state-Corr_reduction-<$<!isideal_kem_cpa_security!>$>-TESTED>   h1.corr_red))
      (= (<pkg-state-Prot-<$<!isideal_kem_cpa_security!>$>-ctr>                prot.prot)
         (<pkg-state-Corr_reduction-<$<!isideal_kem_cpa_security!>$>-ctr>      h1.corr_red))
      (= (<pkg-state-Prot-<$<!isideal_kem_cpa_security!>$>-sk>                 prot.prot)
         (<pkg-state-Corr_KEM-<$<!isideal_kem_correctness!>$>-sk>             h1.corr_kem))
      (= (<pkg-state-Prot-<$<!isideal_kem_cpa_security!>$>-pk>                 prot.prot)
         (<pkg-state-Corr_KEM-<$<!isideal_kem_correctness!>$>-pk>             h1.corr_kem))
    )
  )
)

; Each sample operation is fully indexec by the pair (statement id, sample counter)
; "stmt" – Each instructions containing a sampling operation in the game is assigned a statement id number; check the generated latex code for the proof (not games/compositions or packages) to find the statement ids.
; "ctr" – Each sample operation also has a counter
; "base-ctr" – Additionally, we are given a zero-counter; this is useful if we want to compute offsets
;
; These indices are given for both games; the game on the left and the game on the right.
(define-fun randomness-mapping-GetPK (
  (base-ctr-left Int) 
  (base-ctr-right Int)
  (stmt-left  Int) 
  (stmt-right  Int)
  (ctr-left Int)
  (ctr-right Int)
) Bool
; BEGIN FUNCTION BODY
  (and
    (= stmt-left stmt-right)
    (= (- ctr-left base-ctr-left) (- ctr-right base-ctr-right))
  )
)

(define-fun randomness-mapping-Run (
  (base-ctr-left Int) 
  (base-ctr-right Int)
  (stmt-left  Int) 
  (stmt-right  Int)
  (ctr-left Int)
  (ctr-right Int)
) Bool
; BEGIN FUNCTION BODY
  (and
    (= stmt-left stmt-right)
    (= (- ctr-left base-ctr-left) (- ctr-right base-ctr-right))
  )
)

(define-fun randomness-mapping-TestSender (
  (base-ctr-left Int) 
  (base-ctr-right Int)
  (stmt-left  Int) 
  (stmt-right  Int)
  (ctr-left Int)
  (ctr-right Int)
) Bool
; BEGIN FUNCTION BODY
  (and
    (= stmt-left stmt-right)
    (= (- ctr-left base-ctr-left) (- ctr-right base-ctr-right))
  )
)

(define-fun randomness-mapping-TestReceiver (
  (base-ctr-left Int) 
  (base-ctr-right Int)
  (stmt-left  Int) 
  (stmt-right  Int)
  (ctr-left Int)
  (ctr-right Int)
) Bool
; BEGIN FUNCTION BODY
  (and
    (= stmt-left stmt-right)
    (= (- ctr-left base-ctr-left) (- ctr-right base-ctr-right))
  )
)
