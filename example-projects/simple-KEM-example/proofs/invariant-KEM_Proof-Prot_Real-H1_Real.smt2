(define-fun invariant ( 
  (prot    <GameState_Prot_<$<!false!>$>>)
  (h1      <GameState_H1_<$<!false!>$>>)
) Bool
; BEGIN FUNCTION BODY
  (let 
    (
      (prot.prot   (<game-Prot-<$<!false!>$>-pkgstate-Prot>   prot    ))
      (h1.corr_kem (<game-H1-<$<!false!>$>-pkgstate-Corr_KEM> h1      ))
      (h1.corr_red (<game-H1-<$<!false!>$>-pkgstate-Corr_reduction> h1))
    )
    ; BEGIN LET DEFINITION USAGE
    (and 
      (= (<pkg-state-Prot-<$<!isideal!>$>-SENTCTXT>           prot.prot)
         (<pkg-state-Corr_reduction-<$<!isideal!>$>-SENTCTXT> h1.corr_red))
      (= (<pkg-state-Prot-<$<!isideal!>$>-SENTKEY>            prot.prot)
         (<pkg-state-Corr_reduction-<$<!isideal!>$>-SENTKEY>  h1.corr_red))
      (= (<pkg-state-Prot-<$<!isideal!>$>-RECEIVEDCTXT>       prot.prot)
         (<pkg-state-Corr_reduction-<$<!isideal!>$>-RECEIVEDCTXT> h1.corr_red))
      (= (<pkg-state-Prot-<$<!isideal!>$>-RECEIVEDKEY>        prot.prot)
         (<pkg-state-Corr_reduction-<$<!isideal!>$>-RECEIVEDKEY> h1.corr_red))
      (= (<pkg-state-Prot-<$<!isideal!>$>-TESTED>             prot.prot)
         (<pkg-state-Corr_reduction-<$<!isideal!>$>-TESTED>   h1.corr_red))
      (= (<pkg-state-Prot-<$<!isideal!>$>-ctr>                prot.prot)
         (<pkg-state-Corr_reduction-<$<!isideal!>$>-ctr>      h1.corr_red))
      (= (<pkg-state-Prot-<$<!isideal!>$>-sk>                 prot.prot)
         (<pkg-state-Corr_KEM-<$<!isideal!>$>-sk>             h1.corr_kem))
      (= (<pkg-state-Prot-<$<!isideal!>$>-pk>                 prot.prot)
         (<pkg-state-Corr_KEM-<$<!isideal!>$>-pk>             h1.corr_kem))
    )
  )
)




























  ; <game-Prot-<$<!false!>$>-pkgstate-Prot>
  ;   <pkg-state-Prot-<$<!isideal!>$>-SENTCTXT>
  ;   <pkg-state-Prot-<$<!isideal!>$>-SENTKEY>
  ;   <pkg-state-Prot-<$<!isideal!>$>-RECEIVEDCTXT>
  ;   <pkg-state-Prot-<$<!isideal!>$>-RECEIVEDKEY>
  ;   <pkg-state-Prot-<$<!isideal!>$>-TESTED>
  ;   <pkg-state-Prot-<$<!isideal!>$>-ctr>
  ;   <pkg-state-Prot-<$<!isideal!>$>-sk>
  ;   <pkg-state-Prot-<$<!isideal!>$>-pk>

  ; <game-H1-<$<!false!>$>-pkgstate-Corr_KEM>
  ;   <pkg-state-Corr_KEM-<$<!isideal!>$>-sk>
  ;   <pkg-state-Corr_KEM-<$<!isideal!>$>-pk>

  ; <game-H1-<$<!false!>$>-pkgstate-Corr_reduction>
  ;   <pkg-state-Corr_reduction-<$<!isideal!>$>-SENTCTXT>
  ;   <pkg-state-Corr_reduction-<$<!isideal!>$>-SENTKEY>
  ;   <pkg-state-Corr_reduction-<$<!isideal!>$>-RECEIVEDCTXT>
  ;   <pkg-state-Corr_reduction-<$<!isideal!>$>-RECEIVEDKEY>
  ;   <pkg-state-Corr_reduction-<$<!isideal!>$>-TESTED>
  ;   <pkg-state-Corr_reduction-<$<!isideal!>$>-ctr>













  ; State of Prot/Prot
;          SENTCTXT:     Table(Integer, Bits(256)),    /* administrative kid -> ctxt   */
;          SENTKEY:      Table(Integer, Bits(256)),    /* administrative kid -> k      */
;          RECEIVEDCTXT: Table(Integer, Bits(256)),    /* administrative kid -> k      */
;          RECEIVEDKEY:  Table(Integer, Bits(256)),    /* administrative kid -> k      */
;          TESTED:       Table(Integer,Bool),          /* has the key been tested      */
;          ctr:          Integer,                      /* administrative ctr           */
;          sk:           Maybe(Bits(256)),             /* long-term sk                 */
;          pk:           Bits(256),                    /* long-term pk                 */
  ; State of H1/Corr_KEM
;    state {
;          sk:          Maybe(Bits(256)),             /* long-term sk             */
;          pk:          Bits(256),                    /* long-term pk             */
;          }
  ; State of H1/Corr_reduction
;    state {
;          SENTCTXT:     Table(Integer, Bits(256)),    /* administrative kid -> ctxt   */
;          SENTKEY:      Table(Integer, Bits(256)),    /* administrative kid -> k      */
;          RECEIVEDCTXT: Table(Integer, Bits(256)),    /* administrative kid -> k      */
;          RECEIVEDKEY:  Table(Integer, Bits(256)),    /* administrative kid -> k      */
;          TESTED:       Table(Integer,Bool),          /* has the key been tested      */
;          ctr:          Integer,                      /* administrative ctr           */
;    }

  ; getting package-state out of game-state and demanding equality, they should be exactly the same in this case.
; (=
; (<game-KX-<$<!n!><!b!><!zeron!>$>-pkgstate-Game>     state-kx)         ;some params are still missing.
; (<game-H1-<$<!n!><!b!><!false!><!zeron!>$>-pkgstate-Game> state-kxred) ;some params are still missing.
; )
;  (let
;    ; getting ctr out of state
;    ( (ctr-kxred (<pkg-state-Rand-<$<!n!>$>-ctr> (<game-SmallComposition-<$<!n!>$>-pkgstate-rand> state-0)))
;      (ctr-kx (<pkg-state-Rand-<$<!n!>$>-ctr> (<game-MediumComposition-<$<!n!>$>-pkgstate-rand> state-1))))
;
;    ; ctr are equal
;    (= ctr-kxred ctr-kx))
