#lang racket
(require redex)

(define-language patina
  ;;;; names for things
  ;; α-convertible
  ; variables
  (x variable-not-otherwise-mentioned)
  ;; non α-convertible

  ;; types
  (τ int      ; integers
     )

  ;;;; declarations
  ;; variables
  (vd (x : τ))

  ;;;; values
  (ℤ integer)


  ;; lvalues - assignable places
  (lv x       ; variable
      )

  ;; rvalues - result producing expressions
  (rv ℤ           ; integer constants
      (lv + lv)   ; addition
      )

  ;; statements - things that only alter the heap
  (st (lv = rv)      ; assignment
      (delete lv)    ; shallow destruction
      blk	     ; nested blocks
      )

  ;; block - extend context and execute a sequence of statements (TODO fresh lifetime)
  (blk (block (vd ...) (st ...)))

  ;;;; contexts for type checking
  (γ (x τ))
  (Γ (γ ...))

  )

'Γ-extend
(define-metafunction
  patina
  Γ-extend : Γ vd -> Γ
  [(Γ-extend (γ ...) (x : τ)) ((x τ) γ ...)]
  )

(test-equal
  (term (Γ-extend () (x : int)))
  (term ((x int))))
(test-results)

'Γ-extend-many
(define-metafunction
  patina
  Γ-extend-many : Γ (vd ...) -> Γ
  [(Γ-extend-many Γ ()) Γ]
  [(Γ-extend-many Γ (vd_0 vd_1 ...)) (Γ-extend-many (Γ-extend Γ vd_0) (vd_1 ...))]
  )

(test-equal
  (term (Γ-extend-many () ((x : int) (y : int) (z : int) (x : int))))
  (term ((x int) (z int) (y int) (x int))))
(test-results)

'x-≠
(define-judgment-form
  patina
  #:mode (x-≠ I I)
  #:contract (x-≠ x x)
  [------------------- "x-≠"
   (x-≠ x_!_0 x_!_0)
   ]
  )

(test-equal #t (judgment-holds (x-≠ x y)))
(test-equal #f (judgment-holds (x-≠ x x)))
(test-results)

'Γ-use
(define-judgment-form
  patina
  #:mode (Γ-use I I O)
  #:contract (Γ-use Γ x Γ)
  [------------------------- "Γ-use-here"
   (Γ-use ((x_0 τ) γ ...) x_0 (γ ...))
   ]
  [(Γ-use (γ ...) x_1 Γ_1) (x-≠ x_0 x_1)
   --------------------------------- "Γ-use-there"
   (Γ-use ((x_0 τ) γ ...) x_1 Γ_1)
   ]
  )

(test-equal
  (judgment-holds 
    (Γ-use ((x int)) x Γ)
    Γ)
  '(()))
(test-equal
  (judgment-holds 
    (Γ-use ((x int) (x int)) x Γ)
    Γ)
  '(((x int))))
(test-equal
  (judgment-holds
    (Γ-use ((y int)) x Γ)
    Γ)
  '())
(test-equal
  (judgment-holds
    (Γ-use () x Γ)
    Γ)
  '())
(test-results)

'Γ-get
(define-judgment-form
  patina
  #:mode (Γ-get I I O)
  #:contract (Γ-get Γ x τ)
  [----------------------------- "Γ-get-here"
   (Γ-get ((x_0 τ) γ ...) x_0 τ)
   ]
  [(Γ-get (γ ...) x_1 τ_1) 
   --------------------------------- "Γ-get-there"
   (Γ-get ((x_0 τ_0) γ ...) x_1 τ_1)
   ]
  )

(test-equal
  (judgment-holds
    (Γ-get ((x int)) x τ)
    τ)
  '(int))
(test-equal
  (judgment-holds
    (Γ-get ((y int) (x int)) x τ)
    τ)
  '(int))
(test-equal
  (judgment-holds
    (Γ-get () x τ)
    τ)
  '())
(test-results)


'τ-=
(define-judgment-form
  patina
  #:mode (τ-= I I)
  #:contract (τ-= τ τ)
  [------------- "τ-=-int-int"
   (τ-= int int)
   ]
  )

(test-equal #t (judgment-holds (τ-= int int)))
(test-results)

'Γ-⊆
(define-judgment-form
  patina
  #:mode (Γ-⊆ I I)
  #:contract (Γ-⊆ Γ Γ)
  [------------- "Γ-⊆-∅"
   (Γ-⊆ () Γ)
   ]
  [(Γ-get Γ_1 x τ_1) (τ-= τ_0 τ_1) 
   (Γ-use Γ_1 x Γ_2) (Γ-⊆ (γ ...) Γ_2) 
   ------------------------------- "Γ-⊆-¬∅"
   (Γ-⊆ ((x τ_0) γ ...) Γ_1)
   ]
  )

(test-equal #t (judgment-holds (Γ-⊆ () ())))
(test-equal #t (judgment-holds (Γ-⊆ () ((x int) (y int)))))
(test-equal #f (judgment-holds (Γ-⊆ ((x int)) ())))
(test-equal #t (judgment-holds (Γ-⊆ ((x int)) ((y int) (x int)))))
(test-equal #f (judgment-holds (Γ-⊆ ((x int) (x int)) ((x int)))))
(test-equal #t (judgment-holds (Γ-⊆ ((x int) (x int)) ((x int) (x int)))))
(test-equal #f (judgment-holds (Γ-⊆ ((z int)) ((x int)))))
(test-results)

'τ-lv
(define-judgment-form 
 patina
 #:mode (τ-lv I I O)
 #:contract (τ-lv Γ lv τ)
 [(Γ-get Γ x τ)
  ------------- "τ-lv-var"
  (τ-lv Γ x τ) ; TODO this may need to be adjusted for linear types
  ]
 )

(test-equal
 (judgment-holds 
   (τ-lv ((y int) (x int) (z int)) x τ)
   τ) 
 '(int))
(test-equal
  (judgment-holds
    (τ-lv () x τ)
    τ)
  '())
(test-results)

'τ-rv
(define-judgment-form 
 patina
 #:mode (τ-rv I I O O)
 #:contract (τ-rv Γ rv τ Γ)
 [ ---------------- "τ-rv-ℤ"
   (τ-rv Γ ℤ int Γ)
  ]
 [(τ-lv Γ lv_0 int) (τ-lv Γ lv_1 int)
  ----------------------------------- "τ-rv-+"
  (τ-rv Γ (lv_0 + lv_1) int Γ)
  ]
 )

(test-equal
 (judgment-holds
   (τ-rv () 0 τ Γ)
   (τ Γ))
 '((int ())))
(test-equal
 (judgment-holds
   (τ-rv ((x int) (y int)) (x + y) τ Γ)
   (τ Γ))
 '((int ((x int) (y int)))))
(test-results)

'τ-st
(define-judgment-form
  patina
  #:mode (τ-st I I O)
  #:contract (τ-st Γ st Γ)
  [(τ-lv Γ_0 lv τ_0) (τ-rv Γ_0 rv τ_0 Γ_1)
   --------------------------------------- "τ-st-="
   (τ-st Γ_0 (lv = rv) Γ_1)
   ]
  [(Γ-use Γ_0 x Γ_1)
   ------------------------- "τ-st-delete-var"
   (τ-st Γ_0 (delete x) Γ_1)
   ]
  ; TODO delete non-variables somehow
  [(τ-blk Γ_0 blk Γ_1)
   ------------------- "τ-st-block"
   (τ-st Γ_0 blk Γ_1)
   ]
  )

; a helper judgment for τ-blk
'τ-sts
(define-judgment-form
  patina
  #:mode (τ-sts I I O)
  #:contract (τ-sts Γ (st ...) Γ)
  [------------------ "τ-sts-nil"
   (τ-sts Γ_0 () Γ_0)
   ]
  [(τ-st Γ_0 st_0 Γ_1) 
   (τ-sts Γ_1 (st_1 ...) Γ_n)
   ------------------------------- "τ-sts-cons"
   (τ-sts Γ_0 (st_0 st_1 ...) Γ_n)
   ]
  )

'τ-blk
(define-judgment-form
  patina
  #:mode (τ-blk I I O)
  #:contract (τ-blk Γ blk Γ)
  [(τ-sts (Γ-extend-many Γ_0 (vd ...)) (st ...) Γ_1)
   (Γ-⊆ Γ_1 Γ_0)
   ------------------------------------------------- "τ-blk"
   (τ-blk Γ_0 (block (vd ...) (st ...)) Γ_1)
   ]
  )

(test-equal
  (judgment-holds
    (τ-st ((x int)) (x = 1) Γ)
    Γ)
  '(((x int))))
(test-equal
  (judgment-holds
    (τ-st ((x int)) (delete x) Γ)
    Γ)
  '(()))
(test-equal
  (judgment-holds
    (τ-st ((x int)) (block () ((x = 1) (x = 2))) Γ)
    Γ)
  '(((x int))))
(test-equal
  (judgment-holds
    (τ-blk ((x int)) (block () ((x = 1) (x = 2))) Γ)
    Γ)
  '(((x int))))
(test-equal
  (judgment-holds
    (τ-blk () (block ((x : int)) ((x = 1) (delete x))) Γ)
    Γ)
  '(()))
(test-equal
  (judgment-holds
    (τ-blk ((x int)) (block () ((delete x))) Γ)
    Γ)
  '(()))
(test-equal
  (judgment-holds
    (τ-blk () (block ((x : int)) ((x = 1))) Γ)
    Γ)
  '())
(test-results)
