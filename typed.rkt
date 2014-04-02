#lang racket
(require redex)

;;;; NOTE I'm going to assume no variable shadowing occurs for now

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
  (ℕ natural)
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

  )

(define-extended-language patina-context patina
  ;;;; contexts
  ;; variable types
  (γ (x τ))
  (Γ (γ ...))
  ;; list of initialized paths
  ;(I (lv ...)) TODO
  )

'vd→γ
(define-metafunction
  patina-context
  vd→γ : vd -> γ
  [(vd→γ (x : τ)) (x τ)]
  )

(redex-check patina-context (x τ) (equal? (term (vd→γ (x : τ))) (term (x τ))))

'Γ-extend
(define-metafunction
  patina-context
  Γ-extend : Γ (vd ...) -> Γ
  [(Γ-extend Γ (vd ...))
   ,(append (map (λ (vd) (term (vd→γ ,vd))) (reverse (term (vd ...)))) (term Γ))]
  )

(test-equal
  (term (Γ-extend () ((x : int) (y : int) (z : int) (x : int))))
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

(redex-check patina-context (x_0 x_1) (equal? (not (equal? (term x_0) (term x_1)))
					      (term (x-≠ x_0 x_1))))

(test-equal #t (judgment-holds (x-≠ x y)))
(test-equal #f (judgment-holds (x-≠ x x)))
(test-results)

'Γ-use
(define-judgment-form
  patina-context
  #:mode (Γ-use I I O)
  #:contract (Γ-use Γ x Γ)
  [----------------------------------- "Γ-use-here"
   (Γ-use ((x_0 τ) γ ...) x_0 (γ ...))
   ]
  [(Γ-use (γ_0 ...) x_1 (γ_1 ...)) (x-≠ x_0 x_1)
   ----------------------------------------------- "Γ-use-there"
   (Γ-use ((x_0 τ) γ_0 ...) x_1 ((x_0 τ) γ_1 ...))
   ]
  )

(test-equal
  (judgment-holds 
    (Γ-use ((x int)) x Γ)
    Γ)
  '(()))
;(test-equal
  ;(judgment-holds 
    ;(Γ-use ((x int) (x int)) x Γ)
    ;Γ)
  ;'(((x int))))
(test-equal
  (judgment-holds 
    (Γ-use ((x int) (y int)) x Γ)
    Γ)
  '(((y int))))
(test-equal
  (judgment-holds 
    (Γ-use ((y int) (x int)) x Γ)
    Γ)
  '(((y int))))
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
  patina-context
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
  patina-context
  #:mode (Γ-⊆ I I)
  #:contract (Γ-⊆ Γ Γ)
  [---------- "Γ-⊆-∅"
   (Γ-⊆ () Γ)
   ]
  [(Γ-get Γ_1 x τ_1) ; make sure x is in Γ_1 ...
   (τ-= τ_0 τ_1)     ; ... as has the type we expect (i.e. τ_0)
   (Γ-use Γ_1 x Γ_2) ; remove x from Γ_1 ...
   (Γ-⊆ (γ ...) Γ_2) ; ... and recurse
   ----------------------------------- "Γ-⊆-¬∅"
   (Γ-⊆ ((x τ_0) γ ...) Γ_1)
   ]
  )

(test-equal #t (judgment-holds (Γ-⊆ () ())))
(test-equal #t (judgment-holds (Γ-⊆ () ((x int) (y int)))))
(test-equal #f (judgment-holds (Γ-⊆ ((x int)) ())))
(test-equal #t (judgment-holds (Γ-⊆ ((x int)) ((y int) (x int)))))
(test-equal #t (judgment-holds (Γ-⊆ ((x int) (y int)) ((y int) (x int)))))
;(test-equal #f (judgment-holds (Γ-⊆ ((x int) (x int)) ((x int)))))
;(test-equal #t (judgment-holds (Γ-⊆ ((x int) (x int)) ((x int) (x int)))))
(test-equal #f (judgment-holds (Γ-⊆ ((z int)) ((x int)))))
(test-results)

'τ-lv
(define-judgment-form 
 patina-context
 #:mode (τ-lv I I O)
 #:contract (τ-lv Γ lv τ)
 [(Γ-get Γ x τ)
  ------------- "τ-lv-var"
  (τ-lv Γ x τ)
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
 patina-context
 #:mode (τ-rv I I O O)
 #:contract (τ-rv Γ rv τ Γ)
 [---------------- "τ-rv-ℤ"
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
  patina-context
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
  [(τ-blk Γ_0 blk Γ_1)
   ------------------- "τ-st-block"
   (τ-st Γ_0 blk Γ_1)
   ]
  )

; a helper judgment for τ-blk
'τ-sts
(define-judgment-form
  patina-context
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
  patina-context
  #:mode (τ-blk I I O)
  #:contract (τ-blk Γ blk Γ)
  [(τ-sts (Γ-extend Γ_0 (vd ...)) (st ...) Γ_1)
   (Γ-⊆ Γ_1 Γ_0) ; may have freed variables from Γ_0, but didn't add any new ones
   -------------------------------------------- "τ-blk"
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

(define-extended-language patina-machine patina
  ;;;; memory
  ;; address = base + offset
  (α (ℕ ℕ))
  ;; hvalues - things that can be stored in memory
  (hv (ptr α) ; an address can be stored in memory
      (int ℤ) ; an integer can be stored in memory
      ⊥	      ; invalid data can be stored in memory
      )
  ;; heap - map addresses to hvalues
  (h (α hv))
  (H (h ...))
  ;; map variables to addresses
  (v (x α))
  (V (v ...))
  )

'get
(define (get x l) (cadr (assoc x l)))
'put
(define (put x v l) (map (λ (p) (if (equal? (car p) x) `(,x ,v) p)) l))
'del
(define (del x l) (filter (λ (p) (not (equal? x (car p)))) l))

(test-equal
  (get 'x '((x 0) (y 1)))
  0)
(test-equal
  (put 'x 1 '((x 0) (y 1)))
  '((x 1) (y 1)))
(test-equal
  (del 'x '((x 0) (y 1)))
  '((y 1)))
(test-results)

'sizeof
(define-judgment-form
  patina-machine
  #:mode (sizeof I O)
  #:contract (sizeof τ ℕ)
  [-------------- "sizeof-int"
   (sizeof int 1)
   ]
  )

(test-equal
  (judgment-holds
    (sizeof int ℕ)
    ℕ)
  '(1))
(test-results)

'alloc
(define-judgment-form
  patina-machine
  #:mode (alloc I I I O O)
  #:contract (alloc H V vd H V)
  [(where ℕ_base ,(+ 1 (apply max (cons -1 (map caar (term H_0)))))) ; find the next base address
   (where V_1 ,(cons (term (x (ℕ_base 0))) (term V_0))) ; map x to the start of it
   (sizeof τ ℕ_size) ; compute the size of the type
   (where H_new ,(map (λ (x) `((,(term ℕ_base) ,x) ⊥)) (range (term ℕ_size)))) ; make new space
   (where H_1 ,(append (term H_new) (term H_0))) ; add it to the heap
   -------------------------------------------------------------------------- "alloc"
   (alloc H_0 V_0 (x : τ) H_1 V_1)
   ]
  )

(test-equal
  (judgment-holds
    (alloc (((0 0) (int 0))) ((x (0 0))) (y : int) H V)
    (H V))
  '((
     (((1 0) ⊥) ((0 0) (int 0)))
     ((y (1 0)) (x (0 0)))
     )))
(test-results)

'E-lv
(define-judgment-form 
  patina-machine
  #:mode (E-lv I I I O)
  #:contract (E-lv H V lv α)
  [(where α ,(get (term x) (term V)))
   ------------------------------------- "E-lv-var"
   (E-lv H V x α)
   ]
  )

(test-equal
  (judgment-holds 
    (E-lv () ((a (0 0)) (d (12 321)) (n (123 12321))) d α)
    α)
  '((12 321)))
(test-results)

'E-rv
(define-judgment-form
  patina-machine
  #:mode (E-rv I I I O O O)
  #:contract (E-rv H V rv H V hv)
  [------------------------ "E-rv-ℤ"
   (E-rv H V ℤ H V (int ℤ))
   ]
  [(E-lv H V lv_0 α_0) 
   (E-lv H V lv_1 α_1)
   (where (int ℤ_0) ,(get (term α_0) (term H)))
   (where (int ℤ_1) ,(get (term α_1) (term H)))
   (where ℤ_2 ,(+ (term ℤ_0) (term ℤ_1)))
   ----------------------------------------------------- "E-rv-+"
   (E-rv H V (lv_0 + lv_1) H V (int ℤ_2))
   ]
  )

(test-equal
  (judgment-holds
    (E-rv (((0 0) (int 1)) ((1 0) (int 2)))
	  ((a (0 0)) (b (1 0))) 
	  (a + b) 
	  H V hv)
    (H V hv))
  '(((((0 0) (int 1)) ((1 0) (int 2)))
     ((a (0 0)) (b (1 0)))
     (int 3))))
(test-results)

'patina-step
(define patina-step
  (reduction-relation
    patina-machine
    #:domain (H V (st ...))

    (--> 
      (H_0 V_0 ((lv = rv) st ...)) 
      (H_2 V_1 (st ...)) 
      (judgment-holds (E-lv H_0 V_0 lv α)) 
      (judgment-holds (E-rv H_0 V_0 rv H_1 V_1 hv)) 
      (where H_2 ,(put (term α) (term hv) (term H_1))) 
      "assignment"
      )

    (-->
      (H_0 V_0 ((delete x) st ...))
      (H_1 V_1 (st ...))
      (judgment-holds (E-lv H_0 V_0 x α))
      (where V_1 ,(del (term x) (term V_0)))
      (where H_1 ,(del (term α) (term H_0)))
      "delete-var"
      )

    (-->
      (H_0 V_0 ((block (vd) (st ...))))
      (H_1 V_1 (st ...))
      (judgment-holds (alloc H_0 V_0 vd H_1 V_1))
      "block-alloc-last-var"
      )

    (-->
      (H_0 V_0 ((block (vd_0 vd_1 vd_2 ...) (st ...))))
      (H_1 V_1 ((block (vd_1 vd_2 ...) (st ...))))
      (judgment-holds (alloc H_0 V_0 vd_0 H_1 V_1))
      "block-alloc-one-var"
      )

    )
  )

(test-->> patina-step
  (term (() () ()))
  (term (() () ())))

(test-->> patina-step
  (term ((((0 0) ⊥)) ((x (0 0))) ()))
  (term ((((0 0) ⊥)) ((x (0 0))) ()))
  )

(test-->> patina-step
  (term ((((0 0) (int 0))) ((x (0 0))) ((x = 1))))
  (term ((((0 0) (int 1))) ((x (0 0))) ()))
  )

(test-->> patina-step
  (term ((((0 0) (int 0))) ((x (0 0))) ((delete x))))
  (term (()                ()          ()          ))
  )

(test-->> patina-step
  (term (() () ((block ((x : int) (y : int)) ()))))
  (term ((((1 0) ⊥) ((0 0) ⊥)) ((y (1 0)) (x (0 0))) ()))
  )

(test-->> patina-step
  (term (() () ((block ((x : int) (y : int)) ((delete y) (delete x))))))
  (term (() () ())))

(test-results)

;(define-union-language patina-context-machine patina-context patina-machine)

;(define-judgment-form
  ;patina-context-machine
  ;#:mode (τ-hv I I O)
  ;#:contract (τ-hv H hv τ)
  ;[-------------------- "τ-hv-int"
   ;(τ-hv H (int ℤ) int)
   ;]
  ;[(τ-hv H ,(get (term α) (term H)) τ)
   ;----------------------------------- "τ-hv-ptr"
   ;(τ-hv H (ptr α) τ)
   ;]
  ;)
;
;(define-metafunction
  ;patina-context-machine
  ;H+V→Γ : H V -> Γ
  ;[(H+V→Γ () ()) ()]
  ;[(H+V→Γ H ((x α) v ...))
;
;(define (types? H V sts)
;  (equal? '(()) (judgment-holds (τ-sts () ,sts Γ) Γ)))
;
;(judgment-holds (τ-sts () ((block ((x : int) (y : int)) ((delete y) (delete x)))) Γ) Γ)
;(judgment-holds (τ-sts () ((block ((x : int) (y : int)) ( (delete x)))) Γ) Γ)
;(judgment-holds (τ-sts () ((block ((x : int) (y : int)) ( ))) Γ) Γ)
;(types? (term ((block ((x : int) (y : int)) ((delete y) (delete x))))))
;(types? (term ((block ((x : int) (y : int)) ( (delete x))))))
;(types? (term ((block ((x : int) (y : int)) ( )))))
;
;(define (reduces? sts)

