#lang racket
(require redex)

;;;; NOTE I'm going to assume no variable shadowing occurs for now

;;;; SYNTAX
'patina
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

  ;; block - extend context and execute a sequence of statements
  (blk (block (vd ...) (st ...)))

  )

;;;; EVALUATION
'patina-machine
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

;; HEAP OPERATIONS
'H-in
(define-relation
  patina-machine
  H-in ⊆ H × α
  [(H-in ((α_0 _) _ ...) α_0)]
  [(H-in ((α_0 _) h ...) α_1)
   (H-in (h ...) α_1)]
  )

(test-equal (term (H-in (((0 0) (int 0)) ((1 1) ⊥)) (0 0))) #t)
(test-equal (term (H-in (((0 0) (int 0)) ((1 1) ⊥)) (1 1))) #t)
(test-equal (term (H-in (((0 0) (int 0)) ((1 1) ⊥)) (0 1))) #f)
(test-results)

'H-get
(define-metafunction
  patina-machine
  H-get : H α -> hv
  [(H-get H α) ,(cadr (assoc (term α) (term H)))])

(test-equal (term (H-get (((0 0) (int 0)) ((1 1) ⊥)) (0 0))) '(int 0))
(test-equal (term (H-get (((0 0) (int 0)) ((1 1) ⊥)) (1 1))) '⊥)
(test-results)

'H-set
(define-metafunction
  patina-machine
  H-set : H α hv -> H
  [(H-set ((α_0 _) h ...) α_0 hv) 
   ((α_0 hv) h ...)]
  [(H-set ((α_0 hv_0) h_0 ...) α_1 hv_1)
   ((α_0 hv_0) h_1 ...)
   (where (h_1 ...) (H-set (h_0 ...) α_1 hv_1))]
  )

(test-equal
  (term (H-set (((0 0) (int 0)) ((1 1) ⊥)) (0 0) (ptr (1 1))))
  '(((0 0) (ptr (1 1))) ((1 1) ⊥)))
(test-equal
  (term (H-set (((0 0) (int 0)) ((1 1) ⊥)) (1 1) (int 1)))
  '(((0 0) (int 0)) ((1 1) (int 1))))
(test-results)

; H-get respects H-set
(redex-check patina-machine ((h ...) α hv)
    (equal? (term hv) (term (H-get (H-set ((α ⊥) h ...) α hv) α))))

'H-del
(define-metafunction
  patina-machine
  H-del : H α -> H
  [(H-del ((α_0 _) h ...) α_0)
   (h ...)]
  [(H-del ((α_0 hv) h_0 ...) α_1)
   ((α_0 hv) h_1 ...)
   (where (h_1 ...) (H-del (h_0 ...) α_1))]
  )

(test-equal
  (term (H-del (((0 0) (int 0)) ((1 1) ⊥)) (0 0)))
  '(((1 1) ⊥)))
(test-equal
  (term (H-del (((0 0) (int 0)) ((1 1) ⊥)) (1 1)))
  '(((0 0) (int 0))))
(test-results)

'H-cons
(define-metafunction
  patina-machine
  H-cons : H α hv -> H
  [(H-cons H α hv) ,(cons (term (α hv)) (term H))]
  )

; H-cons => H-in
(redex-check patina-machine (H α hv) (term (H-in (H-cons H α hv) α)))

; H-get (H-cons α hv) α = hv
(redex-check patina-machine (H α hv) (equal? (term (H-get (H-cons H α hv) α))
					     (term hv)))

; H-in (H-del (H-cons H)) = H-in H
(redex-check patina-machine (H α hv) (equal? (term (H-in (H-del (H-cons H α hv) α) α)) 
					     (term (H-in H α))))

;; VARIBALE MAP OPERATIONS
'V-in
(define-relation
  patina-machine
  V-in ⊆ V × x
  [(V-in ((x_0 _) _ ...) x_0)]
  [(V-in ((x_0 _) v ...) x_1)
   (V-in (v ...) x_1)]
  )

(test-equal (term (V-in ((x (0 0)) (y (1 1))) x)) #t)
(test-equal (term (V-in ((x (0 0)) (y (1 1))) y)) #t)
(test-equal (term (V-in ((x (0 0)) (y (1 1))) z)) #f)
(test-results)

'V-get
(define-metafunction
  patina-machine
  V-get : V x -> α
  [(V-get V x) ,(cadr (assoc (term x) (term V)))])

(test-equal (term (V-get ((x (0 0)) (y (1 1))) x)) '(0 0))
(test-equal (term (V-get ((x (0 0)) (y (1 1))) y)) '(1 1))
(test-results)

'V-set
(define-metafunction
  patina-machine
  V-set : V x α -> V
  [(V-set ((x_0 _) v ...) x_0 α) 
   ((x_0 α) v ...)]
  [(V-set ((x_0 α_0) v_0 ...) x_1 α_1)
   ((x_0 α_0) v_1 ...)
   (where (v_1 ...) (V-set (v_0 ...) x_1 α_1))]
  )

(test-equal
  (term (V-set ((x (0 0)) (y (1 1))) x (0 1)))
  '((x (0 1)) (y (1 1))))
(test-equal
  (term (V-set ((x (0 0)) (y (1 1))) y (1 0)))
  '((x (0 0)) (y (1 0))))
(test-results)

; V-get respects V-set
(redex-check patina-machine ((v ...) x α)
    (equal? (term α) (term (V-get (V-set ((x (1000 1000)) v ...) x α) x))))

'V-del
(define-metafunction
  patina-machine
  V-del : V x -> V
  [(V-del ((x_0 _) v ...) x_0)
   (v ...)]
  [(V-del ((x_0 α) v_0 ...) x_1)
   ((x_0 α) v_1 ...)
   (where (v_1 ...) (V-del (v_0 ...) x_1))]
  )

(test-equal
  (term (V-del ((x (0 0)) (y (1 1))) x))
  '((y (1 1))))
(test-equal
  (term (V-del ((x (0 0)) (y (1 1))) y))
  '((x (0 0))))
(test-results)

'V-cons
(define-metafunction
  patina-machine
  V-cons : V x α -> V
  [(V-cons V x α) ,(cons (term (x α)) (term V))]
  )

; V-cons => V-in
(redex-check patina-machine (V x α) (term (V-in (V-cons V x α) x)))

; V-in (V-del (V-cons V)) = V-in V
(redex-check patina-machine (V x α) (equal? (term (V-in (V-del (V-cons V x α) x) x)) 
					    (term (V-in V x))))

'sizeof
(define-metafunction
  patina-machine
  sizeof : τ -> ℕ 
  [(sizeof int) 1]
  )

(test-equal (term (sizeof int)) '1)
(test-results)

'alloc
(define-metafunction
  patina-machine
  #:mode (alloc I I I O O)
  #:contract (alloc H V vd H V)
  [(where ℕ_base ,(+ 1 (apply max (cons -1 (map caar (term H_0)))))) ; find the next base address
   (where V_1 ,(cons (term (x (ℕ_base 0))) (term V_0))) ; map x to the start of it
   (where ℕ_size (sizeof τ)) ; compute the size of the type
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
  [(where α (V-get V x))
   --------------------- "E-lv-var"
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
   (where (int ℤ_0) (H-get H α_0))
   (where (int ℤ_1) (H-get H α_1))
   (where ℤ_2 ,(+ (term ℤ_0) (term ℤ_1)))
   -------------------------------------- "E-rv-+"
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
      (where H_2 (H-set H_1 α hv)) 
      "assignment"
      )

    (-->
      (H_0 V_0 ((delete x) st ...))
      (H_1 V_1 (st ...))
      (judgment-holds (E-lv H_0 V_0 x α))
      (where V_1 (V-del V_0 x))
      (where H_1 (H-del H_0 α)) 
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


;;;; TYPING
'patina-context
(define-extended-language patina-context patina
  ;;;; contexts
  ;; variable types
  (γ (x τ))
  (Γ (γ ...))
  ;; list of initialized paths
  (I (lv ...))
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
  [----------------- "x-≠"
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

'initialized
(define-judgment-form
  patina-context
  #:mode (initialized I I)
  #:contract (initialized I lv)
  [---------------------------------- "initialized-here"
   (initialized (lv_0 lv_1 ...) lv_0)
   ]
  [(initialized (lv_1 ...) lv_2)
   ---------------------------------- "initialized-there"
   (initialized (lv_0 lv_1 ...) lv_2)
   ]
  )

(redex-check patina-context (lv_0 lv_1 ...)
  (equal? (if (member (term lv_0) (term (lv_1 ...))) #t #f)
	  (judgment-holds (initialized (lv_1 ...) lv_0))))

'lv-≠
(define-judgment-form
  patina-context
  #:mode (lv-≠ I I)
  #:contract (lv-≠ lv lv)
  [(x-≠ x_0 x_1)
   -------------- "lv-≠-var"
   (lv-≠ x_0 x_1)
   ]
  )

(redex-check patina-context (lv_0 lv_1) (equal? (not (equal? (term lv_0) (term lv_1)))
						(term (lv-≠ lv_0 lv_1))))

'uninitialized
(define-judgment-form
  patina-context
  #:mode (uninitialized I I)
  #:contract (uninitialized I lv)
  [--------------------- "uninitialized-here"
   (uninitialized () lv)
   ]
  [(lv-≠ lv_0 lv_2)
   (uninitialized (lv_1 ...) lv_2)
   ------------------------------------ "uninitialized-there"
   (uninitialized (lv_0 lv_1 ...) lv_2)
   ]
  )

(redex-check patina-context (lv_0 lv_1 ...)
  (equal? (not (if (member (term lv_0) (term (lv_1 ...))) #t #f))
	  (judgment-holds (uninitialized (lv_1 ...) lv_0))))

'initialize
(define-judgment-form
  patina-context
  #:mode (initialize I I O)
  #:contract (initialize I lv I)
  [(initialized I_0 lv)
   ----------------------- "initalize-already"
   (initialize I_0 lv I_0)
   ]
  [(uninitialized (lv_0 ...) lv_1)
   (where I_1 (lv_1 lv_0 ...))
   -------------------------------- "initialize-not-already"
   (initialize (lv_0 ...) lv_1 I_1)
   ]
  )

(redex-check patina-context (lv_0 lv_1 ...)
  (redex-let patina-context ([(I) (judgment-holds (initialize (lv_1 ...) lv_0 I) I)])
      (judgment-holds (initialized I lv_0))))

'deinitialize
(define-judgment-form
  patina-context
  #:mode (deinitialize I I O)
  #:contract (deinitialize I lv I)
  [(uninitialized (lv_1 ...) lv_0) ; finally done
   ---------------------------------------------- "deinitialize-here-done"
   (deinitialize (lv_0 lv_1 ...) lv_0 (lv_1 ...))
   ]
  [(initialized (lv_1 ...) lv_0) ; still more to do
   (deinitialize (lv_1 ...) lv_0 I)
   ------------------------------------- "deinitialize-here-continue"
   (deinitialize (lv_0 lv_1 ...) lv_0 I)
   ]
  [(lv-≠ lv_0 lv_2)
   (initialized (lv_0 lv_1 ...) lv_2) ; no double deinitialize
   (deinitialize (lv_1 ...) lv_2 (lv_3 ...))
   --------------------------------------------------- "deinitialize-there"
   (deinitialize (lv_0 lv_1 ...) lv_2 (lv_0 lv_3 ...))
   ]
  )

(redex-check patina-context (lv_0 lv_1 ...)
  (redex-let* patina-context ([(I_0) (judgment-holds (initialize (lv_1 ...) lv_0 I) I)]
			      [(I_1) (judgment-holds (deinitialize I_0 lv_0 I) I)])
      (judgment-holds (uninitialized I_1 lv_0))))

'I-⊆
(define-judgment-form
  patina-context
  #:mode (I-⊆ I I)
  #:contract (I-⊆ I I)
  [---------- "I-⊆-∅"
   (I-⊆ () I)
   ]
  [(initialized I_1 lv_0) ; make sure lv_0 is in I_1 ...
   (deinitialize I_1 lv_0 I_2) ; remove lv_0 from I_1
   (I-⊆ (lv_1 ...) I_2) ; ... and recurse
   ----------------------------------- "I-⊆-¬∅"
   (I-⊆ (lv_0 lv_1 ...) I_1)
   ]
  )

(test-equal #t (judgment-holds (I-⊆ () ())))
(test-equal #t (judgment-holds (I-⊆ () (x y))))
(test-equal #f (judgment-holds (I-⊆ (x) ())))
(test-equal #t (judgment-holds (I-⊆ (x) (y x))))
(test-equal #t (judgment-holds (I-⊆ (x y) (y x))))
;(test-equal #f (judgment-holds (I-⊆ (x x) (x)))))
;(test-equal #t (judgment-holds (I-⊆ (x x) (x x))))
(test-equal #f (judgment-holds (I-⊆ (z) (x))))
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
   (τ-lv ((y int) (z int)) x τ)
   τ) 
 '())
(test-equal
  (judgment-holds
    (τ-lv () x τ)
    τ)
  '())
(test-results)

'τ-rv
(define-judgment-form 
 patina-context
 #:mode (τ-rv I I I O O)
 #:contract (τ-rv Γ I rv τ I)
 [-------------------- "τ-rv-ℤ"
  (τ-rv Γ I ℤ int I)
  ]
 [(τ-lv Γ lv_0 int) (τ-lv Γ lv_1 int) 
  (initialized I lv_0) (initialized I lv_1)
  ----------------------------------------- "τ-rv-+"
  (τ-rv Γ I (lv_0 + lv_1) int I)
  ]
 )

(test-equal
 (judgment-holds
   (τ-rv () () 0 τ I)
   (τ I))
 '((int ())))
(test-equal
 (judgment-holds
   (τ-rv ((x int) (y int)) (x y) (x + y) τ I)
   (τ I))
 '((int (x y))))
(test-equal
 (judgment-holds
   (τ-rv ((x int) (y int)) (y x) (x + y) τ I)
   (τ I))
 '((int (y x))))
(test-equal
 (judgment-holds
   (τ-rv ((x int) (y int)) (y) (x + y) τ I)
   (τ I))
 '())
(test-results)

; addition preserves initialization
(redex-check patina-context (x_0 x_1)
  (equal? (judgment-holds 
	    (τ-rv ((x_0 int) (x_1 int)) 
		  (x_0 x_1) 
		  (x_0 + x_1) 
		  τ I) 
	    (τ I))
	  `((int ,(term (x_0 x_1))))))

'τ-st
(define-judgment-form
  patina-context
  #:mode (τ-st I I I O)
  #:contract (τ-st Γ I st I)
  [(τ-lv Γ lv τ_0) 
   (τ-rv Γ I_0 rv τ_0 I_1) 
   (initialize I_1 lv I_2)
   -------------------------- "τ-st-="
   (τ-st Γ I_0 (lv = rv) I_2)
   ]
  [(deinitialize I_0 lv I_1)
   ; TODO make sure there are no initialized subpaths
   ---------------------------- "τ-st-delete"
   (τ-st Γ I_0 (delete lv) I_1)
   ]
  [(τ-blk Γ I_O blk I_1)
   --------------------- "τ-st-block"
   (τ-st Γ I_O blk I_1)
   ]
  )

; a helper judgment for τ-blk
'τ-sts
(define-judgment-form
  patina-context
  #:mode (τ-sts I I I O)
  #:contract (τ-sts Γ I (st ...) I)
  [---------------- "τ-sts-nil"
   (τ-sts Γ I () I)
   ]
  [(τ-st Γ I_0 st_0 I_1) 
   (τ-sts Γ I_1 (st_1 ...) I_n)
   --------------------------------- "τ-sts-cons"
   (τ-sts Γ I_0 (st_0 st_1 ...) I_n)
   ]
  )

'τ-blk
(define-judgment-form
  patina-context
  #:mode (τ-blk I I I O)
  #:contract (τ-blk Γ I blk I)
  [(τ-sts (Γ-extend Γ (vd ...)) I_0 (st ...) I_1)
   (I-⊆ I_1 I_0) ; may have deinitialized variables from I_0, but didn't initialize any new ones
   ------------------------------------------------- "τ-blk"
   (τ-blk Γ I_0 (block (vd ...) (st ...)) I_1)
   ]
  )

(test-equal
  (judgment-holds
    (τ-st ((x int)) (x) (x = 1) I)
    I)
  '((x)))
(test-equal
  (judgment-holds
    (τ-st ((x int)) (x) (delete x) I)
    I)
  '(()))
(test-equal
  (judgment-holds
    (τ-st ((x int)) (x) (block () ((x = 1) (x = 2))) I)
    I)
  '((x)))
(test-equal
  (judgment-holds
    (τ-blk ((x int)) (x) (block () ((x = 1) (x = 2))) I)
    I)
  '((x)))
(test-equal
  (judgment-holds
    (τ-blk () () (block ((x : int)) ((x = 1) (delete x))) I)
    I)
  '(()))
(test-equal
  (judgment-holds
    (τ-blk ((x int)) (x) (block () ((delete x))) I)
    I)
  '(()))
; fails because x was not deleted
(test-equal
  (judgment-holds
    (τ-blk () () (block ((x : int)) ((x = 1))) I)
    I)
  '())
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

