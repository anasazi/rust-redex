#lang racket
(require redex)

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

;; EQUALITY OPERATIONS

'x-≠
(define-relation
  patina
  x-≠ ⊆ x × x
  [(x-≠ x_!_0 x_!_0)])

(redex-check patina (x_0 x_1) (equal? (not (equal? (term x_0) (term x_1))) 
				      (term (x-≠ x_0 x_1))))

(test-equal #t (term (x-≠ x y)))
(test-equal #f (term (x-≠ x x)))

'τ-=
(define-relation
  patina
  τ-= ⊆ τ × τ
  [(τ-= int int)]
  )

(test-equal #t (term (τ-= int int)))

'lv-≠
(define-relation
  patina
  lv-≠ ⊆ lv × lv
  [(lv-≠ x_0 x_1)
   (x-≠ x_0 x_1)]
  )

(redex-check patina (lv_0 lv_1) (equal? (not (equal? (term lv_0) (term lv_1))) 
					(term (lv-≠ lv_0 lv_1))))


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

;; ADDRESS OPERATIONS
'α-=
(define-relation
  patina-machine
  α-= ⊆ α × α
  [(α-= (ℕ_b ℕ_o) (ℕ_b ℕ_o))])

(redex-check patina-machine (α) (term (α-= α α)))
(test-equal #f (term (α-= (0 0) (1 0))))
(test-equal #f (term (α-= (0 0) (0 1))))
(test-equal #f (term (α-= (0 0) (1 1))))

'α-offset
(define-metafunction
  patina-machine
  α-offset : α ℕ -> α
  [(α-offset (ℕ_base ℕ_offset) ℕ_offset2) (ℕ_base ,(+ (term ℕ_offset) (term ℕ_offset2)))])

(redex-check patina-machine (ℕ_base ℕ_orig ℕ_1 ℕ_2) (term (α-= (α-offset (α-offset (ℕ_base ℕ_orig) ℕ_1) ℕ_2)
							       (α-offset (ℕ_base ℕ_orig) ,(+ (term ℕ_1) (term ℕ_2))))))

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

'H-get
(define-metafunction
  patina-machine
  H-get : H α -> hv
  [(H-get H α) ,(cadr (assoc (term α) (term H)))])

(test-equal (term (H-get (((0 0) (int 0)) ((1 1) ⊥)) (0 0))) '(int 0))
(test-equal (term (H-get (((0 0) (int 0)) ((1 1) ⊥)) (1 1))) '⊥)

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

'V-get
(define-metafunction
  patina-machine
  V-get : V x -> α
  [(V-get V x) ,(cadr (assoc (term x) (term V)))])

(test-equal (term (V-get ((x (0 0)) (y (1 1))) x)) '(0 0))
(test-equal (term (V-get ((x (0 0)) (y (1 1))) y)) '(1 1))

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

'alloc
(define-judgment-form
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

; make sure alloc works
(redex-check patina-machine (H_0 V_0 x τ)
  (redex-let patina-machine ([((H V)) (judgment-holds (alloc H_0 V_0 (x : τ) H V) (H V))])
    (and (term (V-in V x))
	 (term (H-in H (V-get V x)))
	 (term (H-in H (α-offset (V-get V x) ,(- (term (sizeof τ)) 1))))
	 )))

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



;;;; TYPING
'patina-context
(define-extended-language patina-context patina-machine
  ;;;; contexts
  ;; variable types
  (γ (x τ))
  (Γ (γ ...))
  ;; list of initialized paths
  (I (lv ...))
  ;; heap types
  (hτ (ptr hτ)
      int
      ⊥)
  (σ (α hτ))
  (Σ (σ ...))
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

'Γ-in
(define-relation
  patina-context
  Γ-in ⊆ Γ × x
  [(Γ-in ((x_0 _) _ ...) x_0)]
  [(Γ-in ((x_0 _) γ ...) x_1)
   (Γ-in (γ ...) x_1)])

(test-equal #t (term (Γ-in ((x int) (y int)) x)))
(test-equal #t (term (Γ-in ((x int) (y int)) y)))
(test-equal #f (term (Γ-in ((x int) (y int)) z)))

'Γ-get
(define-metafunction
  patina-context
  Γ-get : Γ x -> τ
  [(Γ-get Γ x) ,(cadr (assoc (term x) (term Γ)))])

(test-equal (term (Γ-get ((x int)) x)) 'int)
(test-equal (term (Γ-get ((y int) (x int)) x)) 'int)

'Γ-del
(define-metafunction
  patina-context
  Γ-del : Γ x -> Γ
  [(Γ-del ((x_0 _) γ ...) x_0)
   (γ ...)]
  [(Γ-del ((x_0 τ) γ_0 ...) x_1)
   ((x_0 τ) γ_1 ...)
   (where (γ_1 ...) (Γ-del (γ_0 ...) x_1))])

(test-equal (term (Γ-del ((x int) (y int)) x)) '((y int)))
(test-equal (term (Γ-del ((x int) (y int)) y)) '((x int)))

'Γ-⊆
(define-judgment-form
  patina-context
  #:mode (Γ-⊆ I I)
  #:contract (Γ-⊆ Γ Γ)
  [---------- "Γ-⊆-∅"
   (Γ-⊆ () Γ)
   ]
  [(Γ-in Γ_1 x)
   (where τ_1 (Γ-get Γ_1 x)) ; make sure x is in Γ_1 ...
   (τ-= τ_0 τ_1)     ; ... as has the type we expect (i.e. τ_0)
   (where Γ_2 (Γ-del Γ_1 x)) ; remove x from Γ_1
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
(test-equal #f (judgment-holds (Γ-⊆ ((x int) (x int)) ((x int)))))
(test-equal #t (judgment-holds (Γ-⊆ ((x int) (x int)) ((x int) (x int)))))
(test-equal #f (judgment-holds (Γ-⊆ ((z int)) ((x int)))))

'I-in
(define-relation
  patina-context
  I-in ⊆ I × lv
  [(I-in (lv_0 _ ...) lv_0)]
  [(I-in (lv_0 lv_1 ...) lv_2)
   (I-in (lv_1 ...) lv_2)])

(redex-check patina-context (lv_0 lv_1 ...)
  (equal? (if (member (term lv_0) (term (lv_1 ...))) #t #f)
	  (term (I-in (lv_1 ...) lv_0))))

(test-equal #t (term (I-in (x y x) x)))
(test-equal #t (term (I-in (x y x) y)))
(test-equal #t (term (I-in (x y x) x)))
(test-equal #f (term (I-in (x y z) w)))

'I-out
(define-relation
  patina-context
  I-out ⊆ I × lv
  [(I-out I lv)
   (side-condition (not (term (I-in I lv))))])

(redex-check patina-context (lv I) (equal? (not (term (I-in I lv))) 
					   (term (I-out I lv))))

(test-equal #f (term (I-out (x y x) x)))
(test-equal #f (term (I-out (x y x) y)))
(test-equal #f (term (I-out (x y x) x)))
(test-equal #t (term (I-out (x y z) w)))

'I-cons
(define-metafunction
  patina-context
  I-cons : I lv -> I
  [(I-cons I lv) 
   ,(cons (term lv) (term I))
   (side-condition (term (I-out I lv)))]
  [(I-cons I lv)
   I
   (side-condition (term (I-in I lv)))])

(test-equal '(x) (term (I-cons () x)))
(test-equal '(x) (term (I-cons (x) x)))

; I-cons => I-in
(redex-check patina-context (lv I) (term (I-in (I-cons I lv) lv)))

'I-del
(define-metafunction
  patina-context
  I-del : I lv -> I
  [(I-del (lv_0 lv_1 ...) lv_0)
   (lv_1 ...)
   ]
  [(I-del (lv_0 lv_1 ...) lv_2)
   (lv_0 lv_3 ...)
   (where (lv_3 ...) (I-del (lv_1 ...) lv_2))
   ])

(test-equal '() (term (I-del (x) x)))
(test-equal '(x) (term (I-del (x y) y)))

; I-in (I-del (I-cons I)) = I-in I
;(redex-check patina-context #:satisfying (I-out I lv) 
  ;(term (I-out (I-del (I-cons I lv) lv) lv)))

'I-⊆
(define-relation
  patina-context
  I-⊆ ⊆ I × I
  [(I-⊆ () I)]
  [(I-⊆ (lv_0 lv_1 ...) I_1)
   (I-in I_1 lv_0) ; make sure lv_0 is in I_1 ...
   (I-⊆ (lv_1 ...) (I-del I_1 lv_0)) ; ... remove lv_0 from I_1 and recurse
   ]
  )

(test-equal #t (term (I-⊆ () ())))
(test-equal #t (term (I-⊆ () (x y))))
(test-equal #f (term (I-⊆ (x) ())))
(test-equal #t (term (I-⊆ (x) (y x))))
(test-equal #t (term (I-⊆ (x y) (y x))))
(test-equal #f (term (I-⊆ (z) (x))))

'τ-lv
(define-judgment-form 
 patina-context
 #:mode (τ-lv I I O)
 #:contract (τ-lv Γ lv τ)
 [(Γ-in Γ x) (where τ (Γ-get Γ x))
  -------------------------------- "τ-lv-var"
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

'τ-rv
(define-judgment-form 
 patina-context
 #:mode (τ-rv I I I O O)
 #:contract (τ-rv Γ I rv τ I)
 [------------------ "τ-rv-ℤ"
  (τ-rv Γ I ℤ int I)
  ]
 [(τ-lv Γ lv_0 int) (τ-lv Γ lv_1 int) 
  (I-in I lv_0) (I-in I lv_1)
  ----------------------------------- "τ-rv-+"
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
   (where I_2 (I-cons I_1 lv))
   --------------------------- "τ-st-="
   (τ-st Γ I_0 (lv = rv) I_2)
   ]
  [(where I_1 (I-del I_0 lv))
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
