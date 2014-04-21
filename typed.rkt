#lang racket
(require redex)

;;;; SYNTAX
(define-language patina
  ;; variables (α-convertible)
  (x variable-not-otherwise-mentioned)

  ;; integers
  (z integer)

  ;; paths (lhs values)
  (lv x      ; variable
      (* lv) ; pointer dereference
      )

  ;; expressions (rhs values)
  (rv z         ; integer constants
      (lv + lv) ; addition (copies operands)
      lv        ; use by moving from a path
      (new lv)  ; move from a path into a new heap allocation
      )

  ;; types
  (τ int    ; integers
     (~ τ)  ; owned pointer
     )

  ;; variable declaration
  (vd (x : τ))

  ;; statements
  (s  ; sequence of statements
     (s ...) 
      ; extend context in a fresh lifetime by pushing onto the stack,
      ; execute a statement,
      ; and then pop all that off the stack.
     (block (vd ...) s (vd ...)) 
      ; assign to a path (path must be uninitialized)
     (lv = rv)
      ; shallow destruction.
      ; subpaths must already be uninitialized.
      ; frees heap memory.
     (delete lv)
     )
  )

;;;; EVALUATION
(define-extended-language patina-machine patina
  ;; natural numbers
  (n natural)
  ;; base of address (i.e. an allocation)
  (β n)
  ;; offset of address (i.e. position in an allocation)
  (δ n)
  ;; an address is a base and an offset
  (α (β δ))
  ;; values can go in memory
  (v ⊥ ; uninitialized
     z ; integers
     α ; addresses
     )
  ;; memory (heap) maps address to values
  (μ ((α v) ...))
  ;; map from variables to addresses
  (V ((x α) ...))

  ;; context mapping variables to types
  ; NB type checking results available at runtime
  (Γ ((x τ) ...))
  )

;; address offset from an address
(define-judgment-form patina-machine
  #:mode (α+ I I O)
  #:contract (α+ α n α)
  [--------------------------------------- "α+"
   (α+ (β δ) n (β ,(+ (term δ) (term n))))
   ]
  )

; (α+ α 0 α)
(redex-check patina-machine α (equal? (term (α)) (judgment-holds (α+ α 0 α_r) α_r)))
; (α+ (α+ α n_0) n_1) = (α+ α (n_0 n_1))
(redex-check patina-machine (α_0 n_0 n_1) 
  (equal? 
    (judgment-holds (α+ α_0 ,(+ (term n_0) (term n_1)) α) α)
    (redex-let patina-machine 
               [((α_1) (judgment-holds (α+ α_0 n_0 α) α))] 
               (judgment-holds (α+ α_1 n_1 α_2) α_2))))

;; size of a type in memory
(define-judgment-form patina-machine
  #:mode (sizeof I O)
  #:contract (sizeof τ n)
  [----------- "sizeof int"
   (sizeof int 1)
   ]
  [------------- "sizeof ~τ"
   (sizeof (~ τ) 1)
   ]
  )

(test-equal (term (1)) (judgment-holds (sizeof int n) n))
(redex-check patina-machine τ (equal? (term (1)) (judgment-holds (sizeof (~ τ) n) n)))

;; allocate space for a type
(define-judgment-form patina-machine
  #:mode (μ+ I I O O)
  #:contract (μ+ μ τ α μ)
  [(sizeof τ n)
   (where (n_off ...) ,(range (term n)))
   (where ((β_0 _) ...) (α_0 ...))
   (where β_new ,(+ 1 (apply max (cons -1 (term (β_0 ...))))))
   (α+ (β_new 0) n_off α_new) ...
   --------------------------------------------------------------- "μ+"
   (μ+ ((α_0 v_0) ...)  τ (β_new 0) ((α_0 v_0) ... (α_new ⊥) ...))
   ]
  )

(test-equal '((((0 0) ⊥))) (judgment-holds (μ+ () int α μ) μ))
(test-equal '((((0 0) ⊥) ((0 1) ⊥) ((1 0) ⊥))) 
            (judgment-holds (μ+ (((0 0) ⊥) ((0 1) ⊥)) (~ (~ int)) α μ) μ))

;; set the value at an address in memory
(define-judgment-form patina-machine
  #:mode (μ<- I I I O)
  #:contract (μ<- μ α v μ)
  [--------------------------------------------------------------------------------------- "μ<-"
   (μ<- ((α_s v_s) ... (α_0 _) (α_e v_e) ...) α_0 v ((α_s v_s) ... (α_0 v) (α_e v_e) ...))
   ]
  )

(test-equal '((((0 0) 1))) (judgment-holds (μ<- (((0 0) ⊥)) (0 0) 1 μ) μ))

;; lookup address in memory to get value
(define-judgment-form patina-machine
  #:mode (μ= I I O)
  #:contract (μ= μ α v)
  [--------------------------------------------- "μ="
   (μ= ((α_s _) ... (α_0 v) (α_e _) ...) α_0 v)
   ]
  )

(test-equal '(1) (judgment-holds (μ= (((0 0) 1)) (0 0) v) v))

;; move helper - thread the heap through moving a value on a sequence of addresses
(define-judgment-form patina-machine
  #:mode (μ->helper I I I O)
  #:contract (μ->helper μ (α ...) (α ...) μ)
  [--------------------- "μ->helper done"
   (μ->helper μ () () μ)
   ]
  [(μ= μ_0 α_s0 v)
   (μ<- μ_0 α_d0 v μ_1)
   (μ<- μ_1 α_s0 ⊥ μ_2)
   (μ->helper μ_2 (α_s1 ...) (α_d1 ...) μ_3)
   ------------------------------------------------------- "μ->helper move one"
   (μ->helper μ_0 (α_s0 α_s1 ..._0) (α_d0 α_d1 ..._0) μ_3)
   ]
  )

;; move a type's worth of space to another spot on the heap
(define-judgment-form patina-machine
  #:mode (μ-> I I I I O)
  #:contract (μ-> μ α τ α μ)
  [(sizeof τ n) 
   (where (n_off ...) ,(range (term n)))
   (α+ α_s n_off α_s0) ...
   (α+ α_d n_off α_d0) ...
   (μ->helper μ_0 (α_s0 ...) (α_d0 ...) μ_1)
   ---------------------------------------------- "μ->"
   (μ-> μ_0 α_s τ α_d μ_1)
   ]
  )

(test-equal '((((0 0) ⊥) ((1 0) 1))) (judgment-holds (μ-> (((0 0) 1) ((1 0) ⊥)) (0 0) int (1 0) μ) μ))

;; free space for a type from an address
(define-judgment-form patina-machine
  #:mode (μ- I I I O)
  #:contract (μ- μ τ α μ)
  [(sizeof τ n)
   (where (n_off ...) ,(range (term n)))
   (α+ α n_off α_0) ...
   -------------------------------------------------------------------------------- "μ-"
   (μ- ((α_s v_s) ... (α_0 _) ... (α_e v_e) ...) τ α ((α_s v_s) ... (α_e v_e) ...))
   ]
  )

(test-equal '(()) (judgment-holds (μ- (((0 0) 1)) int (0 0) μ) μ))

;; lookup variable in map to get address
(define-judgment-form patina-machine
  #:mode (V= I I O)
  #:contract (V= V x α)
  [--------------------------------------------- "V="
   (V= ((x_s _) ... (x_0 α) (x_e _) ...) x_0 α)
   ]
  )

(test-equal '((0 0)) (judgment-holds (V= ((x (0 0))) x α) α))

;; lookup type of a variable
(define-judgment-form patina-machine
  #:mode (Γ= I I O)
  #:contract (Γ= Γ x τ)
  [--------------------------------------------- "Γ="
   (Γ= ((x_s _) ... (x_0 τ) (x_e _) ...) x_0 τ)
   ]
  )

(test-equal '(int) (judgment-holds (Γ= ((x int)) x τ) τ))

;;;; TYPING
(define-extended-language patina-checked patina-machine
  ;; initialization flags
  (ι ⊥ ; uninitialized
     ⊤ ; initialized
     )
  ;; initialization of allocated paths
  (Δ ((lv ι) ...))
  ;; heap typing
  (Σ ((α τ) ...))
  )

;; look up initialization status of a path
(define-judgment-form patina-checked
  #:mode (Δ= I I O)
  #:contract (Δ= Δ lv ι)
  [------------------------------------------------ "Δ="
   (Δ= ((lv_s _) ... (lv_0 ι) (lv_e _) ...) lv_0 ι)
   ]
  )

(test-equal '(⊤) (judgment-holds (Δ= ((x ⊤)) x ι) ι))

;; path initialization unspecified
(define-judgment-form patina-checked
  #:mode (Δ? I I)
  #:contract (Δ? Δ lv)
  [---------- "Δ? empty"
   (Δ? () lv)
   ]
  [(Δ? ((lv_1 ι_1) ...) lv_2)
   (where (lv_!_0 lv_!_0) (lv_0 lv_2))
   ----------------------------------- "Δ? cons"
   (Δ? ((lv_0 _) (lv_1 ι_1) ...) lv_2)
   ]
  )

(test-equal #f (judgment-holds (Δ? ((x ⊤) (y ⊥)) x)))
(test-equal #f (judgment-holds (Δ? ((x ⊤) (y ⊥)) y)))
(test-equal #t (judgment-holds (Δ? ((x ⊤) (y ⊥)) z)))

;; initialize a path
(define-judgment-form patina-checked
  #:mode (Δ↑ I I O)
  #:contract (Δ↑ Δ lv Δ)
  [------------------------------------------------------------------------------------------- "Δ↑ present"
   (Δ↑ ((lv_s ι_s) ... (lv_0 _) (lv_e ι_e) ...) lv_0 ((lv_s ι_s) ... (lv_0 ⊤) (lv_e ι_e) ...))
   ]
  [ (Δ? Δ lv)
   --------------------------------------------------- "Δ↑ new"
   (Δ↑ Δ lv ,(cons (term (lv ⊤)) (term Δ)))
   ]
  )

(test-equal '(((x ⊤) (y ⊤))) (judgment-holds (Δ↑ ((x ⊥) (y ⊤)) x Δ) Δ))
(test-equal '(((x ⊤) (y ⊤))) (judgment-holds (Δ↑ ((x ⊤) (y ⊤)) x Δ) Δ))
(test-equal '(((x ⊤) (y ⊤))) (judgment-holds (Δ↑ ((y ⊤)) x Δ) Δ))

;; uninitialize a path
(define-judgment-form patina-checked
  #:mode (Δ↓ I I O)
  #:contract (Δ↓ Δ lv Δ)
  [------------------------------------------------------------------------------------------- "Δ↓ present"
   (Δ↓ ((lv_s ι_s) ... (lv_0 _) (lv_e ι_e) ...) lv_0 ((lv_s ι_s) ... (lv_0 ⊥) (lv_e ι_e) ...))
   ]
  [(Δ? Δ lv)
   --------------------------------------------------- "Δ↓ new"
   (Δ↓ Δ lv ,(cons (term (lv ⊥)) (term Δ)))
   ]
  )

(test-equal '(((x ⊥) (y ⊤))) (judgment-holds (Δ↓ ((x ⊥) (y ⊤)) x Δ) Δ))
(test-equal '(((x ⊥) (y ⊤))) (judgment-holds (Δ↓ ((x ⊤) (y ⊤)) x Δ) Δ))
(test-equal '(((x ⊥) (y ⊤))) (judgment-holds (Δ↓ ((y ⊤)) x Δ) Δ))

;; typechecking for paths. makes sure a path will be allocated, but not necessarily initialized
(define-judgment-form patina-checked
  #:mode (lv⊢ I I O)
  #:contract (lv⊢ Γ lv τ)
  [(Γ= Γ x τ)
   ----------- "lv⊢ var"
   (lv⊢ Γ x τ)
   ]
  [(lv⊢ Γ lv (~ τ))
   ---------------- "lv⊢ owned"
   (lv⊢ Γ (* lv) τ)
   ]
  )

(test-equal '(int) (judgment-holds (lv⊢ ((x (~ (~ int)))) (* (* x)) τ) τ))
(test-equal #f (judgment-holds (lv⊢ ((x int)) (* x) τ)))

;; path fully initialized (all subpaths initialized)
(define-judgment-form patina-checked
  #:mode (lv⇑ I I I)
  #:contract (lv⇑ Γ Δ lv)
  [(lv⊢ Γ lv int) (Δ= Δ lv ⊤)
   -------------------------- "lv⇑ int"
         (lv⇑ Γ Δ lv)
   ]
  [(lv⊢ Γ lv (~ τ)) (Δ= Δ lv ⊤) (lv⇑ Γ Δ (* lv))
   --------------------------------------------- "lv⇑ ~τ"
                    (lv⇑ Γ Δ lv)
   ]
  )

(test-equal #t (judgment-holds (lv⇑ ((x int) (y (~ int))) ((x ⊤) (y ⊤) ((* y) ⊥)) x)))
(test-equal #f (judgment-holds (lv⇑ ((x int) (y (~ int))) ((x ⊤) (y ⊤) ((* y) ⊥)) y)))
(test-equal #f (judgment-holds (lv⇑ ((x int) (y (~ int))) ((x ⊤) (y ⊤) ((* y) ⊥)) (* y))))

;; path fully uninitialized (all subpaths uninitialized)
(define-judgment-form patina-checked
  #:mode (lv⇓ I I I)
  #:contract (lv⇓ Γ Δ lv)
  [(lv⊢ Γ lv int) (Δ= Δ lv ⊥)
   -------------------------- "lv⇓ int"
        (lv⇓ Γ Δ lv)
   ]
  [(lv⊢ Γ lv (~ τ)) (Δ= Δ lv ⊥) (lv⇓ Γ Δ (* lv))
   --------------------------------------------- "lv⇓ ~τ"
                    (lv⇓ Γ Δ lv)
   ]
  )

(test-equal #f (judgment-holds (lv⇓ ((x int) (y (~ int))) ((x ⊤) (y ⊤) ((* y) ⊥)) x)))
(test-equal #f (judgment-holds (lv⇓ ((x int) (y (~ int))) ((x ⊤) (y ⊤) ((* y) ⊥)) y)))
(test-equal #t (judgment-holds (lv⇓ ((x int) (y (~ int))) ((x ⊤) (y ⊤) ((* y) ⊥)) (* y))))
(test-equal #t (judgment-holds (lv⇓ ((x int) (y (~ int))) ((x ⊤) (y ⊥) ((* y) ⊥)) y)))

;; all subpaths uninitialized, but path may or may not be initialized
(define-judgment-form patina-checked
  #:mode (lv↓ I I I)
  #:contract (lv↓ Γ Δ lv)
  [(lv⇓ Γ ((lv_s ι_s) ... (lv_0 ⊥) (lv_e ι_e) ...) lv_0)
   ----------------------------------------------------- "lv↓ present"
   (lv↓ Γ ((lv_s ι_s) ... (lv_0 _) (lv_e ι_e) ...) lv_0)
   ]
  )

(test-equal #t (judgment-holds (lv↓ ((x int) (y (~ int))) ((x ⊤) (y ⊤) ((* y) ⊥)) x)))
(test-equal #t (judgment-holds (lv↓ ((x int) (y (~ int))) ((x ⊤) (y ⊤) ((* y) ⊥)) y)))
(test-equal #t (judgment-holds (lv↓ ((x int) (y (~ int))) ((x ⊤) (y ⊤) ((* y) ⊥)) (* y))))
(test-equal #t (judgment-holds (lv↓ ((x int) (y (~ int))) ((x ⊤) (y ⊥) ((* y) ⊥)) y)))

;; fully initialize a path
(define-judgment-form patina-checked
  #:mode (lv⇑⇑ I I I O)
  #:contract (lv⇑⇑ Γ Δ lv Δ)
  [(lv⊢ Γ lv int) (Δ↑ Δ_0 lv Δ_1)
   ------------------------------ "lv⇑⇑ int"
        (lv⇑⇑ Γ Δ_0 lv Δ_1)
   ]
  [(lv⊢ Γ lv (~ τ)) (lv⇑⇑ Γ Δ_0 (* lv) Δ_1) (Δ↑ Δ_1 lv Δ_2)
   -------------------------------------------------------- "lv⇑⇑ ~τ"
                       (lv⇑⇑ Γ Δ_0 lv Δ_2)
   ]
  )

(test-equal '(((x ⊤))) (judgment-holds (lv⇑⇑ ((x int)) () x Δ) Δ))
(test-equal '(((x ⊤))) (judgment-holds (lv⇑⇑ ((x int)) ((x ⊤)) x Δ) Δ))
(test-equal '(((x ⊤))) (judgment-holds (lv⇑⇑ ((x int)) ((x ⊥)) x Δ) Δ))
(test-equal '(((x ⊤) ((* x) ⊤))) (judgment-holds (lv⇑⇑ ((x (~ int))) () x Δ) Δ))
(test-equal '((((* x) ⊤) (x ⊤))) (judgment-holds (lv⇑⇑ ((x (~ int))) ((x ⊤)) x Δ) Δ))
(test-equal '(((x ⊤) ((* x) ⊤))) (judgment-holds (lv⇑⇑ ((x (~ int))) ((x ⊤) ((* x) ⊤)) x Δ) Δ))
(test-equal '(((x ⊤) ((* x) ⊤))) (judgment-holds (lv⇑⇑ ((x (~ int))) ((x ⊤) ((* x) ⊥)) x Δ) Δ))
(test-equal '((((* x) ⊤) (x ⊤))) (judgment-holds (lv⇑⇑ ((x (~ int))) ((x ⊥)) x Δ) Δ))
(test-equal '(((x ⊤) ((* x) ⊤))) (judgment-holds (lv⇑⇑ ((x (~ int))) ((x ⊥) ((* x) ⊤)) x Δ) Δ))
(test-equal '(((x ⊤) ((* x) ⊤))) (judgment-holds (lv⇑⇑ ((x (~ int))) ((x ⊥) ((* x) ⊥)) x Δ) Δ))

;; fully uninitialize a path
(define-judgment-form patina-checked
  #:mode (lv⇓⇓ I I I O)
  #:contract (lv⇓⇓ Γ Δ lv Δ)
  [(lv⊢ Γ lv int) (Δ↓ Δ_0 lv Δ_1)
   ------------------------------ "lv⇓⇓ int"
        (lv⇓⇓ Γ Δ_0 lv Δ_1)
   ]
  [(lv⊢ Γ lv (~ τ)) (lv⇓⇓ Γ Δ_0 (* lv) Δ_1) (Δ↓ Δ_1 lv Δ_2)
   -------------------------------------------------------- "lv⇓⇓ ~τ"
                       (lv⇓⇓ Γ Δ_0 lv Δ_2)
   ]
  )

(test-equal '(((x ⊥))) (judgment-holds (lv⇓⇓ ((x int)) () x Δ) Δ))
(test-equal '(((x ⊥))) (judgment-holds (lv⇓⇓ ((x int)) ((x ⊤)) x Δ) Δ))
(test-equal '(((x ⊥))) (judgment-holds (lv⇓⇓ ((x int)) ((x ⊥)) x Δ) Δ))
(test-equal '(((x ⊥) ((* x) ⊥))) (judgment-holds (lv⇓⇓ ((x (~ int))) () x Δ) Δ))
(test-equal '((((* x) ⊥) (x ⊥))) (judgment-holds (lv⇓⇓ ((x (~ int))) ((x ⊤)) x Δ) Δ))
(test-equal '(((x ⊥) ((* x) ⊥))) (judgment-holds (lv⇓⇓ ((x (~ int))) ((x ⊤) ((* x) ⊤)) x Δ) Δ))
(test-equal '(((x ⊥) ((* x) ⊥))) (judgment-holds (lv⇓⇓ ((x (~ int))) ((x ⊤) ((* x) ⊥)) x Δ) Δ))
(test-equal '((((* x) ⊥) (x ⊥))) (judgment-holds (lv⇓⇓ ((x (~ int))) ((x ⊥)) x Δ) Δ))
(test-equal '(((x ⊥) ((* x) ⊥))) (judgment-holds (lv⇓⇓ ((x (~ int))) ((x ⊥) ((* x) ⊤)) x Δ) Δ))
(test-equal '(((x ⊥) ((* x) ⊥))) (judgment-holds (lv⇓⇓ ((x (~ int))) ((x ⊥) ((* x) ⊥)) x Δ) Δ))

;; evaluate a path down to the address it refers to
(define-judgment-form patina-machine
  #:mode (lv-> I I I I O)
  #:contract(lv-> Γ V μ lv α)
  [  (V= V x α)
   ---------------- "lv-> var"
   (lv-> Γ V μ x α)
   ]
  [(lv-> Γ V μ lv α_1) (μ= μ α_1 α_0)
   ----------------------------------- "lv-> deref"
         (lv-> Γ V μ (* lv) α_0)
   ]
  )

(test-equal '((0 0)) (judgment-holds
                     (lv-> ((x (~ (~ int)))) 
                           ((x (2 0)))
                           (((0 0) ⊥) ((1 0) (0 0)) ((2 0) (1 0)))
                           (* (* x))
                           α)
                     α))

;; typechecking for expressions. tracks initialization of paths
(define-judgment-form patina-checked
  #:mode (rv⊢ I I I I O O)
  #:contract (rv⊢ Γ Δ Σ rv τ Δ)
  [------------------- "rv⊢ int"
   (rv⊢ Γ Δ Σ z int Δ)
   ]
  [(lv⊢ Γ lv_1 int) (lv⇑ Γ Δ lv_1)
   (lv⊢ Γ lv_2 int) (lv⇑ Γ Δ lv_2)
   ------------------------------- "rv⊢ plus"
   (rv⊢ Γ Δ Σ (lv_1 + lv_2) int Δ)
   ]
  [(lv⊢ Γ lv τ) (lv⇑ Γ Δ_0 lv) (lv⇓⇓ Γ Δ_0 lv Δ_1)
   ----------------------------------------------- "rv⊢ lv"
              (rv⊢ Γ Δ_0 Σ lv τ Δ_1)
   ]
  [(lv⊢ Γ lv τ) (lv⇑ Γ Δ_0 lv) (lv⇓⇓ Γ Δ_0 lv Δ_1)
   ----------------------------------------------- "rv⊢ new"
           (rv⊢ Γ Δ_0 Σ (new lv) (~ τ) Δ_1)
   ]
  )

(test-equal '((int ())) (judgment-holds (rv⊢ () () () 0 τ Δ) (τ Δ)))
(test-equal (judgment-holds (rv⊢ ((x int)) ((x ⊤)) () (x + x) τ Δ) (τ Δ)) '((int ((x ⊤)))))
(test-equal (judgment-holds (rv⊢ ((x int)) ((x ⊤)) () x τ Δ) (τ Δ)) '((int ((x ⊥)))))
(test-equal (judgment-holds (rv⊢ ((x int)) ((x ⊤)) () (new x) τ Δ) (τ Δ)) '(((~ int) ((x ⊥)))))

;; evaluate an expression and store the result at the provided address
(define-judgment-form patina-machine
  #:mode (rv-> I I I I I O)
  #:contract (rv-> Γ V μ α rv μ)
  [(μ<- μ α z μ_1)
   -------------------- "rv-> int"
   (rv-> Γ V μ α z μ_1)
   ]
  [(lv-> Γ V μ lv_1 α_1) (μ= μ α_1 z_1)
   (lv-> Γ V μ lv_2 α_2) (μ= μ α_2 z_2)
   (μ<- μ α ,(+ (term z_1) (term z_2)) μ_1)
   ---------------------------------------- "rv-> plus"
   (rv-> Γ V μ α (lv_1 + lv_2) μ_1)
   ]
  [(lv-> Γ V μ lv α_1) (lv⊢ Γ lv τ) (μ-> μ α_1 τ α μ_1)
   ---------------------------------------------------- "rv-> lv"
                 (rv-> Γ V μ α lv μ_1)
   ]
  [(lv-> Γ V μ lv α_1) (lv⊢ Γ lv τ)
   (μ+ μ τ α_2 μ_1) (μ-> μ_1 α_1 τ α_2 μ_2)
   (μ<- μ_2 α α_2 μ_3)
   ---------------------------------------- "rv-> new"
   (rv-> Γ V μ α (new lv) μ_3)
   ]
  )

(test-equal (judgment-holds (rv-> () () (((0 0) ⊥)) (0 0) 0 μ) μ) '((((0 0) 0))))
(test-equal (judgment-holds (rv-> ((x int)) ((x (0 0))) (((0 0) 1) ((1 0) ⊥)) (1 0) (x + x) μ) μ)
            '((((0 0) 1) ((1 0) 2))))
(test-equal (judgment-holds (rv-> ((x int)) ((x (0 0))) (((0 0) 1) ((1 0) ⊥)) (1 0) x μ) μ)
            '((((0 0) ⊥) ((1 0) 1))))
(test-equal (judgment-holds (rv-> ((x int) (y (~ int))) ((x (0 0)) (y (1 0))) 
                                  (((0 0) 1) ((1 0) ⊥)) (1 0) (new x) μ) μ)
            '((((0 0) ⊥) ((1 0) (2 0)) ((2 0) 1))))

;; typechecking for statements
; TODO remove paths from Δ when they are freed
(define-judgment-form patina-checked
  #:mode (s⊢ I I I I O)
  #:contract (s⊢ Γ Δ Σ s Δ)
  [--------------- "s⊢ skip"
   (s⊢ Γ Δ Σ () Δ)
   ]
  [(s⊢ Γ Δ_0 Σ s_1 Δ_1) (s⊢ Γ Δ_1 Σ (s_2 ...) Δ_2)
  ------------------------------------------------ "s⊢ seq"
         (s⊢ Γ Δ_0 Σ (s_1 s_2 ...) Δ_2)
   ]
  [(where Γ_1 ,(cons (term (x τ)) (term Γ_0)))
   (lv⇓⇓ Γ_1 Δ_0 x Δ_1)
   (s⊢ Γ_1 Δ_1 Σ (block (vd_0 ...) s ()) Δ_2)
   ;(lv⇓ Γ_1 Δ_2 x)
   (lv↓ Γ_1 Δ_2 x)
   ---------------------------------------------------------- "s⊢ block alloc"
   (s⊢ Γ_0 Δ_0 Σ (block ((x : τ) vd_0 ...) s ()) Δ_2)
   ]
  [          (s⊢ Γ Δ_0 Σ s Δ_1)   
   -------------------------------------- "s⊢ block"
   (s⊢ Γ Δ_0 Σ (block () s ()) Δ_1)
   ]
  [(lv⊢ Γ lv τ)
   (lv↓ Γ Δ_0 lv)
   (rv⊢ Γ Δ_0 Σ rv τ Δ_1)
   (lv⇑⇑ Γ Δ_1 lv Δ_2)
   -------------------------- "s⊢ assign"
   (s⊢ Γ Δ_0 Σ (lv = rv) Δ_2)
   ]
  [(lv⊢ Γ lv τ)
   (lv↓ Γ Δ_0 lv) ; subpaths are uninitialized
   (Δ= Δ_0 lv ⊤) ; but the path is initialized (prevents double/unnecessary deletes)
   (lv⇓⇓ Γ Δ_0 lv Δ_1)
   ------------------------- "s⊢ delete"
   (s⊢ Γ Δ_0 Σ (delete lv) Δ_1)
   ]
  )

(test-equal (judgment-holds (s⊢ () () () () Δ) Δ) '(()))
(test-equal (judgment-holds (s⊢ () () () (() ()) Δ) Δ) '(()))
(test-equal (judgment-holds (s⊢ () () () (block ((x : int)) () ()) Δ) Δ) '(((x ⊥))))
(test-equal (judgment-holds (s⊢ ((x int)) ((x ⊥)) () (x = 1) Δ) Δ) '(((x ⊤))))
(test-equal (judgment-holds (s⊢ ((x int) (y int)) ((x ⊤) (y ⊥)) () (y = x) Δ) Δ) '(((x ⊥) (y ⊤))))
(test-equal (judgment-holds (s⊢ ((x int) (y int)) ((x ⊤) (y ⊥)) () ((y = x) (x = y)) Δ) Δ) '(((x ⊤) (y ⊥))))
(test-equal (judgment-holds (s⊢ ((x int) (y int)) ((x ⊤) (y ⊥)) () ((y = x) (y = x)) Δ) Δ) '())
(test-equal (judgment-holds (s⊢ ((x int)) ((x ⊤)) () (delete x) Δ) Δ) '(((x ⊥))))
(test-equal (judgment-holds (s⊢ ((x (~ int))) ((x ⊤) ((* x) ⊥)) () (delete x) Δ) Δ) 
	    '(((x ⊥) ((* x) ⊥))))
(test-equal (judgment-holds (s⊢ ((x (~ int))) ((x ⊤) ((* x) ⊤)) () (delete (* x)) Δ) Δ)
	    '(((x ⊤) ((* x) ⊥))))
(test-equal (judgment-holds (s⊢ ((x (~ int))) ((x ⊤) ((* x) ⊤)) () (delete x) Δ) Δ) '())
(test-equal (judgment-holds (s⊢ ((x int)) ((x ⊤)) () ((delete x) (delete x)) Δ) Δ) '())
(test-equal (judgment-holds (s⊢ ((x (~ int))) ((x ⊤) ((* x) ⊤)) () ((delete (* x)) (delete (* x))) Δ) Δ) '())
(test-equal (judgment-holds (s⊢ ((x (~ int)) (y int)) ((x ⊤) ((* x) ⊤) (y ⊥)) () ((y = (* x)) (delete (* x))) Δ) Δ) '())

;; small-step evaluation for statements
(define-judgment-form patina-machine
  #:mode (s-> I I I I O O O O)
  #:contract (s-> Γ V μ s Γ V μ s)
  [------------------------------------ "s-> seq skip"
   (s-> Γ V μ (() s ...) Γ V μ (s ...))
   ]
  [         (s-> Γ_0 V_0 μ_0 s_0 Γ_1 V_1 μ_1 s_1)
   --------------------------------------------------------- "s-> seq step"
   (s-> Γ_0 V_0 μ_0 (s_0 s_2 ...) Γ_1 V_1 μ_1 (s_1 s_2 ...))
   ]
  [------------------------------------- "s-> block skip"
   (s-> Γ V μ (block () () ()) Γ V μ ())
   ]
  [                  (s-> Γ_0 V_0 μ_0 s_0 Γ_1 V_1 μ_1 s_1)
   ----------------------------------------------------------------------------- "s-> block step"
   (s-> Γ_0 V_0 μ_0 (block () s_0 (vd ...)) Γ_1 V_1 μ_1 (block () s_1 (vd ...)))
   ]
  [  (μ+ μ_0 τ α μ_1) (where Γ_1 ,(cons (term (x τ)) (term Γ_0))) (where V_1 ,(cons (term (x α)) (term V_0)))
   ------------------------------------------------------------------------------------------------------------- "s-> block alloc"
   (s-> Γ_0 V_0 μ_0 (block ((x : τ) vd_0 ...) s (vd_1 ...)) Γ_1 V_1 μ_1 (block (vd_0 ...) s ((x : τ) vd_1 ...)))
   ]
  [(where ((x_s τ_s) ... (x τ) (x_e τ_e) ...) Γ_0)
   (where ((x_s α_s) ... (x α) (x_e α_e) ...) V_0)
   (μ- μ_0 τ α μ_1)
   (where Γ_1 ((x_s τ_s) ... (x_e τ_e) ...))
   (where V_1 ((x_s α_s) ... (x_e α_e) ...))
   ----------------------------------------------------------------------------------- "s-> block free"
   (s-> Γ_0 V_0 μ_0 (block () () ((x : τ) vd ...)) Γ_1 V_1 μ_1 (block () () (vd ...)))
   ]
  [(lv-> Γ V μ_0 lv α)
   (rv-> Γ V μ_0 α rv μ_1)
   ---------------------------------- "s-> assignment"
   (s-> Γ V μ_0 (lv = rv) Γ V μ_1 ())
   ]
  [------------------------------- "s-> delete variable"
   (s-> Γ V μ (delete x) Γ V μ ())
   ]
  [(lv⊢ Γ lv (~ τ))
   (lv-> Γ V μ_0 (* lv) α)
   (μ- μ_0 τ α μ_1)
   ---------------------------------------- "s-> delete owned pointer"
   (s-> Γ V μ_0 (delete (* lv)) Γ V μ_1 ())
   ]
  )

(test-equal '((() () () (() ()))) (judgment-holds (s-> () () () (() () ()) Γ V μ s) (Γ V μ s)))
(test-equal '((() () () ())) (judgment-holds (s-> () () () (block () () ()) Γ V μ s) (Γ V μ s)))
(test-equal (judgment-holds (s-> () () () (block ((x : int)) () ()) Γ V μ s) (Γ V μ s))
	    '((((x int)) ((x (0 0))) (((0 0) ⊥)) (block () () ((x : int))))))
(test-equal (judgment-holds (s-> ((x int)) ((x (0 0))) (((0 0) ⊥)) (block () () ((x : int))) Γ V μ s) (Γ V μ s))
	    '((() () () (block () () ()))))
(test-equal (judgment-holds (s-> ((x int) (y int)) ((x (0 0)) (y (1 0))) (((0 0) 1) ((1 0) ⊥)) (y = x) Γ V μ s) (Γ V μ s))
	    '((((x int) (y int)) ((x (0 0)) (y (1 0))) (((0 0) ⊥) ((1 0) 1)) ())))
(test-equal (judgment-holds (s-> ((x int)) ((x (0 0))) (((0 0) 1)) (delete x) Γ V μ s) (Γ V μ s))
	    '((((x int)) ((x (0 0))) (((0 0) 1)) ())))
(test-equal (judgment-holds (s-> ((x (~ int))) ((x (0 0))) (((0 0) (1 0)) ((1 0) 1)) (delete (* x)) Γ V μ s) (Γ V μ s))
	    '((((x (~ int))) ((x (0 0))) (((0 0) (1 0))) ())))

(define patina-step
  (reduction-relation patina-machine
    [--> (Γ_0 V_0 μ_0 s_0)
         (Γ_1 V_1 μ_1 s_1)
         (judgment-holds (s-> Γ_0 V_0 μ_0 s_0 Γ_1 V_1 μ_1 s_1))]))

(test-equal #t
(judgment-holds
  (s⊢ () () ()
    (block ((x : int) (y : (~ int)) (z : int)) 
           ((x = 1) 
            (y = (new x))
            (z = (* y))
            ((* y) = z) 
            (delete (* y))
            ) 
           ())
    Δ))
)

(test-equal '((() () () ()))
(apply-reduction-relation* patina-step
  (term  (() () ()
    (block ((x : int) (y : (~ int)) (z : int)) 
           ((x = 1) 
            (y = (new x))
            (z = (* y))
            ((* y) = z) 
            (delete (* y))
            ) 
           ()))))
)

(test-results)
