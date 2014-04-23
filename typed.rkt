#lang racket
(require redex)

;;;; SYNTAX
(define-language patina
  ;; variables (α-convertible)
  (x variable-not-otherwise-mentioned)

  ;; lifetimes / labels
  (ℓ variable-not-otherwise-mentioned)

  ;; integers
  (z integer)

  ;; mutability qualifiers
  (mq mut ; mutable
      imm ; immutable
      )

  ;; paths (lhs values)
  (lv x      ; variable
      (* lv) ; pointer dereference
      )

  ;; expressions (rhs values)
  (rv z		  ; integer constants
      (lv + lv)	  ; addition (copies operands)
      lv	  ; use by moving from a path
      (new lv)	  ; move from a path into a new heap allocation
      (& ℓ mq lv) ; create a borrowed reference with mutability rights `mq` guaranteed for lifetime `ℓ`
      )

  ;; types
  (τ int	; integers
     (~ τ)	; owned pointer
     (& ℓ mq τ) ; borrowed reference with lifetime `ℓ` and mutability rights `mq`
     )

  ;; variable declaration
  (vd (x : τ))

  ;; statements
  (s  ; sequence of statements
     (s ...) 
      ; extend context in a fresh lifetime by pushing onto the stack,
      ; execute a statement,
      ; and then pop all that off the stack.
     (block ℓ (vd ...) s (vd ...)) 
      ; assign to a path (path must be uninitialized)
     (lv = rv)
      ; shallow destruction.
      ; subpaths must already be uninitialized.
      ; frees heap memory.
     (delete lv)
     )
  )

;;;; TYPING
(define-extended-language patina-checked patina
  ;; context mapping variables to types
  ; NB type checking results available at runtime
  (Γ ((x τ) ...))
  ;; lifetime of variables (i.e. lifetime of the block they are declared in)
  (Λ ((x ℓ) ...))
  ;; the stack of lifetimes (to define the ordering of lifetimes)
  (L (ℓ ...))
  ;; initialization flags
  (ι ⊥ ; uninitialized
     ⊤ ; initialized
     )
  ;; initialization of allocated paths
  (Δ ((lv ι) ...))
  ;; heap typing
  (Σ ((α τ) ...))
  ;; actions that can be forbidden by borrows
  (action mutate ; assign to (change the data)
          claim  ; borrow mutably (claim sole mutability rights)
          freeze ; borrow immutably (prevent data mutating underneath the borrow)
          )
  ;; a restriction is a path and a list of forbidden actions (empty list implies move is forbidden
  (restriction (lv (action ...)))
  ;; a loan on a path for a certain lifetime and mutability carries a list of restrictions that prevent loan invalidation
  (loan (lv ℓ mq (restriction ...)))
  ;; the set of current loans (who holds the loans? well the bank of course)
  ($ (loan ...))
  )

;; lookup type of a variable
(define-judgment-form patina-checked
  #:mode (Γ= I I O)
  #:contract (Γ= Γ x τ)
  [-------------------------------------------- "Γ="
   (Γ= ((x_s _) ... (x_0 τ) (x_e _) ...) x_0 τ)
   ]
  )

(test-equal '(int) (judgment-holds (Γ= ((x int)) x τ) τ))

;; lookup lifetime of a variable
(define-judgment-form patina-checked
  #:mode (Λ= I I O)
  #:contract (Λ= Λ x ℓ)
  [-------------------------------------------- "Λ="
   (Λ= ((x_s _) ... (x_0 ℓ) (x_e _) ...) x_0 ℓ)
   ]
  )

(test-equal '(ℓ0) (judgment-holds (Λ= ((x ℓ0)) x ℓ) ℓ))

;; ℓ₁ ≤ ℓ₂ (ℓ₁ does not exceed ℓ₂)
(define-judgment-form patina-checked
  #:mode (ℓ≤ I I I)
  #:contract (ℓ≤ L ℓ ℓ)
  [-------------- "ℓ≤ reflexive"
   (ℓ≤ L ℓ_0 ℓ_0)
   ]
  [---------------------------------------------- "ℓ≤ ordered"
   (ℓ≤ (ℓ_s ... ℓ_0 ℓ_m ... ℓ_1 ℓ_e ...) ℓ_0 ℓ_1)
   ]
  )

(test-equal #t (judgment-holds (ℓ≤ () ℓ0 ℓ0)))
(test-equal #f (judgment-holds (ℓ≤ () ℓ0 ℓ1)))
(test-equal #t (judgment-holds (ℓ≤ (ℓ5 ℓ4 ℓ3 ℓ2 ℓ1 ℓ0) ℓ4 ℓ2)))
(test-equal #t (judgment-holds (ℓ≤ (ℓ5 ℓ4 ℓ3 ℓ2 ℓ1 ℓ0) ℓ4 ℓ4)))
(test-equal #t (judgment-holds (ℓ≤ (ℓ5 ℓ4 ℓ3 ℓ2 ℓ1 ℓ0) ℓ4 ℓ3)))
(test-equal #f (judgment-holds (ℓ≤ (ℓ5 ℓ4 ℓ3 ℓ2 ℓ1 ℓ0) ℓ3 ℓ4)))
(test-equal #f (judgment-holds (ℓ≤ (ℓ5 ℓ4 ℓ3 ℓ2 ℓ1 ℓ0) ℓ6 ℓ4)))

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
  [(where (lv_!_0 lv_!_0) (lv_0 lv_2))
   (Δ? ((lv_1 ι_1) ...) lv_2)
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
   ---------------------------------------- "Δ↑ new"
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
   ---------------------------------------- "Δ↓ new"
   (Δ↓ Δ lv ,(cons (term (lv ⊥)) (term Δ)))
   ]
  )

(test-equal '(((x ⊥) (y ⊤))) (judgment-holds (Δ↓ ((x ⊥) (y ⊤)) x Δ) Δ))
(test-equal '(((x ⊥) (y ⊤))) (judgment-holds (Δ↓ ((x ⊤) (y ⊤)) x Δ) Δ))
(test-equal '(((x ⊥) (y ⊤))) (judgment-holds (Δ↓ ((y ⊤)) x Δ) Δ))

;; check if an action is in an action set
(define-judgment-form patina-checked
  #:mode (action∈ I I)
  #:contract (action∈ (action ...) action)
  [------------------------------------------------------- "action∈"
   (action∈ (action_s ... action_0 action_e ...) action_0)
   ]
  )

(test-equal #t (judgment-holds (action∈ (mutate) mutate)))
(test-equal #f (judgment-holds (action∈ () mutate)))

;; check if an action is not in an action set
(define-judgment-form patina-checked
  #:mode (action∉ I I)
  #:contract (action∉ (action ...) action)
  [------------------- "action∉ empty"
   (action∉ () action)
   ]
  [(where (action_!_0 action_!_0) (action_s action_0))
   (action∉ (action_e ...) action_0)
   --------------------------------------------------- "action∉ cons"
   (action∉ (action_s action_e ...) action_0)
   ]
  )

(test-equal #f (judgment-holds (action∉ (mutate) mutate)))
(test-equal #t (judgment-holds (action∉ (claim) mutate)))

;; union of action sets
(define-judgment-form patina-checked
  #:mode (action∪ I I O)
  #:contract (action∪ (action ...) (action ...) (action ...))
  [(action∈ (action_1 ...) action_0s)
   (action∪ (action_0e ...) (action_1 ...) (action_2 ...))
   ----------------------------------------------------------------- "action∪ - in both"
   (action∪ (action_0s action_0e ...) (action_1 ...) (action_2 ...))
   ]
  [(action∉ (action_1 ...) action_0s)
   (action∪ (action_0e ...) (action_1 ...) (action_2 ...))
   --------------------------------------------------------------------------- "action∪ - in first only"
   (action∪ (action_0s action_0e ...) (action_1 ...) (action_0s action_2 ...))
   ]
  [------------------------------------------ "action∪ - first empty"
   (action∪ () (action_1 ...) (action_1 ...))
   ]
  )

(test-equal (judgment-holds (action∪ () () (action ...)) (action ...)) '(()))
(test-equal (judgment-holds (action∪ () (mutate claim) (action ...)) (action ...)) '((mutate claim)))
(test-equal (judgment-holds (action∪ (claim mutate) () (action ...)) (action ...)) '((claim mutate)))
(test-equal (judgment-holds (action∪ (mutate) (mutate) (action ...)) (action ...)) '((mutate)))
(test-equal (judgment-holds (action∪ (claim) (mutate) (action ...)) (action ...)) '((claim mutate)))
(test-equal (judgment-holds (action∪ (mutate) (claim) (action ...)) (action ...)) '((mutate claim)))

;; subset for action sets
(define-judgment-form patina-checked
  #:mode (action⊆ I I)
  #:contract (action⊆ (action ...) (action ...))
  [(action∈ (action_1 ...) action_0) ...
   --------------------------------------- "action⊆"
   (action⊆ (action_0 ...) (action_1 ...))
   ]
  )

(test-equal #t (judgment-holds (action⊆ () ())))
(test-equal #t (judgment-holds (action⊆ () (mutate))))
(test-equal #f (judgment-holds (action⊆ (mutate) ())))
(test-equal #t (judgment-holds (action⊆ (mutate claim) (claim mutate))))

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
  [(lv⊢ Γ lv (& ℓ mq τ))
   --------------------- "lv⊢ borrow"
   (lv⊢ Γ (* lv) τ)
   ]
  )

(test-equal '(int) (judgment-holds (lv⊢ ((x (~ (~ int)))) (* (* x)) τ) τ))
(test-equal '(int) (judgment-holds (lv⊢ ((x (& ℓ2 imm (& ℓ1 mut int)))) (* (* x)) τ) τ))
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
  [(lv⊢ Γ lv (& ℓ mq τ)) (Δ= Δ lv ⊤) (lv⇑ Γ Δ (* lv))
   -------------------------------------------------- "lv⇑ &'ℓ mq τ"
		    (lv⇑ Γ Δ lv)
   ]
  )

(test-equal #t (judgment-holds (lv⇑ ((x int) (y (~ int))) ((x ⊤) (y ⊤) ((* y) ⊥)) x)))
(test-equal #t (judgment-holds (lv⇑ ((x (~ int))) ((x ⊤) ((* x) ⊤)) x)))
(test-equal #t (judgment-holds (lv⇑ ((x (& ℓ mut int))) ((x ⊤) ((* x) ⊤)) x)))
(test-equal #t (judgment-holds (lv⇑ ((x (& ℓ imm int))) ((x ⊤) ((* x) ⊤)) x)))
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
  ;[(lv⊢ Γ lv (& ℓ mq τ)) (Δ= Δ lv ⊥) (lv⇓ Γ Δ (* lv))
  [(lv⊢ Γ lv (& ℓ mq τ)) (Δ= Δ lv ⊥) ;(lv⇓ Γ Δ (* lv)) ; TODO figure out
   -------------------------------------------------- "lv⇓ &'ℓ mq τ"
		    (lv⇓ Γ Δ lv)
   ]
  )

(test-equal #f (judgment-holds (lv⇓ ((x int) (y (~ int))) ((x ⊤) (y ⊤) ((* y) ⊥)) x)))
(test-equal #f (judgment-holds (lv⇓ ((x int) (y (~ int))) ((x ⊤) (y ⊤) ((* y) ⊥)) y)))
(test-equal #t (judgment-holds (lv⇓ ((x int) (y (~ int))) ((x ⊤) (y ⊤) ((* y) ⊥)) (* y))))
(test-equal #t (judgment-holds (lv⇓ ((x int) (y (~ int))) ((x ⊤) (y ⊥) ((* y) ⊥)) y)))
(test-equal #t (judgment-holds (lv⇓ ((x (& ℓ mut int))) ((x ⊥) ((* x) ⊥)) x)))
(test-equal #t (judgment-holds (lv⇓ ((x (& ℓ imm int))) ((x ⊥) ((* x) ⊥)) x)))
(test-equal #f (judgment-holds (lv⇓ ((x (& ℓ mut int))) ((x ⊥) ((* x) ⊤)) x)))
(test-equal #f (judgment-holds (lv⇓ ((x (& ℓ imm int))) ((x ⊥) ((* x) ⊤)) x)))

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
  [(lv⊢ Γ lv (& ℓ mq τ)) (lv⇑⇑ Γ Δ_0 (* lv) Δ_1) (Δ↑ Δ_1 lv Δ_2)
   ------------------------------------------------------------- "lv⇑⇑ &'ℓ mq τ"
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
(test-equal '(((x ⊤) ((* x) ⊤))) (judgment-holds (lv⇑⇑ ((x (& ℓ mut int))) () x Δ) Δ))
(test-equal '(((x ⊤) ((* x) ⊤))) (judgment-holds (lv⇑⇑ ((x (& ℓ imm int))) () x Δ) Δ))

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
  [(lv⊢ Γ lv (& ℓ mq τ)) (lv⇓⇓ Γ Δ_0 (* lv) Δ_1) (Δ↓ Δ_1 lv Δ_2)
   ------------------------------------------------------------- "lv⇓⇓ &'ℓ mq τ"
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
(test-equal '(((x ⊥) ((* x) ⊥))) (judgment-holds (lv⇓⇓ ((x (& ℓ mut int))) () x Δ) Δ))
(test-equal '(((x ⊥) ((* x) ⊥))) (judgment-holds (lv⇓⇓ ((x (& ℓ imm int))) () x Δ) Δ))

;; mutability compatibility for borrowing
(define-judgment-form patina-checked
  #:mode (mutability I I I)
  #:contract (mutability Γ lv mq)
  [; all variables in patina are mutable
   ------------------- "mutability - variable"
   (mutability Γ x mq)
   ]
  [(lv⊢ Γ lv (& ℓ imm τ)) ; we can only borrow immutable pointers immutably
   ------------------------- "mutability - immutable borrow"
   (mutability Γ (* lv) imm)
   ]
  [(lv⊢ Γ lv (& ℓ mut τ))
   ------------------------ "mutability - mutable borrow"
   (mutability Γ (* lv) mq)
   ]
  [(lv⊢ Γ lv (~ τ)) (mutability Γ lv mq)
   ------------------------------------- "mutability - owned pointer"
	 (mutability Γ (* lv) mq)
   ]
  )

(test-equal #t (judgment-holds (mutability ((x int)) x mut)))
(test-equal #t (judgment-holds (mutability ((x int)) x imm)))
(test-equal #t (judgment-holds (mutability ((x (& ℓ imm int))) (* x) imm)))
(test-equal #f (judgment-holds (mutability ((x (& ℓ imm int))) (* x) mut)))
(test-equal #t (judgment-holds (mutability ((x (& ℓ mut int))) (* x) imm)))
(test-equal #t (judgment-holds (mutability ((x (& ℓ mut int))) (* x) mut)))
(test-equal #t (judgment-holds (mutability ((x (~ int))) (* x) imm)))
(test-equal #t (judgment-holds (mutability ((x (~ int))) (* x) mut)))
(test-equal #t (judgment-holds (mutability ((x (~ (& ℓ imm int)))) (* x) imm)))
(test-equal #t (judgment-holds (mutability ((x (~ (& ℓ imm int)))) (* x) mut)))
(test-equal #t (judgment-holds (mutability ((x (~ (& ℓ imm int)))) (* (* x)) imm)))
(test-equal #f (judgment-holds (mutability ((x (~ (& ℓ imm int)))) (* (* x)) mut)))

;; aliasability compatibility for borrowing
(define-judgment-form patina-checked
  #:mode (aliasable I I I)
  #:contract (aliasable Γ lv mq)
  [------------------ "aliasable - variable"
   (aliasable Γ x mq)
   ]
  [(lv⊢ Γ lv (~ τ))
   (aliasable Γ lv mq)
   ----------------------- "aliasable - owned pointer"
   (aliasable Γ (* lv) mq)
   ]
  [(lv⊢ Γ lv (& ℓ imm τ))
   ------------------------ "aliasable - immutable borrow"
   (aliasable Γ (* lv) imm)
   ]
  [(lv⊢ Γ lv (& ℓ mut τ))
   ----------------------- "aliasable - mutable borrow"
   (aliasable Γ (* lv) mq)
   ]
  )

(test-equal #t (judgment-holds (aliasable ((x int)) x mut)))
(test-equal #t (judgment-holds (aliasable ((x int)) x imm)))
(test-equal #t (judgment-holds (aliasable ((x (~ int))) (* x) mut)))
(test-equal #t (judgment-holds (aliasable ((x (~ int))) (* x) imm)))
(test-equal #t (judgment-holds (aliasable ((x (& ℓ mut int))) (* x) mut)))
(test-equal #t (judgment-holds (aliasable ((x (& ℓ mut int))) (* x) imm)))
(test-equal #t (judgment-holds (aliasable ((x (& ℓ imm int))) (* x) imm)))
(test-equal #f (judgment-holds (aliasable ((x (& ℓ imm int))) (* x) mut)))

;; scope of a path (lifetime of the path)
(define-judgment-form patina-checked
  #:mode (scope I I I O)
  #:contract (scope Γ Λ lv ℓ)
  [(Λ= Λ x ℓ)
   --------------- "scope - variable"
   (scope Γ Λ x ℓ)
   ]
  [(lv⊢ Γ lv (~ τ))
   (scope Γ Λ lv ℓ)
   -------------------- "scope - owned pointer"
   (scope Γ Λ (* lv) ℓ)
   ]
  [(lv⊢ Γ lv (& ℓ mq τ))
   --------------------- "scope - borrowed pointer"
   (scope Γ Λ (* lv) ℓ)
   ]
  )

(test-equal '(ℓ0) (judgment-holds (scope ((x int)) ((x ℓ0)) x ℓ) ℓ))
(test-equal '(ℓ0) (judgment-holds (scope ((x (~ (~ int)))) ((x ℓ0)) x ℓ) ℓ))
(test-equal '(ℓ0) (judgment-holds (scope ((x (~ (~ int)))) ((x ℓ0)) (* x) ℓ) ℓ))
(test-equal '(ℓ0) (judgment-holds (scope ((x (~ (~ int)))) ((x ℓ0)) (* (* x)) ℓ) ℓ))
(test-equal '(ℓ0) (judgment-holds (scope ((x (& ℓ0 imm (& ℓ1 imm int)))) ((x ℓ0)) x ℓ) ℓ))
(test-equal '(ℓ0) (judgment-holds (scope ((x (& ℓ0 imm (& ℓ1 imm int)))) ((x ℓ0)) (* x) ℓ) ℓ))
(test-equal '(ℓ1) (judgment-holds (scope ((x (& ℓ0 imm (& ℓ1 imm int)))) ((x ℓ0)) (* (* x)) ℓ) ℓ))
(test-equal '(ℓ0) (judgment-holds (scope ((x (& ℓ0 mut (& ℓ1 imm int)))) ((x ℓ0)) x ℓ) ℓ))
(test-equal '(ℓ0) (judgment-holds (scope ((x (& ℓ0 mut (& ℓ1 imm int)))) ((x ℓ0)) (* x) ℓ) ℓ))
(test-equal '(ℓ1) (judgment-holds (scope ((x (& ℓ0 mut (& ℓ1 imm int)))) ((x ℓ0)) (* (* x)) ℓ) ℓ))
(test-equal '(ℓ0) (judgment-holds (scope ((x (& ℓ0 imm (& ℓ1 mut int)))) ((x ℓ0)) x ℓ) ℓ))
(test-equal '(ℓ0) (judgment-holds (scope ((x (& ℓ0 imm (& ℓ1 mut int)))) ((x ℓ0)) (* x) ℓ) ℓ))
(test-equal '(ℓ1) (judgment-holds (scope ((x (& ℓ0 imm (& ℓ1 mut int)))) ((x ℓ0)) (* (* x)) ℓ) ℓ))
(test-equal '(ℓ0) (judgment-holds (scope ((x (& ℓ0 mut (& ℓ1 mut int)))) ((x ℓ0)) x ℓ) ℓ))
(test-equal '(ℓ0) (judgment-holds (scope ((x (& ℓ0 mut (& ℓ1 mut int)))) ((x ℓ0)) (* x) ℓ) ℓ))
(test-equal '(ℓ1) (judgment-holds (scope ((x (& ℓ0 mut (& ℓ1 mut int)))) ((x ℓ0)) (* (* x)) ℓ) ℓ))
(test-equal '(ℓ0) (judgment-holds (scope ((x (& ℓ0 imm (~ int)))) ((x ℓ0)) x ℓ) ℓ))
(test-equal '(ℓ0) (judgment-holds (scope ((x (& ℓ0 imm (~ int)))) ((x ℓ0)) (* x) ℓ) ℓ))
(test-equal '(ℓ0) (judgment-holds (scope ((x (& ℓ0 imm (~ int)))) ((x ℓ0)) (* (* x)) ℓ) ℓ))
(test-equal '(ℓ0) (judgment-holds (scope ((x (& ℓ0 mut (~ int)))) ((x ℓ0)) x ℓ) ℓ))
(test-equal '(ℓ0) (judgment-holds (scope ((x (& ℓ0 mut (~ int)))) ((x ℓ0)) (* x) ℓ) ℓ))
(test-equal '(ℓ0) (judgment-holds (scope ((x (& ℓ0 mut (~ int)))) ((x ℓ0)) (* (* x)) ℓ) ℓ))

;; lifetime of a borrow does not exceed the lifetime of the borrowee
(define-judgment-form patina-checked
  #:mode (lifetime I I I I I I)
  #:contract (lifetime Γ Λ L lv ℓ mq)
  [(scope Γ Λ x ℓ_x) 
   (ℓ≤ L ℓ ℓ_x)
   --------------------- "lifetime - variable"
   (lifetime Γ Λ L x ℓ mq)
   ]
  [(lv⊢ Γ lv (~ τ))
   (lifetime Γ Λ L lv ℓ mq)
   ---------------------------- "lifetime - owned pointer"
   (lifetime Γ Λ L (* lv) ℓ mq)
   ]
  [(lv⊢ Γ lv (& ℓ_1 _ τ))
   (ℓ≤ L ℓ_0 ℓ_1)
   ---------------------------- "lifetime - borrowed pointer"
   (lifetime Γ Λ L (* lv) ℓ_0 mq)
   ]
  )

(test-equal #t (judgment-holds (lifetime ((x int)) ((x ℓ0)) (ℓ1 ℓ0) x ℓ1 imm)))
(test-equal #t (judgment-holds (lifetime ((x int)) ((x ℓ0)) (ℓ1 ℓ0) x ℓ1 mut)))
(test-equal #t (judgment-holds (lifetime ((x int)) ((x ℓ0)) (ℓ1 ℓ0) x ℓ0 imm)))
(test-equal #t (judgment-holds (lifetime ((x int)) ((x ℓ0)) (ℓ1 ℓ0) x ℓ0 mut)))
(test-equal #f (judgment-holds (lifetime ((x int)) ((x ℓ1)) (ℓ1 ℓ0) x ℓ0 imm)))
(test-equal #f (judgment-holds (lifetime ((x int)) ((x ℓ1)) (ℓ1 ℓ0) x ℓ0 mut)))
(test-equal #t (judgment-holds (lifetime ((x int)) ((x ℓ1)) (ℓ1 ℓ0) x ℓ1 imm)))
(test-equal #t (judgment-holds (lifetime ((x int)) ((x ℓ1)) (ℓ1 ℓ0) x ℓ1 mut)))
(test-equal #f (judgment-holds (lifetime ((x int)) ((x ℓ1)) (ℓ1 ℓ0) x ℓ2 imm)))
(test-equal #f (judgment-holds (lifetime ((x int)) ((x ℓ1)) (ℓ1 ℓ0) x ℓ2 mut)))
(test-equal #t (judgment-holds (lifetime ((x (~ int))) ((x ℓ0)) (ℓ1 ℓ0) (* x) ℓ0 imm)))
(test-equal #t (judgment-holds (lifetime ((x (~ int))) ((x ℓ0)) (ℓ1 ℓ0) (* x) ℓ0 mut)))
(test-equal #t (judgment-holds (lifetime ((x (~ int))) ((x ℓ0)) (ℓ1 ℓ0) (* x) ℓ1 imm)))
(test-equal #t (judgment-holds (lifetime ((x (~ int))) ((x ℓ0)) (ℓ1 ℓ0) (* x) ℓ1 mut)))
(test-equal #t (judgment-holds (lifetime ((x (& ℓ0 mut int))) ((x ℓ0)) (ℓ1 ℓ0) (* x) ℓ0 imm)))
(test-equal #t (judgment-holds (lifetime ((x (& ℓ0 mut int))) ((x ℓ0)) (ℓ1 ℓ0) (* x) ℓ0 mut)))
(test-equal #t (judgment-holds (lifetime ((x (& ℓ0 mut int))) ((x ℓ0)) (ℓ1 ℓ0) (* x) ℓ1 imm)))
(test-equal #t (judgment-holds (lifetime ((x (& ℓ0 mut int))) ((x ℓ0)) (ℓ1 ℓ0) (* x) ℓ1 mut)))
(test-equal #f (judgment-holds (lifetime ((x (& ℓ1 mut int))) ((x ℓ1)) (ℓ1 ℓ0) (* x) ℓ0 imm)))
(test-equal #f (judgment-holds (lifetime ((x (& ℓ1 mut int))) ((x ℓ1)) (ℓ1 ℓ0) (* x) ℓ0 mut)))
(test-equal #t (judgment-holds (lifetime ((x (& ℓ1 mut int))) ((x ℓ1)) (ℓ1 ℓ0) (* x) ℓ1 imm)))
(test-equal #t (judgment-holds (lifetime ((x (& ℓ1 mut int))) ((x ℓ1)) (ℓ1 ℓ0) (* x) ℓ1 mut)))

;; compute the restrictions required to prevent borrow invalidation
(define-judgment-form patina-checked
  #:mode (restrictions I I I I I O)
  #:contract (restrictions Γ L lv ℓ (action ...) (restriction ...))
  [---------------------------------------------------- "restrictions - variable"
   (restrictions Γ L x ℓ (action ...) ((x (action ...))))
   ]
  [(lv⊢ Γ lv (~ τ))
   (action∪ (mutate claim) (action ...) (action_1 ...))
   (restrictions Γ L lv ℓ (action_1 ...) (restriction_s ...))
   ---------------------------------------------------------------------------------- "restrictions - owned pointer"
   (restrictions Γ L (* lv) ℓ (action ...) (restriction_s ... ((* lv) (action ...))))
   ]
  [(lv⊢ Γ lv (& ℓ_1 imm τ))
   (ℓ≤ L ℓ_0 ℓ_1)
   (action⊆ (action ...) (mutate claim))
   --------------------------------------------- "restrictions - immutable borrow"
   (restrictions Γ L (* lv) ℓ_0 (action ...) ())
   ]
  [(lv⊢ Γ lv (& ℓ_1 mut τ))
   (ℓ≤ L ℓ_0 ℓ_1)
   (restrictions Γ L lv ℓ_0 (action ...) (restriction_s ...))
   ------------------------------------------------------------------------------------ "restrictions - mutable borrow"
   (restrictions Γ L (* lv) ℓ_0 (action ...) (restriction_s ... ((* lv) (action ...))))
   ]
  )

(test-equal (judgment-holds (restrictions ((x int)) (ℓ1 ℓ0) x ℓ0 (mutate claim) (restriction ...)) (restriction ...)) '(((x (mutate claim)))))
(test-equal (judgment-holds (restrictions ((x int)) (ℓ1 ℓ0) x ℓ0 (mutate claim freeze) (restriction ...)) (restriction ...)) '(((x (mutate claim freeze)))))
(test-equal (judgment-holds (restrictions ((x int)) (ℓ1 ℓ0) x ℓ1 (mutate claim) (restriction ...)) (restriction ...)) '(((x (mutate claim)))))
(test-equal (judgment-holds (restrictions ((x int)) (ℓ1 ℓ0) x ℓ1 (mutate claim freeze) (restriction ...)) (restriction ...)) '(((x (mutate claim freeze)))))
(test-equal (judgment-holds (restrictions ((x (~ int))) (ℓ1 ℓ0) (* x) ℓ0 (mutate claim) (restriction ...)) (restriction ...)) '(((x (mutate claim)) ((* x) (mutate claim)))))
(test-equal (judgment-holds (restrictions ((x (~ int))) (ℓ1 ℓ0) (* x) ℓ0 (mutate claim freeze) (restriction ...)) (restriction ...)) '(((x (mutate claim freeze)) ((* x) (mutate claim freeze)))))
(test-equal (judgment-holds (restrictions ((x (~ int))) (ℓ1 ℓ0) (* x) ℓ1 (mutate claim) (restriction ...)) (restriction ...)) '(((x (mutate claim)) ((* x) (mutate claim)))))
(test-equal (judgment-holds (restrictions ((x (~ int))) (ℓ1 ℓ0) (* x) ℓ1 (mutate claim freeze) (restriction ...)) (restriction ...)) '(((x (mutate claim freeze)) ((* x) (mutate claim freeze)))))
(test-equal (judgment-holds (restrictions ((x (& ℓ0 imm int))) (ℓ1 ℓ0) (* x) ℓ0 (mutate claim) (restriction ...)) (restriction ...)) '(()))
(test-equal (judgment-holds (restrictions ((x (& ℓ0 imm int))) (ℓ1 ℓ0) (* x) ℓ0 (mutate claim) (restriction ...)) (restriction ...)) '(()))
(test-equal (judgment-holds (restrictions ((x (& ℓ0 imm int))) (ℓ1 ℓ0) (* x) ℓ1 (mutate claim) (restriction ...)) (restriction ...)) '(()))
(test-equal (judgment-holds (restrictions ((x (& ℓ0 imm int))) (ℓ1 ℓ0) (* x) ℓ1 (mutate claim) (restriction ...)) (restriction ...)) '(()))
(test-equal (judgment-holds (restrictions ((x (& ℓ1 imm int))) (ℓ1 ℓ0) (* x) ℓ0 (mutate claim) (restriction ...)) (restriction ...)) '())
(test-equal (judgment-holds (restrictions ((x (& ℓ1 imm int))) (ℓ1 ℓ0) (* x) ℓ0 (mutate claim) (restriction ...)) (restriction ...)) '())
(test-equal (judgment-holds (restrictions ((x (& ℓ1 imm int))) (ℓ1 ℓ0) (* x) ℓ1 (mutate claim) (restriction ...)) (restriction ...)) '(()))
(test-equal (judgment-holds (restrictions ((x (& ℓ1 imm int))) (ℓ1 ℓ0) (* x) ℓ1 (mutate claim) (restriction ...)) (restriction ...)) '(()))
(test-equal (judgment-holds (restrictions ((x (& ℓ0 mut int))) (ℓ1 ℓ0) (* x) ℓ0 (mutate claim) (restriction ...)) (restriction ...)) '(((x (mutate claim)) ((* x) (mutate claim)))))
(test-equal (judgment-holds (restrictions ((x (& ℓ0 mut int))) (ℓ1 ℓ0) (* x) ℓ0 (mutate claim) (restriction ...)) (restriction ...)) '(((x (mutate claim)) ((* x) (mutate claim)))))
(test-equal (judgment-holds (restrictions ((x (& ℓ0 mut int))) (ℓ1 ℓ0) (* x) ℓ1 (mutate claim) (restriction ...)) (restriction ...)) '(((x (mutate claim)) ((* x) (mutate claim)))))
(test-equal (judgment-holds (restrictions ((x (& ℓ0 mut int))) (ℓ1 ℓ0) (* x) ℓ1 (mutate claim) (restriction ...)) (restriction ...)) '(((x (mutate claim)) ((* x) (mutate claim)))))
(test-equal (judgment-holds (restrictions ((x (& ℓ1 mut int))) (ℓ1 ℓ0) (* x) ℓ0 (mutate claim) (restriction ...)) (restriction ...)) '())
(test-equal (judgment-holds (restrictions ((x (& ℓ1 mut int))) (ℓ1 ℓ0) (* x) ℓ0 (mutate claim) (restriction ...)) (restriction ...)) '())
(test-equal (judgment-holds (restrictions ((x (& ℓ1 mut int))) (ℓ1 ℓ0) (* x) ℓ1 (mutate claim) (restriction ...)) (restriction ...)) '(((x (mutate claim)) ((* x) (mutate claim)))))
(test-equal (judgment-holds (restrictions ((x (& ℓ1 mut int))) (ℓ1 ℓ0) (* x) ℓ1 (mutate claim) (restriction ...)) (restriction ...)) '(((x (mutate claim)) ((* x) (mutate claim)))))
(test-equal (judgment-holds (restrictions ((x (& ℓ0 imm int))) (ℓ1 ℓ0) (* x) ℓ0 (mutate claim freeze) (restriction ...)) (restriction ...)) '())
(test-equal (judgment-holds (restrictions ((x (& ℓ0 imm int))) (ℓ1 ℓ0) (* x) ℓ0 (mutate claim freeze) (restriction ...)) (restriction ...)) '())
(test-equal (judgment-holds (restrictions ((x (& ℓ0 imm int))) (ℓ1 ℓ0) (* x) ℓ1 (mutate claim freeze) (restriction ...)) (restriction ...)) '())
(test-equal (judgment-holds (restrictions ((x (& ℓ0 imm int))) (ℓ1 ℓ0) (* x) ℓ1 (mutate claim freeze) (restriction ...)) (restriction ...)) '())
(test-equal (judgment-holds (restrictions ((x (& ℓ1 imm int))) (ℓ1 ℓ0) (* x) ℓ0 (mutate claim freeze) (restriction ...)) (restriction ...)) '())
(test-equal (judgment-holds (restrictions ((x (& ℓ1 imm int))) (ℓ1 ℓ0) (* x) ℓ0 (mutate claim freeze) (restriction ...)) (restriction ...)) '())
(test-equal (judgment-holds (restrictions ((x (& ℓ1 imm int))) (ℓ1 ℓ0) (* x) ℓ1 (mutate claim freeze) (restriction ...)) (restriction ...)) '())
(test-equal (judgment-holds (restrictions ((x (& ℓ1 imm int))) (ℓ1 ℓ0) (* x) ℓ1 (mutate claim freeze) (restriction ...)) (restriction ...)) '())
(test-equal (judgment-holds (restrictions ((x (& ℓ0 mut int))) (ℓ1 ℓ0) (* x) ℓ0 (mutate claim freeze) (restriction ...)) (restriction ...)) '(((x (mutate claim freeze)) ((* x) (mutate claim freeze)))))
(test-equal (judgment-holds (restrictions ((x (& ℓ0 mut int))) (ℓ1 ℓ0) (* x) ℓ0 (mutate claim freeze) (restriction ...)) (restriction ...)) '(((x (mutate claim freeze)) ((* x) (mutate claim freeze)))))
(test-equal (judgment-holds (restrictions ((x (& ℓ0 mut int))) (ℓ1 ℓ0) (* x) ℓ1 (mutate claim freeze) (restriction ...)) (restriction ...)) '(((x (mutate claim freeze)) ((* x) (mutate claim freeze)))))
(test-equal (judgment-holds (restrictions ((x (& ℓ0 mut int))) (ℓ1 ℓ0) (* x) ℓ1 (mutate claim freeze) (restriction ...)) (restriction ...)) '(((x (mutate claim freeze)) ((* x) (mutate claim freeze)))))
(test-equal (judgment-holds (restrictions ((x (& ℓ1 mut int))) (ℓ1 ℓ0) (* x) ℓ0 (mutate claim freeze) (restriction ...)) (restriction ...)) '())
(test-equal (judgment-holds (restrictions ((x (& ℓ1 mut int))) (ℓ1 ℓ0) (* x) ℓ0 (mutate claim freeze) (restriction ...)) (restriction ...)) '())
(test-equal (judgment-holds (restrictions ((x (& ℓ1 mut int))) (ℓ1 ℓ0) (* x) ℓ1 (mutate claim freeze) (restriction ...)) (restriction ...)) '(((x (mutate claim freeze)) ((* x) (mutate claim freeze)))))
(test-equal (judgment-holds (restrictions ((x (& ℓ1 mut int))) (ℓ1 ℓ0) (* x) ℓ1 (mutate claim freeze) (restriction ...)) (restriction ...)) '(((x (mutate claim freeze)) ((* x) (mutate claim freeze)))))

;; helper judgment that checks if a restriction allows an action on a path
(define-judgment-form patina-checked
  #:mode (restriction-allows I I I)
  #:contract (restriction-allows restriction action lv)
  [---------------------------------------- "restriction-allows irrelevant"
   (restriction-allows (lv_!_0 _) _ lv_!_0)
   ]
  [(action∉ (action_s ...) action_0)
   -------------------------------------------------------- "restriction-allows relevant"
   (restriction-allows (lv_0 (action_s ...)) action_0 lv_0)
   ]
  )

;; helper judgment that checks if a loan allows an action on a path
(define-judgment-form patina-checked
  #:mode (loan-allows I I I)
  #:contract (loan-allows loan action lv)
  [(restriction-allows restriction action lv) ...
   ------------------------------------------------- "loan-allows"
   (loan-allows (_ _ _ (restriction ...)) action lv)
   ]
  )

;; an action is allowed on a path given the current loans in effect
; for all restrictions on current loans, if the restriction is on a path then it does not forbid the action
(define-judgment-form patina-checked
  #:mode (allowed I I I)
  #:contract (allowed (loan ...) action lv)
  [(loan-allows loan action lv) ...
   -------------------------------- "allowed"
    (allowed (loan ...) action lv)
   ]
  )

(test-equal #t (judgment-holds (allowed ((x ℓ0 imm ((x (mutate claim)))) (x ℓ1 imm ((x (mutate claim))))) freeze x)))
(test-equal #f (judgment-holds (allowed ((x ℓ0 imm ((x (mutate claim)))) (x ℓ1 imm ((x (mutate claim))))) mutate x)))
(test-equal #f (judgment-holds (allowed ((x ℓ0 imm ((x (mutate claim)))) (x ℓ1 imm ((x (mutate claim))))) claim x)))
; we can freeze a mutable borrow if we unfreeze before releasing the mutable borrow
(test-equal #t (judgment-holds (allowed (((* x) ℓ0 mut ((x (mutate claim)) ((* x) (mutate claim))))) freeze (* x))))
; we can't mutably borrow something already mutably borrowed
(test-equal #f (judgment-holds (allowed (((* x) ℓ0 mut ((x (mutate claim freeze)) ((* x) (mutate claim freeze))))) claim (* x))))

;; allowed to move. since restrictions on moving are indicated by the presence of *any* restriction clause, we need a slightly different judgment

; helper judgment to process a restriction
(define-judgment-form patina-checked
  #:mode (restriction-allows-move I I)
  #:contract (restriction-allows-move restriction lv)
  [------------------------------------------- "restriction-allows-move"
   (restriction-allows-move (lv_!_0 _) lv_!_0)
   ]
  )

; helper judgment to process a loan
(define-judgment-form patina-checked
  #:mode (loan-allows-move I I)
  #:contract (loan-allows-move loan lv)
  [(restriction-allows-move restriction lv) ...
   ----------------------------------------------- "loan-allows-move"
   (loan-allows-move (_ _ _ (restriction ...)) lv)
   ]
  )
; the main judgment
(define-judgment-form patina-checked
  #:mode (allowed-to-move I I)
  #:contract (allowed-to-move $ lv)
  [(loan-allows-move loan lv) ...
   ------------------------------- "allowed-to-move"
   (allowed-to-move (loan ...) lv)
   ]
  )

;; typechecking for expressions. tracks initialization of paths
(define-judgment-form patina-checked
  #:mode (rv⊢ I I I I I I I O O O)
  #:contract (rv⊢ Γ Λ L $ Δ Σ rv τ Δ $)
  [--------------------------- "rv⊢ int"
   (rv⊢ Γ Λ L $ Δ Σ z int Δ $)
   ]
  [(lv⊢ Γ lv_1 int) (lv⇑ Γ Δ lv_1)
   (lv⊢ Γ lv_2 int) (lv⇑ Γ Δ lv_2)
   --------------------------------------- "rv⊢ plus"
   (rv⊢ Γ Λ L $ Δ Σ (lv_1 + lv_2) int Δ $)
   ]
  [(lv⊢ Γ lv τ) 
   (lv⇑ Γ Δ_0 lv) 
   (lv⇓⇓ Γ Δ_0 lv Δ_1)
   (allowed-to-move $ lv)
   ------------------------------ "rv⊢ lv"
   (rv⊢ Γ Λ L $ Δ_0 Σ lv τ Δ_1 $)
   ]
  [(lv⊢ Γ lv τ) 
   (lv⇑ Γ Δ_0 lv) 
   (lv⇓⇓ Γ Δ_0 lv Δ_1)
   (allowed-to-move $ lv)
   ---------------------------------------- "rv⊢ new" 
   (rv⊢ Γ Λ L $ Δ_0 Σ (new lv) (~ τ) Δ_1 $)
   ]
  [(lv⊢ Γ lv τ)
   (lv⇑ Γ Δ lv)
   (mutability Γ lv imm)
   (aliasable Γ lv imm) 
   (lifetime Γ Λ L lv ℓ imm)
   (restrictions Γ L lv ℓ (mutate claim) (restriction ...))
   (allowed $_0 freeze lv)
   (where $_1 ,(cons (term (lv ℓ imm (restriction ...))) (term $_0)))
   ------------------------------------------------------------------ "rv⊢ &imm"
   (rv⊢ Γ Λ L $_0 Δ Σ (& ℓ imm lv) (& ℓ imm τ) Δ $_1)
   ]
  [(lv⊢ Γ lv τ)
   (lv⇑ Γ Δ lv)
   (mutability Γ lv mut)
   (aliasable Γ lv mut)
   (lifetime Γ Λ L lv ℓ mut)
   (restrictions Γ L lv ℓ (mutate claim freeze) (restriction ...))
   (allowed $_0 claim lv)
   (where $_1 ,(cons (term (lv ℓ mut (restriction ...))) (term $_0)))
   ------------------------------------------------------------------ "rv⊢ &mut"
   (rv⊢ Γ Λ L $_0 Δ Σ (& ℓ mut lv) (& ℓ mut τ) Δ $_1)
   ]
  )

(test-equal '((int () ())) (judgment-holds (rv⊢ () () () () () () 0 τ Δ $) (τ Δ $)))
(test-equal (judgment-holds (rv⊢ ((x int)) ((x ℓ0)) (ℓ0) () ((x ⊤)) () (x + x) τ Δ $) (τ Δ $)) '((int ((x ⊤)) ())))
(test-equal (judgment-holds (rv⊢ ((x int)) ((x ℓ0)) (ℓ0) () ((x ⊤)) () x τ Δ $) (τ Δ $)) '((int ((x ⊥)) ())))
(test-equal (judgment-holds (rv⊢ ((x int)) ((x ℓ0)) (ℓ0) () ((x ⊤)) () (new x) τ Δ $) (τ Δ $)) '(((~ int) ((x ⊥)) ())))
; can borrow an unaliased variable immutably
(test-equal (judgment-holds (rv⊢ ((x int)) ((x ℓ0)) (ℓ0) () ((x ⊤)) () (& ℓ0 imm x) τ Δ $) (τ Δ $)) '(((& ℓ0 imm int) ((x ⊤)) ((x ℓ0 imm ((x (mutate claim))))))))
; can reborrow immutably if already borrowed immutably (TODO duplicates the loan info...)
(test-equal (judgment-holds (rv⊢ ((x int)) ((x ℓ0)) (ℓ0) ((x ℓ0 imm ((x (mutate claim))))) ((x ⊤)) () (& ℓ0 imm x) τ Δ $) $) '(((x ℓ0 imm ((x (mutate claim)))) (x ℓ0 imm ((x (mutate claim)))))))
; cannot reborrow immutably if already borrowed mutably
(test-equal (judgment-holds (rv⊢ ((x int)) ((x ℓ0)) (ℓ0) ((x ℓ0 mut ((x (mutate claim freeze))))) ((x ⊤)) () (& ℓ0 imm x) τ Δ $) $) '())
; can borrow an unaliased variable mutably
(test-equal (judgment-holds (rv⊢ ((x int)) ((x ℓ0)) (ℓ0) () ((x ⊤)) () (& ℓ0 mut x) τ Δ $) (τ Δ $)) '(((& ℓ0 mut int) ((x ⊤)) ((x ℓ0 mut ((x (mutate claim freeze))))))))
; cannot reborrow mutably if already borrowed immutably
(test-equal (judgment-holds (rv⊢ ((x int)) ((x ℓ0)) (ℓ0) ((x ℓ0 imm ((x (mutate claim))))) ((x ⊤)) () (& ℓ0 mut x) τ Δ $) $) '())
; cannot reborrow mutably if already borrowed mutably
(test-equal (judgment-holds (rv⊢ ((x int)) ((x ℓ0)) (ℓ0) ((x ℓ0 mut ((x (mutate claim freeze))))) ((x ⊤)) () (& ℓ0 mut x) τ Δ $) $) '())

;; typechecking for statements
; TODO maybe remove variables and their subpaths from Δ when they are freed
(define-judgment-form patina-checked
  #:mode (s⊢ I I I I I I I O O)
  #:contract (s⊢ Γ Λ L $ Δ Σ s Δ $)
  [----------------------- "s⊢ skip"
   (s⊢ Γ Λ L $ Δ Σ () Δ $)
   ]
  [(s⊢ Γ Λ L $_0 Δ_0 Σ s_1 Δ_1 $_1) (s⊢ Γ Λ L $_1 Δ_1 Σ (s_2 ...) Δ_2 $_2)
  ------------------------------------------------ "s⊢ seq"
         (s⊢ Γ Λ L $_0 Δ_0 Σ (s_1 s_2 ...) Δ_2 $_2)
   ]
  [(where Γ_1 ,(cons (term (x τ)) (term Γ_0)))
   (where Λ_1 ,(cons (term (x ℓ)) (term Λ_0)))
   (where L_1 ,(cons (term ℓ) (term L_0)))
   (lv⇓⇓ Γ_1 Δ_0 x Δ_1)
   (s⊢ Γ_1 Λ_1 L_1 $_0 Δ_1 Σ (block ℓ (vd_0 ...) s ()) Δ_2 $_1) ; TODO I think we can just throw away $_1.
   (lv↓ Γ_1 Δ_2 x) ; don't need to delete stack variables as long as their contents have been freed
   -------------------------------------------------- "s⊢ block alloc"
   (s⊢ Γ_0 Λ_0 L_0 $_0 Δ_0 Σ (block ℓ ((x : τ) vd_0 ...) s ()) Δ_2 $_0)
   ]
  [          (s⊢ Γ Λ L $_0 Δ_0 Σ s Δ_1 $_1)   ; TODO I think we can throw away $_1
   -------------------------------- "s⊢ block"
   (s⊢ Γ Λ L $_0 Δ_0 Σ (block ℓ () s ()) Δ_1 $_0)
   ]
  [(lv⊢ Γ lv τ)
   (lv↓ Γ Δ_0 lv)
   (allowed $_0 mutate lv)
   (rv⊢ Γ Λ L $_0 Δ_0 Σ rv τ Δ_1 $_1) ; TODO need to propagate restrictions to lv
   (lv⇑⇑ Γ Δ_1 lv Δ_2)
   -------------------------- "s⊢ assign" 
   (s⊢ Γ Λ L $_0 Δ_0 Σ (lv = rv) Δ_2 $_1)
   ]
  [(lv⊢ Γ lv τ)
   (lv↓ Γ Δ_0 lv) ; subpaths are uninitialized
   (Δ= Δ_0 lv ⊤) ; but the path is initialized (prevents double/unnecessary deletes)
   (allowed-to-move $ lv)
   (lv⇓⇓ Γ Δ_0 lv Δ_1)
   ---------------------------- "s⊢ delete"
   (s⊢ Γ Λ L $ Δ_0 Σ (delete lv) Δ_1 $)
   ]
  )

(test-equal (judgment-holds (s⊢ () () () () () () () Δ $) Δ) '(()))
(test-equal (judgment-holds (s⊢ () () () () () () (() ()) Δ $) Δ) '(()))
(test-equal (judgment-holds (s⊢ () () () () () () (block ℓ ((x : int)) () ()) Δ $) Δ) '(((x ⊥))))
(test-equal (judgment-holds (s⊢ ((x int)) ((x ℓ0)) (ℓ) () ((x ⊥)) () (x = 1) Δ $) Δ) '(((x ⊤))))
(test-equal (judgment-holds (s⊢ ((x int) (y int)) ((x ℓ0) (y ℓ0)) (ℓ0) () ((x ⊤) (y ⊥)) () (y = x) Δ $) Δ) '(((x ⊥) (y ⊤))))
(test-equal (judgment-holds (s⊢ ((x int) (y int)) ((x ℓ) (y ℓ)) (ℓ) () ((x ⊤) (y ⊥)) () ((y = x) (x = y)) Δ $) Δ) '(((x ⊤) (y ⊥))))
(test-equal (judgment-holds (s⊢ ((x int) (y int)) ((x ℓ) (y ℓ)) (ℓ) () ((x ⊤) (y ⊥)) () ((y = x) (y = x)) Δ $) Δ) '())
(test-equal (judgment-holds (s⊢ ((x int)) ((x ℓ)) (ℓ) ((x ℓ imm ((x (mutate claim))))) ((x ⊥)) () ((x = 1)) Δ $) $) '())
(test-equal (judgment-holds (s⊢ ((x int)) ((x ℓ)) (ℓ) () ((x ⊤)) () (delete x) Δ $) Δ) '(((x ⊥))))
(test-equal (judgment-holds (s⊢ ((x (~ int))) ((x ℓ)) (ℓ) () ((x ⊤) ((* x) ⊥)) () (delete x) Δ $) Δ) '(((x ⊥) ((* x) ⊥))))
(test-equal (judgment-holds (s⊢ ((x (~ int))) ((x ℓ)) (ℓ) () ((x ⊤) ((* x) ⊤)) () (delete (* x)) Δ $) Δ) '(((x ⊤) ((* x) ⊥))))
(test-equal (judgment-holds (s⊢ ((x (~ int))) ((x ℓ)) (ℓ) () ((x ⊤) ((* x) ⊤)) () (delete x) Δ $) Δ) '())
(test-equal (judgment-holds (s⊢ ((x int)) ((x ℓ)) (ℓ) () ((x ⊤)) () ((delete x) (delete x)) Δ $) Δ) '())
(test-equal (judgment-holds (s⊢ ((x int)) ((x ℓ)) (ℓ) ((x ℓ imm ((x (mutate claim))))) ((x ⊥)) () (delete x) Δ $) $) '())
(test-equal (judgment-holds (s⊢ ((x (~ int))) ((x ℓ)) (ℓ) () ((x ⊤) ((* x) ⊤)) () ((delete (* x)) (delete (* x))) Δ $) Δ) '())
(test-equal (judgment-holds (s⊢ ((x (~ int)) (y int)) ((x ℓ) (y ℓ)) (ℓ) () ((x ⊤) ((* x) ⊤) (y ⊥)) () ((y = (* x)) (delete (* x))) Δ $) Δ) '())

;;;; EVALUATION
(define-extended-language patina-machine patina-checked
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
  [-------------- "sizeof int"
   (sizeof int 1)
   ]
  [---------------- "sizeof ~τ"
   (sizeof (~ τ) 1)
   ]
  [--------------------- "sizeof &'ℓ mq τ"
   (sizeof (& ℓ mq τ) 1)
   ]
  )

(test-equal (term (1)) (judgment-holds (sizeof int n) n))
(redex-check patina-machine τ (equal? (term (1)) (judgment-holds (sizeof (~ τ) n) n)))
(redex-check patina-machine (ℓ mq τ) (equal? (term (1)) (judgment-holds (sizeof (& ℓ mq τ) n) n)))

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
  [-------------------------------------------- "μ="
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
   ----------------------------------------- "μ->"
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
  [-------------------------------------------- "V="
   (V= ((x_s _) ... (x_0 α) (x_e _) ...) x_0 α)
   ]
  )

(test-equal '((0 0)) (judgment-holds (V= ((x (0 0))) x α) α))

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
(test-equal '((0 0)) (judgment-holds
                     (lv-> ((x (& ℓ1 imm (& ℓ2 mut int)))) 
                           ((x (2 0)))
                           (((0 0) ⊥) ((1 0) (0 0)) ((2 0) (1 0)))
                           (* (* x))
                           α)
                     α))

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
  [(lv-> Γ V μ lv α_1) (μ<- μ α α_1 μ_1)
   ------------------------------------- "rv-> borrow"
   (rv-> Γ V μ α (& ℓ mq lv) μ_1)
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
(test-equal (judgment-holds (rv-> ((x int)) ((x (0 0))) (((0 0) 1) ((1 0) ⊥)) (1 0) (& ℓ imm x) μ) μ)
	    '((((0 0) 1) ((1 0) (0 0)))))
(test-equal (judgment-holds (rv-> ((x int)) ((x (0 0))) (((0 0) 1) ((1 0) ⊥)) (1 0) (& ℓ mut x) μ) μ)
	    '((((0 0) 1) ((1 0) (0 0)))))

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
   (s-> Γ V μ (block ℓ () () ()) Γ V μ ())
   ]
  [                  (s-> Γ_0 V_0 μ_0 s_0 Γ_1 V_1 μ_1 s_1)
   ----------------------------------------------------------------------------- "s-> block step"
   (s-> Γ_0 V_0 μ_0 (block ℓ () s_0 (vd ...)) Γ_1 V_1 μ_1 (block ℓ () s_1 (vd ...)))
   ]
  [  (μ+ μ_0 τ α μ_1) (where Γ_1 ,(cons (term (x τ)) (term Γ_0))) (where V_1 ,(cons (term (x α)) (term V_0)))
   ------------------------------------------------------------------------------------------------------------- "s-> block alloc"
   (s-> Γ_0 V_0 μ_0 (block ℓ ((x : τ) vd_0 ...) s (vd_1 ...)) Γ_1 V_1 μ_1 (block ℓ (vd_0 ...) s ((x : τ) vd_1 ...)))
   ]
  [(where ((x_s τ_s) ... (x τ) (x_e τ_e) ...) Γ_0)
   (where ((x_s α_s) ... (x α) (x_e α_e) ...) V_0)
   (μ- μ_0 τ α μ_1)
   (where Γ_1 ((x_s τ_s) ... (x_e τ_e) ...))
   (where V_1 ((x_s α_s) ... (x_e α_e) ...))
   ----------------------------------------------------------------------------------- "s-> block free"
   (s-> Γ_0 V_0 μ_0 (block ℓ () () ((x : τ) vd ...)) Γ_1 V_1 μ_1 (block ℓ () () (vd ...)))
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
  ; pretty sure you can't delete through a borrowed pointer because it doesn't have ownership
  )

(test-equal '((() () () (() ()))) (judgment-holds (s-> () () () (() () ()) Γ V μ s) (Γ V μ s)))
(test-equal '((() () () ())) (judgment-holds (s-> () () () (block ℓ () () ()) Γ V μ s) (Γ V μ s)))
(test-equal (judgment-holds (s-> () () () (block ℓ ((x : int)) () ()) Γ V μ s) (Γ V μ s))
	    '((((x int)) ((x (0 0))) (((0 0) ⊥)) (block ℓ () () ((x : int))))))
(test-equal (judgment-holds (s-> ((x int)) ((x (0 0))) (((0 0) ⊥)) (block ℓ () () ((x : int))) Γ V μ s) (Γ V μ s))
	    '((() () () (block ℓ () () ()))))
(test-equal (judgment-holds (s-> ((x int) (y int)) ((x (0 0)) (y (1 0))) (((0 0) 1) ((1 0) ⊥)) (y = x) Γ V μ s) (Γ V μ s))
	    '((((x int) (y int)) ((x (0 0)) (y (1 0))) (((0 0) ⊥) ((1 0) 1)) ())))
(test-equal (judgment-holds (s-> ((x int)) ((x (0 0))) (((0 0) 1)) (delete x) Γ V μ s) (Γ V μ s))
	    '((((x int)) ((x (0 0))) (((0 0) 1)) ())))
(test-equal (judgment-holds (s-> ((x (~ int))) ((x (0 0))) (((0 0) (1 0)) ((1 0) 1)) (delete (* x)) Γ V μ s) (Γ V μ s))
	    '((((x (~ int))) ((x (0 0))) (((0 0) (1 0))) ())))
(test-equal (judgment-holds (s-> ((x (& ℓ imm int))) ((x (0 0))) (((0 0) (1 0)) ((1 0) 1))
				 (delete (* x)) Γ V μ s) (Γ V μ s))
	    '())

(define patina-step
  (reduction-relation patina-machine
    [--> (Γ_0 V_0 μ_0 s_0)
         (Γ_1 V_1 μ_1 s_1)
         (judgment-holds (s-> Γ_0 V_0 μ_0 s_0 Γ_1 V_1 μ_1 s_1))]))

(test-equal #t
(judgment-holds
  (s⊢ () () () () () ()
    (block ℓ ((x : int) (y : (~ int)) (z : int)) 
           ((x = 1) 
            (y = (new x))
            (z = (* y))
            ((* y) = z) 
            (delete (* y))
            ) 
           ())
    Δ $))
)

(test-equal '((() () () ()))
(apply-reduction-relation* patina-step
  (term  (() () ()
    (block ℓ ((x : int) (y : (~ int)) (z : int)) 
           ((x = 1) 
            (y = (new x))
            (z = (* y))
            ((* y) = z) 
            (delete (* y))
            ) 
           ()))))
)

; TODO fails because we current require all subpaths to be uninitialized before freeing stack
; since (*y) == x is still initialized, this check fails
; we need to change the check to look at the type:
;   - if `int`, then we can just free it
;   - if `~ τ`, then (* lv) must be ⊥
;   - if `& ℓ mut τ`, then we can just free it
;   - if `struct { f, g }`, then recurse onto `lv.f` and `lv.g`
;(test-equal #t
(judgment-holds
  (s⊢ ((x int) (y (& ℓ imm int)))
      ((x ℓ) (y ℓ))
      (ℓ)
      ()
      ((x ⊥) (y ⊥) ((* y) ⊥))
      ()
      ((x = 1)
       (y = (& ℓ imm x))
       ((* y) = 2)
       )
      Δ
      $)
  Δ)
(judgment-holds
  (s⊢ ((x int) (y (& ℓ imm int)))
      ((x ℓ) (y ℓ))
      (ℓ)
      ()
      ((x ⊥) (y ⊥) ((* y) ⊥))
      ()
      ((x = 1)
       (y = (& ℓ imm x))
       ((* y) = 2)
       )
      Δ
      $)
  $)
(build-derivations
  (s⊢ ((x int) (y (& ℓ imm int)))
      ((x ℓ) (y ℓ))
      (ℓ)
      ((x ℓ imm ((x (mutate claim)))))
      ((x ⊤) (y ⊤) ((* y) ⊤))
      ()
      ((* y) = 2)
      Δ
      $))
(judgment-holds
  (s⊢ () () () () () ()
      (block ℓ ((x : int) (y : (& ℓ imm int)))
             ((x = 1)
              (y = (& ℓ imm x))
              ((* y) = 2)
             )
             ())
      Δ $)
  Δ)
(judgment-holds
  (s⊢ () () () () () ()
      (block ℓ ((x : int) (y : (& ℓ imm int)))
             ((x = 1)
              (y = (& ℓ imm x))
              ((* y) = 2)
             )
             ())
      Δ $)
  $)
;)

(test-results)
