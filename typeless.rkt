#lang racket
(require redex)

(define-language typeless
  ;; constants
  (ℕ natural)
  (ℤ number)
  ;; variable names
  (var variable-not-otherwise-mentioned)
  ;; addresses
  (size ℕ)
  (offset size) ;; offset
  (base ℕ) ;; base address
  (α (base offset)) ;; address = base + offset
  ;; values can be
  (val ℕ ;; integer constants
       α ;; addresses
       )
  ;; lhs values (things that can be assigned to)
  (lv var ;; we can set variables
      (lv + size) ;; pointer arithmetic
      (* lv) ;; dereference
      )
  ;; rhs values (things that can be put in memory)
  (rv var ;; we can use variables
      val ;; we can use values
      (& lv) ;; we can make references to assignable things
      (new size) ;; we can allocate memory
      (rv + rv) ;; we can perform addition (on numbers)
      )
  ;; statements (things that only have side effects)
  (stmt (lv <- rv) ;; assign rv to lv)
        (let var = rv in (stmt ...)) ;; bind a variable
        (delete α) ;; deallocate memory
        (switch lv (ℤ => (stmt ...)) ...) ;; control flow
        (while rv (stmt ...)) ;; loop
        )
  )

(define-extended-language typeless-heap typeless
  (hv α ℤ ⊥) ;; things that go in a heap
  (slot (ℕ hv)) ;; a storage slot
  (heap (slot ...)) ;; a heap is a bunch of storage slots
  (binding (var α)) ;; a variable binding
  (ctx (binding ...)) ;; a context is a bunch of bindings
  )

;;;; lifted operations

;; list construction. Redex throws a fit if I use cons, so I just used con instead.
(define-metafunction typeless
    con : any (any ...) -> (any ...)

    [(con any_0 (any_1 ...)) ,(cons (term any_0) (term (any_1 ...)))])

(test-equal (term (con 0 (1 2))) (term (0 1 2)))

;;;; address operations

;; offset an address
(define-metafunction typeless
    α+ : α size -> α

    [(α+ (base offset) size) (base ,(+ (term offset) (term size)))])

(test-equal (term (α+ (0 1) 2)) (term (0 3)))

;; convert an address to a nat
(define-metafunction typeless
   α→ℕ : α -> ℕ

   [(α→ℕ (base offset)) ,(+ (term base) (term offset))])

(test-equal (term (α→ℕ (1 2))) (term 3))

;;;; heap operations

;; find a fresh physical address (1) higher than any currently allocated address
(define-metafunction typeless-heap
    fresh-highest : heap -> ℕ

    [(fresh-highest heap) ,(+ 1 (apply max -1 (map car (term heap))))])

(test-equal (term (fresh-highest ((0 1) (2 0))))
            (term 3))

;; given a base address, generate a specified amount of uninitialized addresses
(define-metafunction typeless-heap
    fresh-memory : ℕ size -> heap

    [(fresh-memory ℕ size) ,(map (lambda (o) `(,(+ o (term ℕ)) ,(term ⊥))) (range (term size)))])

(test-equal (term (fresh-memory 2 2))
            (term ((2 ⊥) (3 ⊥))))

;; allocate memory initialized to ⊥
(define-metafunction typeless-heap
    allocate : heap size -> (heap α)

    [(allocate heap size) (,(append (term heap) (term heap_new)) (ℕ_base 0))
                          (where ℕ_base (fresh-highest heap))
                          (where heap_new (fresh-memory ℕ_base size))
                          ])

(test-equal (term (allocate () 2))
            (term (((0 ⊥) (1 ⊥)) (0 0))))
(test-equal (term (allocate ((0 1) (4 0)) 2))
            (term (((0 1) (4 0) (5 ⊥) (6 ⊥)) (5 0))))

;; delete a slot from the heap
(define-metafunction typeless-heap
    delete-slot : heap ℕ  -> heap

    [(delete-slot ((ℕ_0 hv) slot ...) ℕ_0) (slot ...)]
    [(delete-slot ((ℕ_0 hv) slot ...) ℕ_1) (con (ℕ_0 hv) (delete-slot (slot ...) ℕ_1))])

(test-equal (term (delete-slot ((0 0)) 0)) (term ()))
(test-equal (term (delete-slot ((0 0) (1 0)) 0)) (term ((1 0))))
(test-equal (term (delete-slot ((0 0) (1 0) (2 0)) 2)) (term ((0 0) (1 0))))

;; set a slot in the heap to a value
(define-metafunction typeless-heap
    heap-set : heap ℕ hv -> heap

    [(heap-set ((ℕ_0 hv_0) slot ...) ℕ_0 hv_1) ((ℕ_0 hv_1) slot ...)]
    [(heap-set ((ℕ_0 hv_0) slot ...) ℕ_1 hv_1) (con (ℕ_0 hv_0) (heap-set (slot ...) ℕ_1 hv_1))])

(test-equal (term (heap-set ((0 ⊥)) 0 1)) (term ((0 1))))
(test-equal (term (heap-set ((0 ⊥) (1 ⊥)) 1 2)) (term ((0 ⊥) (1 2))))


;; lookup a physical address in the heap to get the value there
(define-metafunction typeless-heap
    heap-lookup : heap ℕ -> hv

    [(heap-lookup ((ℕ_0 hv) slot ...) ℕ_0) hv]
    [(heap-lookup ((ℕ_0 hv) slot ...) ℕ_1) (heap-lookup (slot ...) ℕ_1)])

(test-equal (term (heap-lookup ((2 ⊥)) 2)) (term ⊥))
(test-equal (term (heap-lookup ((0 0) (1 1)) 1)) (term 1))

;;;; context operations

;; lookup a variable in the context to get the address it refers to
(define-metafunction typeless-heap
    ctx-lookup : ctx var -> α

    [(ctx-lookup ((var_0 α) binding ...) var_0) α]
    [(ctx-lookup ((var_0 α) binding ...) var_1) (ctx-lookup (binding ...) var_1)])

(test-equal (term (ctx-lookup ((x (0 1))) x)) (term (0 1)))
(test-equal (term (ctx-lookup ((x (0 1)) (y (1 2))) y)) (term (1 2)))

;;;; evalutation

;; evaluate a lv
(define-metafunction typeless-heap
    lv-eval : heap ctx lv -> α

    [(lv-eval heap ctx var)         (ctx-lookup ctx var)] ;; lookup var
    [(lv-eval heap ctx (lv + size)) (α+ (lv-eval heap ctx lv) size)] ;; offset
    [(lv-eval heap ctx (* lv))      (heap-lookup heap (α→ℕ (lv-eval heap ctx lv)))]) ;; deref

(test-equal (term (lv-eval ((3 (10 11))) ; heap
                           ((x (0 1)))   ; context
                           (* (x + 2)))) ; lv
            (term (10 11)))

;; evaluate a rv, which could modify the heap
(define-metafunction typeless-heap
    rv-eval : heap ctx rv -> (heap val)

    ;; values are already done
    [(rv-eval heap ctx val)             (heap val)] 
    ;; lookup the address the variable points to and deref to get the value there
    [(rv-eval heap ctx var)             (heap (heap-lookup heap (α→ℕ (ctx-lookup ctx var))))]
    ;; just the address the lv evaluates to?
    [(rv-eval heap ctx (& lv))          (heap (lv-eval heap ctx lv))]
    ;; eval both sides. if they're ℕ then add them
    [(rv-eval heap_0 ctx (rv_0 + rv_1)) (heap_2 ,(+ (term ℕ_0) (term ℕ_1)))
                                        (where (heap_1 ℕ_0) (rv-eval heap_0 ctx rv_0))
                                        (where (heap_2 ℕ_1) (rv-eval heap_1 ctx rv_1))]
    ;; allocate new space on the heap of the given size and return a pointer to the start of it
    [(rv-eval heap ctx (new size))      (allocate heap size)]
    )
    

(define typeless-heap-step
  (reduction-relation typeless-heap

    ;; assignment - do we evaluate the lv first or the rv first?
    [--> (heap_0 ctx ((lv <- rv) stmt ...))
         (heap_2 ctx (stmt ...))
         (where (heap_1 val) (rv-eval heap_0 ctx rv))
         (where heap_2 (heap-set heap_1 (α→ℕ (lv-eval heap_0 ctx lv)) val))]
    ;; bind a variable (let stmt)
    [--> (heap ctx ((let var = rv in (stmt_0 ...)) stmt_1 ...))
      ]
    ))


(test-results)
