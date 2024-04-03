#lang racket

;; Group work done by Junzhang Luo, Elyn Huang

(define tmps-ht (make-hash))
;;(define var-ht (make-hash))
(define vargs-ht (make-hash))
(define fun-name-ht (make-hash))
(define program empty)
(define cur-fun 'x)

(define s-top 0)
(define s-cur 0)
(define s-count 0)

(define labels 0)

(define aexpop-ht
  (hash
   '+ 'add
   '- 'sub
   '* 'mul
   'div 'div
   'mod 'mod))

(define bexpop-ht
  (hash
   '= 'equal
   '> 'gt
   '< 'lt
   '>= 'ge
   '<= 'le
   'not 'not
   'and 'land
   'or 'lor
   'not 'lnot))

(define (generate)
  (set! s-count (+ s-count 1))
  (define curtop (+ s-cur 1))
  (cond [(> curtop s-top)
         (set! s-top (+ s-top 1)) (set! s-cur s-top)
         (define ntmp (string->symbol (string-append "TMP" (number->string s-cur))))
         (hash-set! tmps-ht ntmp s-cur) ntmp]
        [else (set! s-cur curtop) (string->symbol (string-append "TMP" (number->string s-cur)))]))

(define (create-label)
  (set! labels (+ labels 1))
  (string->symbol (string-append "LABEL" (number->string labels))))

;; add "_" in front of SIMPL variables
(define (mod-sym sym)
  (string->symbol (string-append "_" (symbol->string sym))))

;; add function name in front
;; CHECKED TODO: write a mod-arg 
;; CHECKED TODO: mod-var
(define (add-fun-name fn sym)
  (string->symbol (string-append (symbol->string fn)
                                 (string-append "_" (symbol->string sym)))))

(define (add-fun-end fn)
  (string->symbol (string-append (symbol->string fn) "_end")))

;(define (print-ht ht)
;  (for ([(key val) (in-hash ht)])
;    (display key)
;    (display ": ")
;    (displayln val)))

;; Check aexp
(define (aexp? exp)
  (cond [(list? exp) (or (hash-has-key? aexpop-ht (first exp))
                         (hash-has-key? fun-name-ht (first exp)))]
        [(symbol? exp) (not (or (symbol=? exp 'true) (symbol=? exp 'false)))]
        [else (number? exp)]))

;; Check bexp
(define (bexp? exp)
  (cond [(list? exp) (hash-has-key? bexpop-ht (first exp))]
        [else (or (symbol=? exp 'true) (symbol=? exp 'false))]))

(define (tf-convert sym)
  (if (symbol=? sym 'true) #t #f))

(define (eval-loop lostmt)
  (cond [(empty? lostmt) s-count]
        [else (define ncount (interp #t (first lostmt)))
              (eval-loop (rest lostmt))]))

(define (eval-lobexp lobexp lontmps)
  (cond [(empty? lobexp) (list lontmps s-count)]
        [else 
         (define res (eval-bexp (first lobexp)))
              ;; (define ncount (cadr res))
              (define ntmp (car res))
              ;; (set! s-count ncount)
              (eval-lobexp (rest lobexp) (cons ntmp lontmps))]))

;; eval-aexp: tmpcount aexp
;; - update program and tmpcount
;; - return (list type tmpcount placeholder)
(define (eval-aexp fun aexp)
  (cond [(number? aexp)
         (list aexp s-count aexp)]
        [(symbol? aexp)
         (cond [(hash-has-key? tmps-ht aexp)
                (define res (hash-ref tmps-ht aexp))
                (define nid (car res))
                (list aexp s-count nid)]
               [else
                (define res (hash-ref vargs-ht aexp))
                (define nid (list (car res) 'FP))
                (list aexp s-count nid)])]
        ;; Can we assume the function is pre-defined
        [(hash-has-key? fun-name-ht (first aexp))
        ; TODO: need to have the function in hash first
        ;;TODO: check there are the right number of parameters being passed in to the function
        (define cur_fun (hash-ref fun-name-ht (first aexp)))
        (define arg-num (cadr cur_fun))
        (define nfun-name (car cur_fun))
        (define params (rest aexp))
        (define params-len (length params))
        
        (cond [(= arg-num params-len)
               (define arg-lists empty)
               (define tmp-count 0) ;; Asume SP points to the end of function
               (for [(param params)]
                 ;; Create tmp variables at the end of current stack, relative to SP
                 ;; For passing arguments to the called function
                 ;; TODO: make sure parameters are in right order
                 (define param-res (eval-aexp #t param))
                 (set! arg-lists (cons (third param-res) arg-lists)))
               
               (for [(param arg-lists)]
                 ;(define nparam (add-fun-name nfun-name param))
                 (set! program (cons (list 'move (list tmp-count 'SP) param) program))
                 (set! tmp-count (+ tmp-count 1)))
               (set! program (cons (list 'add 'SP 'SP params-len) program))
               ;; TODO: not sure if moving FP and SP is needed
               
               ;(set! program (cons (list 'move 'FP 'SP) program))
               (set! program (cons (list 'jsr 'RETURN-ADDR nfun-name) program))
               (set! program (cons (list 'sub 'SP 'SP params-len) program))
               (define ntmp (generate))
               
               ;(set! s-count (+ s-count 1))
               (set! program (cons (list 'move ntmp 'RETURN-VAL) program))
               (list 'RETURN-VAL s-count ntmp)]
        ;;(set! SP (sub SP tmp-count))
              [else (error "incorrect number of arguments")])]
        [(hash-has-key? aexpop-ht (first aexp))
         (match aexp
           [`(,op ,aexp1 ,aexp2)
            (define nop (hash-ref aexpop-ht op))
            (define res1 (eval-aexp #f aexp1))
            (define var1 (car res1))
            ;(set! s-count (+ (cadr res1) s-count))
            (define res2 (eval-aexp #f aexp2))
            (define var2 (car res2))
            ;;(set! tmpcount (+ (cadr res2) tmpcount))
            (cond [fun
                   (define ntmp (generate))
                   ;; (set! s-count (+ s-count 1))
                   (define res (list nop ntmp (caddr res1) (caddr res2)))
                   (set! program (cons res program))
                   (list ntmp s-count ntmp)]
;                  [(and (number? var1) (hash-has-key? vargs-ht var2))
;                   (define res (list nop (caddr res2) (caddr res1) (caddr res2)))
;                   (set! program (cons res program))
;                   (list #\0 s-count (caddr res2))]
;                  [(and (number? var2) (hash-has-key? vargs-ht var1))
;                   (define res (list nop (caddr res1) (caddr res1) (caddr res2)))
;                   (set! program (cons res program))
;                   (list #\0 s-count (caddr res1))]
                  [else
                   (define ntmp (generate))
                   ;; (set! tmpcount (+ tmpcount 1))
                   (define res (list nop ntmp (caddr res1) (caddr res2)))
                   (set! program (cons res program))
                   (list ntmp s-count ntmp)])])]
        [else (error "undefined function")]))

;; eval-bexp: tmpcount bexp
;; - update program and tmpcount
;; - return (list var/tmp tmpcount)
(define (eval-bexp bexp)
  (cond
    [(boolean? bexp) (list bexp s-count)]
    [(symbol? bexp)
         (define res (tf-convert bexp))
         (list res s-count)]
        [else
         (match bexp
           [`(and ,lobexp ...)
            (define ntmp (generate))
            ;;(set! tmpcount (+ tmpcount 1))
            (define res (eval-lobexp lobexp empty))
            ;;(define ncount (cadr res))
            ;;(set! tmpcount ncount)
            ;;(displayln res)
            (define lontmp (reverse (car res)))
            (define nline (cons 'land (cons ntmp lontmp)))
            (set! program (cons nline program))
            (list ntmp s-count)]
           [`(or ,lobexp ...)
            (define ntmp (generate))
            ;;(set! tmpcount (+ tmpcount 1))
            (define res (eval-lobexp lobexp empty))
            ;(define ncount (cadr res))
            ;(set! tmpcount ncount)
            (define lontmp (reverse (car res)))
            (define nline (cons 'lor (cons ntmp lontmp)))
            (set! program (cons nline program))
            (list ntmp s-count)]
           [`(,op ,aexp1 ,aexp2)
            (define nop (hash-ref bexpop-ht op))
            (define ntmp (generate))
            ;;(set! tmpcount (+ tmpcount 1))
            (define res1 (eval-aexp #f aexp1))
            (define var1 (caddr res1))
            ;(set! tmpcount (+ (cadr res1) tmpcount))
            (define res2 (eval-aexp #f aexp2))
            (define var2 (caddr res2))
            ;(set! tmpcount (+ (cadr res2) tmpcount))
            (define res (list nop ntmp var1 var2))
            (set! program (cons res program))
            (list ntmp s-count)]
           [`(,op ,aexp)
            (define nop (hash-ref bexpop-ht op))
            (define ntmp (generate))
            ;;(set! tmpcount (+ tmpcount 1))
            (define res (eval-bexp aexp))
            (define var (car res))
            ;;(set! tmpcount (+ (cadr res) tmpcount))
            (define nline (list nop ntmp var))
            (set! program (cons nline program))
            (list ntmp s-count)])]))
  
;; interp a stmt
(define (interp loop stmt)
  (match stmt
    [`(return ,x)
    ;;TODO: after x is evaluated, x needs to be stored in the global RETURN-VAL
    (define res (eval-aexp #f x)) ;; TODO: assume return is the last statement to call
    ;; (list var tmpcount var)
    ;;(set! tmpcount (+ (cadr res) tmpcount))
    ;; the previous line will return the name to move FP to
    (set! program (cons (list 'move 'RETURN-VAL (caddr res)) program))
    (set! program (cons (list 'jump cur-fun) program))]
    ;(if loop s-count (set! s-cur (- s-cur tmpcount)))]
    [`(print ,s)
     (cond [(string? s)
            (define nline (list 'print-string s))
            (set! program (cons nline program))]
            ;(if loop tmpcount (set! s-cur (- s-cur tmpcount)))]
           [(number? s)
            (define nline (list 'print-val s))
            (set! program (cons nline program))]
            ;(if loop tmpcount (set! s-cur (- s-cur tmpcount)))]
           [else
            (define res (eval-aexp #f s))
            ;(set! tmpcount (+ (cadr res) tmpcount))
            (define nvar (caddr res))
            (cond [(number? nvar)
                   (define ns (mod-sym s))
                   (define nline (list 'print-val ns))
                   (set! program (cons nline program))]
                   ;(if loop tmpcount (set! s-cur (- s-cur tmpcount)))]
                  [else (define nline (list 'print-val nvar))
                        (set! program (cons nline program))
                        ;(if loop tmpcount (set! s-cur (- s-cur tmpcount)))
                        ])])]
    [`(set ,id ,exp)
     (cond [(aexp? exp)
            (define mid 'x)
            (cond [(hash-has-key? tmps-ht id) (set! mid id)]
                  [else (define res (hash-ref vargs-ht id))
                        (set! mid (list (car res) 'FP))])
            
            (define res (eval-aexp #f exp))

            ;(set! tmpcount (+ (cadr res) tmpcount))
            (define var (caddr res))

            (define nline (list 'move mid var))
            (set! program (cons nline program))]

;            (cond [(char? var) s-count]
;
;                   ;(if loop tmpcount (set! s-cur (- s-cur tmpcount)))]
;                  [else (define nline (list 'move mid var))
;                        (set! program (cons nline program))])]
                        ;(if loop tmpcount (set! s-cur (- s-cur tmpcount)))])]
           [(bexp? exp)
            (define mid 'x)
            (cond [(hash-has-key? tmps-ht id) (set! mid id)]
                  [else (define res (hash-ref vargs-ht id))
                        (set! mid (list (car res) 'FP))])
            (define res (eval-bexp exp))
            ;(set! tmpcount (+ (cadr res) tmpcount))
            (define var (car res))
            (define nline (list 'move mid var))
            (set! program (cons nline program))
            ;(if loop tmpcount (set! s-cur (- s-cur tmpcount)))
            ])]
    [`(seq ,lostmt ...)
     (eval-loop lostmt)]
     ;(if loop tmpcount (set! s-cur (- s-cur tmpcount)))]
    [`(iif ,bexp ,stmt1 ,stmt2)
     (define stmt1-start (create-label))
     (define stmt1-end (create-label))
     (define res (eval-bexp bexp))
     ;(set! tmpcount (+ (cadr res) tmpcount))
     (define var (car res))
     (define nline (list 'branch var stmt1-start))
     (set! program (cons nline program))
     (interp loop stmt2)
     (set! nline (list 'jump stmt1-end))
     (set! program (cons nline program))
     (set! nline (list 'label stmt1-start))
     (set! program (cons nline program))
     (interp loop stmt1)
     (set! nline (list 'label stmt1-end))
     (set! program (cons nline program))]
     ;(if loop tmpcount (set! s-cur (- s-cur tmpcount)))]
    [`(while ,bexp ,lostmt ...)
     (define loop-top (create-label))
     (define loop-body (create-label))
     (define loop-end (create-label))
     (define nline (list 'label loop-top))
     (set! program (cons nline program))
     (define res (eval-bexp bexp))
     ;(set! tmpcount (+ (cadr res) tmpcount))
     (define var (car res))
     (set! nline (list 'branch var loop-body))
     (set! program (cons nline program))
     (set! nline (list 'jump loop-end))
     (set! program (cons nline program))
     (set! nline (list 'label loop-body))
     (set! program (cons nline program))
     (eval-loop lostmt)
     (set! nline (list 'jump loop-top))
     (set! program (cons nline program))
     (set! nline (list 'label loop-end))
     (set! program (cons nline program))]
     ;(if loop tmpcount (set! s-cur (- s-cur tmpcount)))]
    [`(skip)
     ;(if loop tmpcount (set! s-cur (- s-cur tmpcount)))
     s-count]))

(define (insert-data)
  (for ([(key value) (in-hash tmps-ht)])
    (define res (list 'data key value))
    (set! program (cons res program))))


;; what about empty function
(define (eval-stmts stmts)
  (cond [(empty? stmts) (error "no statements in function")]
        [(empty? (rest stmts))
         (cond [(symbol=? (car (car stmts)) 'return)
                (interp #f (car stmts))]
               [else (error "last statement is not return")])]
        [else (interp #f (car stmts)) (eval-stmts (cdr stmts))]))

(define (compile-function fun)
  (set! vargs-ht (make-hash))
  ;; (set! tmps-ht (make-hash))
  (define fun-name (first (second fun)))
  (define nfun-name (mod-sym fun-name))
  (set! cur-fun (add-fun-end nfun-name))
  (set! program (cons (list 'label nfun-name) program))
  ;; Args
  (define args (rest (second fun)))
  (define args-len (length args))
  (define arg-counter 0)
  (when (and (symbol=? fun-name 'main) (not (= args-len 0))) (error "main argument error"))
  ;; (hash-set! fun-name-ht fun-name (list nfun-name args-len))
  (for ([arg args])
    (cond [(hash-has-key? vargs-ht arg) (error "duplicate")]
          [else
           (set! arg-counter (- arg-counter 1))
           (define narg (add-fun-name nfun-name arg))
           (hash-set! vargs-ht arg (list narg arg-counter))
           (define arg-line (list 'const narg arg-counter))
           (set! program (cons arg-line program))]))
  ;; FP
  (define nFP (add-fun-name nfun-name 'FP))
  (set! program (cons (list 'const nFP 0) program))
  ;; RTA
  (define nRTA (add-fun-name nfun-name 'RETURN-ADDR))
  (set! program (cons (list 'const nRTA 1) program))
  ;; Local vars
  (define vars (second (third fun)))
  (define vars-len (length vars))
  (define var-count 1)
  (for ([var vars])
    (define var-name (car var))
    (cond [(hash-has-key? vargs-ht var-name) (error "duplicate")]
          [else
           (define nvar-name (add-fun-name nfun-name var-name))
           (define value (cadr var))
           (hash-set! vargs-ht var-name (list nvar-name value)) ;; (list new_name init_val)
           (set! var-count (+ var-count 1))
           (set! program (cons (list 'const nvar-name var-count) program))]))
  ;; Stack frame size
  (define size (+ vars-len 2))
  (define size-name (add-fun-name nfun-name 'SIZE))
  (set! program (cons (list 'const size-name size) program))
  ;; Prologue
  (set! program (cons (list 'move (list nFP 'SP) 'FP) program))
  (set! program (cons (list 'move (list nRTA 'SP) 'RETURN-ADDR) program))
  ;; Prologue loc_vars
  (for ([var vars])
    (define var-name (car var))
    (define res (hash-ref vargs-ht var-name))
    (define nvar-name (car res))
    (define val (cadr res))
    (set! program (cons (list 'move (list nvar-name 'SP) val) program)))
  (set! program (cons (list 'move 'FP 'SP) program))
  (set! program (cons (list 'add 'SP 'SP size-name) program))
  ;; Body
  (define body (cddr (third fun)))
  (eval-stmts body)
  (set! s-cur (- s-cur s-count))
  (set! s-count 0)
  ;; Epilogue
  (set! program (cons (list 'label cur-fun) program))
  (set! program (cons (list 'sub 'SP 'SP size-name) program))
  (set! program (cons (list 'move 'FP (list nFP 'SP)) program))
  (set! program (cons (list 'move 'RETURN-ADDR (list nRTA 'SP)) program))
  (if (symbol=? fun-name 'main)
      (set! program (cons (list 'halt) program))
  (set! program (cons (list 'jump 'RETURN-ADDR) program))))
         
(define (compile-program lofun)
  (cond [(empty? lofun)
         (insert-data) ;; insert all tmp variables initialized
         (set! program (cons '(data RETURN-VAL 0) program))
         (set! program (cons '(data RETURN-ADDR 0) program))
         (set! program (cons '(data FP 0) program))
         (set! program (cons '(data SP END) program))
         (set! program (cons '(label END) program))
         (cond [(hash-has-key? fun-name-ht 'main) ;; check for main existence
                (set! program (reverse program))
                (set! program (cons '(jump _main) program))
                program]
               [else
                (set! program (reverse program))
                (set! program (cons '(halt) program))
                program])]
        [else 
         (compile-function (first lofun)) (compile-program (rest lofun))]))

(define (compile-simpl lofun)
  (set! program empty)
  (for ([fun lofun])
    (define f-name (car (cadr fun)))
    (define arg-len (length (cdr (cadr fun))))
    (cond [(hash-has-key? fun-name-ht f-name) (error "duplicate")]
          [else (define nf-name (mod-sym f-name))
                (hash-set! fun-name-ht f-name (list nf-name arg-len))]))
  (compile-program lofun))
    
