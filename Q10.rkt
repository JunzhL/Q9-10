#lang racket

;; Group work done by Junzhang Luo, Elyn Huang

(define tmps-ht (make-hash))
;;(define var-ht (make-hash))
(define vargs-ht (make-hash))
(define fun-name-ht (make-hash))
(define program empty)

(define s-top 0)
(define s-cur 0)

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

(define (eval-loop tmpcount lostmt)
  (cond [(empty? lostmt) tmpcount]
        [else (define ncount (interp #t (first lostmt) 0))
              (eval-loop ncount (rest lostmt))]))

(define (eval-lobexp tmpcount lobexp lontmps)
  (cond [(empty? lobexp) (list lontmps tmpcount)]
        [else 
         (define res (eval-bexp tmpcount (first lobexp)))
              (define ncount (cadr res))
              (define ntmp (car res))
              (set! tmpcount ncount)
              (eval-lobexp tmpcount (rest lobexp) (cons ntmp lontmps))]))

;; eval-aexp: tmpcount aexp
;; - update program and tmpcount
;; - return (list type tmpcount placeholder)
(define (eval-aexp fun tmpcount aexp)
  (cond [(number? aexp)
         (list aexp tmpcount aexp)]
        [(symbol? aexp)
         (cond [(hash-has-key? tmps-ht aexp)
                (define res (hash-ref tmps-ht aexp))
                (define nid (car res))
                (list aexp tmpcount nid)]
               [else
                (define res (hash-ref vargs-ht aexp))
                (define nid (list (car res) 'FP))
                (list aexp tmpcount nid)])]
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
                 (define param-res (eval-aexp #t tmpcount param))
                 (set! arg-lists (cons (third param-res) arg-lists)))
               
               (for [(param arg-lists)]
                 ;(define nparam (add-fun-name nfun-name param))
                 (set! program (cons (list 'move (list tmp-count 'SP) param) program))
                 (set! tmp-count (- tmp-count 1)))
               (set! program (cons (list 'add 'SP 'SP params-len) program))
               ;; TODO: not sure if moving FP and SP is needed
               
               ;(set! program (cons (list 'move 'FP 'SP) program))
               (set! program (cons (list 'jsr 'RETURN-ADDR nfun-name) program))
               (set! program (cons (list 'sub 'SP 'SP params-len) program))
               (list 'RETURN-VAL tmpcount 'RETURN-VAL)]
        ;;(set! SP (sub SP tmp-count))
              [else (error "incorrect number of arguments")])]
        [(hash-has-key? aexpop-ht (first aexp))
         (match aexp
           [`(,op ,aexp1 ,aexp2)
            (define nop (hash-ref aexpop-ht op))
            (define res1 (eval-aexp #f tmpcount aexp1))
            (define var1 (car res1))
            (set! tmpcount (+ (cadr res1) tmpcount))
            (define res2 (eval-aexp #f tmpcount aexp2))
            (define var2 (car res2))
            (set! tmpcount (+ (cadr res2) tmpcount))
            (cond [fun
                   (define ntmp (generate))
                   (set! tmpcount (+ tmpcount 1))
                   (define res (list nop ntmp (caddr res1) (caddr res2)))
                   (set! program (cons res program))
                   (list ntmp tmpcount ntmp)]
                  [(and (number? var1) (hash-has-key? vargs-ht var2))
                   (define res (list nop (caddr res2) (caddr res1) (caddr res2)))
                   (set! program (cons res program))
                   (list #\0 tmpcount (caddr res2))]
                  [(and (number? var2) (hash-has-key? vargs-ht var1))
                   (define res (list nop (caddr res1) (caddr res1) (caddr res2)))
                   (set! program (cons res program))
                   (list #\0 tmpcount (caddr res1))]
                  [else
                   (define ntmp (generate))
                   (set! tmpcount (+ tmpcount 1))
                   (define res (list nop ntmp (caddr res1) (caddr res2)))
                   (set! program (cons res program))
                   (list ntmp tmpcount ntmp)])])]
        [else (error "undefined function")]))

;; eval-bexp: tmpcount bexp
;; - update program and tmpcount
;; - return (list var/tmp tmpcount)
(define (eval-bexp tmpcount bexp)
  (cond [(symbol? bexp)
         (define res (tf-convert bexp))
         (list res tmpcount)]
        [else
         (match bexp
           [`(and ,lobexp ...)
            (define ntmp (generate))
            (set! tmpcount (+ tmpcount 1))
            (define res (eval-lobexp tmpcount lobexp empty))
            (define ncount (cadr res))
            (set! tmpcount ncount)
            (define lontmp (car res))
            (define nline (cons 'land (cons ntmp lontmp)))
            (set! program (cons nline program))
            (list ntmp tmpcount)]
           [`(or ,lobexp ...)
            (define ntmp (generate))
            (set! tmpcount (+ tmpcount 1))
            (define res (eval-lobexp tmpcount lobexp empty))
            (define ncount (cadr res))
            (set! tmpcount ncount)
            (define lontmp (car res))
            (define nline (cons 'lor (cons ntmp lontmp)))
            (set! program (cons nline program))
            (list ntmp tmpcount)]
           [`(,op ,aexp1 ,aexp2)
            (define nop (hash-ref bexpop-ht op))
            (define ntmp (generate))
            (set! tmpcount (+ tmpcount 1))
            (define res1 (eval-aexp #f tmpcount aexp1))
            (define var1 (caddr res1))
            (set! tmpcount (+ (cadr res1) tmpcount))
            (define res2 (eval-aexp #f tmpcount aexp2))
            (define var2 (caddr res2))
            (set! tmpcount (+ (cadr res2) tmpcount))
            (define res (list nop ntmp var1 var2))
            (set! program (cons res program))
            (list ntmp tmpcount)]
           [`(,op ,aexp)
            (define nop (hash-ref bexpop-ht op))
            (define ntmp (generate))
            (set! tmpcount (+ tmpcount 1))
            (define res (eval-bexp tmpcount aexp))
            (define var (car res))
            (set! tmpcount (+ (cadr res) tmpcount))
            (define nline (list nop ntmp var))
            (set! program (cons nline program))
            (list ntmp tmpcount)])]))
  
;; interp a stmt
(define (interp loop stmt tmpcount)
  (match stmt
    [`(return ,x)
    ;;TODO: after x is evaluated, x needs to be stored in the global RETURN-VAL
    (define res (eval-aexp #f tmpcount x)) ;; TODO: assume return is the last statement to call
    ;; (list var tmpcount var)
    (set! tmpcount (+ (cadr res) tmpcount))
    ;; the previous line will return the name to move FP to
    (set! program (cons (list 'move 'RETURN-VAL (caddr res)) program))
    (if loop tmpcount (set! s-cur (- s-cur tmpcount)))]
    [`(print ,s)
     (cond [(string? s)
            (define nline (list 'print-string s))
            (set! program (cons nline program))
            (if loop tmpcount (set! s-cur (- s-cur tmpcount)))]
           [(number? s)
            (define nline (list 'print-val s))
            (set! program (cons nline program))
            (if loop tmpcount (set! s-cur (- s-cur tmpcount)))]
           [else
            (define res (eval-aexp #f tmpcount s))
            (set! tmpcount (+ (cadr res) tmpcount))
            (define nvar (caddr res))
            (cond [(number? nvar)
                   (define ns (mod-sym s))
                   (define nline (list 'print-val ns))
                   (set! program (cons nline program))
                   (if loop tmpcount (set! s-cur (- s-cur tmpcount)))]
                  [else (define nline (list 'print-val nvar))
                        (set! program (cons nline program))
                        (if loop tmpcount (set! s-cur (- s-cur tmpcount)))])])]
    [`(set ,id ,exp)
     (cond [(aexp? exp)
            (define mid 'x)
            (cond [(hash-has-key? tmps-ht id) (set! mid id)]
                  [else (define res (hash-ref vargs-ht id))
                        (set! mid (list (car res) 'FP))])
            
            (define res (eval-aexp #f tmpcount exp))

            (set! tmpcount (+ (cadr res) tmpcount))
            (define var (caddr res))

            (cond [(char? var)
                   (if loop tmpcount (set! s-cur (- s-cur tmpcount)))]
                  [else (define nline (list 'move mid var))
                        (set! program (cons nline program))
                        (if loop tmpcount (set! s-cur (- s-cur tmpcount)))])]
           [(bexp? exp)
            (define mid 'x)
            (cond [(hash-has-key? tmps-ht id) (set! mid id)]
                  [else (define res (hash-ref vargs-ht id))
                        (set! mid (list (car res) 'FP))])
            (define res (eval-bexp tmpcount exp))
            (set! tmpcount (+ (cadr res) tmpcount))
            (define var (car res))
            (define nline (list 'move mid var))
            (set! program (cons nline program))
            (if loop tmpcount (set! s-cur (- s-cur tmpcount)))])]
    [`(seq ,lostmt ...)
     (set! tmpcount (eval-loop tmpcount lostmt))
     (if loop tmpcount (set! s-cur (- s-cur tmpcount)))]
    [`(iif ,bexp ,stmt1 ,stmt2)
     (define stmt1-start (create-label))
     (define stmt1-end (create-label))
     (define res (eval-bexp tmpcount bexp))
     (set! tmpcount (+ (cadr res) tmpcount))
     (define var (car res))
     (define nline (list 'branch var stmt1-start))
     (set! program (cons nline program))
     (interp loop stmt2 0)
     (set! nline (list 'jump stmt1-end))
     (set! program (cons nline program))
     (set! nline (list 'label stmt1-start))
     (set! program (cons nline program))
     (interp loop stmt1 0)
     (set! nline (list 'label stmt1-end))
     (set! program (cons nline program))
     (if loop tmpcount (set! s-cur (- s-cur tmpcount)))]
    [`(while ,bexp ,lostmt ...)
     (define loop-top (create-label))
     (define loop-body (create-label))
     (define loop-end (create-label))
     (define nline (list 'label loop-top))
     (set! program (cons nline program))
     (define res (eval-bexp tmpcount bexp))
     (set! tmpcount (+ (cadr res) tmpcount))
     (define var (car res))
     (set! nline (list 'branch var loop-body))
     (set! program (cons nline program))
     (set! nline (list 'jump loop-end))
     (set! program (cons nline program))
     (set! nline (list 'label loop-body))
     (set! program (cons nline program))
     (set! tmpcount (eval-loop tmpcount lostmt))
     (set! nline (list 'jump loop-top))
     (set! program (cons nline program))
     (set! nline (list 'label loop-end))
     (set! program (cons nline program))
     (if loop tmpcount (set! s-cur (- s-cur tmpcount)))]
    [`(skip)
     (if loop tmpcount (set! s-cur (- s-cur tmpcount)))]))

(define (insert-data)
  (for ([(key value) (in-hash tmps-ht)])
    (define res (list 'data key value))
    (set! program (cons res program))))


;; what about empty function
(define (eval-stmts stmts)
  (cond [(empty? stmts) (error "no statements in function")]
        [(empty? (rest stmts))
         (cond [(symbol=? (car (car stmts)) 'return)
                (interp #f (car stmts) 0)]
               [else (error "last statement is not return")])]
        
;         (define nline (list 'halt))
;         (set! program (cons nline program))
;         (for ([(key value) (in-hash var-ht)])
;           (define mvar (mod-sym key))
;           (define res (cons (list 'data mvar value) program))
;           (set! program res))
;         
;         (reverse program)]
        [else (interp #f (car stmts) 0) (eval-stmts (cdr stmts))]))

;; Assume the sexp is a list
;; (vars [] stmt ...)
;; global variables
;; RETURN-ADDR
;; RETURN-VAL

;; local variables
;; RETURN-ADDR
;; RETURN-VAL
(define (compile-function fun)
  (set! vargs-ht (make-hash))
  ;; (set! tmps-ht (make-hash))
  (define fun-name (first (second fun)))
  (define nfun-name (mod-sym fun-name))
  (set! program (cons (list 'label nfun-name) program))
  ;; Args
  (define args (rest (second fun)))
  (define args-len (length args))
  (define arg-counter 0)
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
  ;; Epilogue
  (set! program (cons (list 'sub 'SP 'SP size-name) program))
  (set! program (cons (list 'move 'FP (list nFP 'SP)) program))
  (set! program (cons (list 'move 'RETURN-ADDR (list nRTA 'SP)) program))
  (if (symbol=? fun-name 'main)
      (set! program (cons (list 'halt) program))
  (set! program (cons (list 'jump 'RETURN-ADDR) program))))
         



         
;         (define local-fp-name (mod-arg fun-name "FP"))
;         (define local-return-addr (mod-arg fun-name "RETURN-ADDR"))
;         (hash-set! var-ht (make-hash))
;         (hash-set! tmps-ht (make-hash)) ;; tmps is 
;         (define args (rest (second sexp)))
;    
;         ;; TODO: check for main existence
;         (define vars (second (third sexp)))
;         (define stmts (third (third sexp)))
;         (define local-size (mod-sym fun-name "SIZE"))
;         (cons '(label fun-name) program)
;         (if (hash-has-key? fun-name-ht fun-name)
;             (error "duplicate")
;             (hash-set! fun-name-ht fun-name 0)) ;;TODO: return void
;         (define counter -1)
;         (for ([arg args])
;           (define marg (mod-arg fun-name arg))
;           (define arg-line '(const marg counter))
;           (if 
;            (hash-has-key? args-ht arg)
;            (error "duplicate")
;            (hash-set! args-ht arg arg-line))
;           (set! program (cons arg-line program))
;           (set! counter (- counter 1)))
;         (set! program (cons '(const local-fp-name 0) program))
;         (set! program (cons '(const local-return-addr 1) program))
;         (set! counter 2)
;         (for ([var vars])
;           (define mvar (mod-sym fun-name (car var)))
;           (define val (cadr var))
;           (if 
;            (hash-has-key? var-ht var) 
;            (error "duplicate") ;;TODO: will return void if error
;            (hash-set! var-ht var val))
;           (set! program (cons '(data mvar counter)))
;           (set! counter (add counter 1)))
;         (set! program (cons local-size (+ 1 (length vars))))
;         ;; Prologue
;         (set! program (cons '(move (local-fp-name SP) FP) program))
;         (set! program (cons '(move (local-return-addr SP) RETURN-ADDR) program))
;         (for [(var (in-hash var-ht))]
;           (set! program (cons '(move ((mod-sym fun-name var) SP) val))))
;         (set! program (cons '(move FP SP) program))
;         (set! program (cons '(add SP SP local-size)))
;         ;; Body
;         (eval-stmts stmts)
;         ;; Epilogue
;         (set! program (cons '(sub SP SP local-size) program))
;         (set! program (cons '(move FP (local-fp-name SP)) program))
;         (set! program (cons '(move RETURN-ADDR (local-return-addr FP))))
;         (set! program (cons '(jump RETURN-ADDR)))]))

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

(define arguments-error-test
'((fun (add a b) (vars [] (return (+ a b))))
  (fun (main) (vars [] (return (add 1))))))

(define arguments-duplicate-error-test
'((fun (add a a) (vars [] (return (+ a a))))))

(define local-duplicate-error-test
'((fun (add a b) (vars [(res 0) (res 1)] (return res)))))

(define mix-duplicate-error-test
'((fun (add a b) (vars [(a 0) (res 1)] (return res)))))

(define return-error-test
'((fun (main) (vars [(res 0)] (set res (+ 1 1)) (seq (set res (+ 2 2)) (set res (+ 2 3)))))))

(define test1
  '((fun (countdown n)
         (vars [(result 0)]
               (print n)
               (print "\n")
               (iif (> n 0)
                    (set result (countdown (- n 1)))
                    (skip))
               (return result)))
     (fun (main) 
          (vars [(n 10)] 
                (return (countdown n))))))
;

(define varg-offset-test 
'((fun (main) (vars [(res 0) (a 1) (b 2)] (set res a) (return res)))))

(define test4
  `((fun (main) (vars [(n 10) (fj 1) (fjm1 0) (t 0) (ans 0)]
         (iif (= n 0) 
              (set ans fjm1)
              (seq
               (while (> n 1) 
                      (print n)
                      (print "\n")
                      (set t fj) ;; t = 0
                      (set fj (+ fj fjm1)) ;; fj = 1
                      (set fjm1 t) ;; fjm1 = 0
                      (set n (- n 1))) ;; n 8
               (set ans fj)))
         (print ans)
         (return 0)))))

(define main-test 
'((fun (main)
  (vars [(result 0)]
    (return result)))))

;; Run code

(compile-simpl test1)
;;; (define assembled-code (primplify compiled-code))
;;; (load-primp assembled-code)
;;; (run-primp)
    
