#lang racket

(define tmps (make-hash))
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
   '<= 'lt
   'not 'not
   'and 'land
   'or 'lor
   'not 'lnot))

(define (generate tmpcount)
  (define curtop (+ s-cur 1)) ;; potentially generate one new tmp
  (cond [(> curtop s-top)
         (set! s-top (+ s-top 1)) (set! s-cur s-top)
         (define ntmp (string->symbol (string-append "TMP" (number->string s-cur))))
         (hash-set! ntmp s-cur) ntmp]
        [else (set! s-cur curtop) (string->symbol (string-append "TMP" (number->string s-cur)))]))

(define (create-label)
  (set! labels (+ labels 1))
  (string->symbol (string-append "Label" (number->string labels))))

;; add "_" in front of SIMPL variables
(define (mod-sym sym)
  (string->symbol (string-append "_" (symbol->string sym))))

(define (print-ht ht)
  (for ([(key val) (in-hash ht)])
    (display key)
    (display ": ")
    (displayln val)))

;; Check aexp
(define (aexp? exp)
  (cond [(list? exp) (hash-has-key? aexpop-ht (first exp))]
        [(symbol? exp) (not (or (symbol=? exp 'true) (symbol=? exp 'false)))]
        [else (number? exp)]))

;; Check bexp
(define (bexp? exp)
  (cond [(list? exp) (hash-has-key? bexpop-ht (first exp))]
        [eles (or (symbol=? exp 'true) (symbol=? exp 'false))]))

(define (tf-convert sym)
  (if (symbol=? sym 'true) #t #f))

;; eval-aexp: tmpcount aexp
;; - update program and tmpcount
;; - return (list var/tmp tmpcount)

(define (eval-aexp tmpcount aexp)
  (cond [(number? aexp) (list tmpcount aexp)]
        [(symbol? aexp)
         (define nid (mod-sym aexp))
         (list tmpcount nid)]
        [else
         (match aexp
           [`(,op ,aexp1 ,aexp2)

;; eval-bexp: tmpcount bexp
;; - 
;; -return (list var/tmp tmpcount)

;; Handles true, false and SIMPL variables
(define (interp stmt tmpcount)
  (match stmt
    [`(print ,s)
     (cond [(aexp? s)
            (define res (eval-aexp tmpcount s))
            (set! tmpcount (+ (cadr res) tmpcount))
            (define var (car res))
            (define nline (list 'print var))
            (set! program (cons nline program))
            (set! s-cur (- s-cur tmpcount))]
;            (set! tmpcount (+ tmpcount 1))
;            (define nvar (generate tmpcount)) ;; increment tmpcount by 1
;            (set! tmpcount (+ tmpcount (eval-aexp tmpcount s))) ;; changes program and returns new tmpcount
;            (define res (list 'print nvar))
;            (set! program (cons res program))
;            (set! s-cur (- s-cur tmpcount))]
;           [(symbol? s)
;            (define mvar (mod-sym s))
;            (define res (list 'print mvar))
;            (set! program (cons res program))
;            (set! s-cur (- s-cur tmpcount))]
           [else (define nline (list 'print-string s)) ;; s is a string
                 (set! program (cons nline program))
                 (set! s-cur (- s-cur tmpcount))])]
;           [else (define res (list 'print s))
;                 (set! program (cons res program))
;                 (set! s-cur (- s-cur tmpcount))])]
    [`(set ,id ,exp)
     (cond [(aexp? exp)
            (define mid (mod-sym id))
            (define res (eval-aexp tmpcount exp))
            (set! tmpcount (+ (cadr res) tmpcount))
            (define var (car res))
            (define nline (list 'move mid var))
            (set! program (cons nline program))
            (set! s-cur (- s-cur tmpcount))]
            
;            (set! tmpcount (+ tmpcount 1))
;            (define nvar (generate tmpcount))
;            (set! tmpcount (eval-aexp nvar tmpcount exp))
;            (define mid (mod-sym id))
;            (define res (list 'move mid nvar))
;            (set! program (cons res program))
;            (set! scur (- scur tmpcount))]
           
           [(bexp? exp)
            (define mid (mod-sym id))
            (define res (eval-bexp tmpcount exp))
            (set! tmpcount (+ (cadr res) tmpcount))
            (define var (car res))
            (define nline (list 'move mid var))
            (set! program (cons nline program))
            (set! s-cur (- s-cur tmpcount))])]

            
;            (set! tmpcount (+ tmpcount 1))
;            (define nvar (generate tmpcount))
;            (set! tmpcount (eval-bexp nvar tmpcount exp))
;            (define mid (mod-sym id))
;            (define res (list 'move mid nvar))
;            (set! program (cons res program))
;            (set! scur (- scur tmpcount))]
;           [(symbol? exp) ;; check if exp is SIMPL var or bexp 'true / 'false
;            (cond [(or (symbol=? exp 'true) (symbol=? exp 'false))
;                   (define mid (mod-sym id))
;                   (define nexp (tf-convert exp))
;                   (define res (list 'move mid nexp))
;                   (set! program (cons res program))
;                   (set! s-cur (- s-cur tmpcount))]
;                  [else (define mvar (mod-sym exp))
;                        (define mid (mod-sym id))
;                        (define res (list 'move mid mvar))
;                        (set! program (cons res program))
;                        (set! s-cur (- s-cur tmpcount))])]
;           ;; Must be number
;           [else (define res (list 'move id exp))
;                 (set! program (cons res program))
;                 (set! s-cur (- s-cur tmpcount))])]
    [`(seq ,lostmt ...)
     (for/list ([stmt lostmt])
       (interp stmt 0))] ;; Maybe solved, need test. TRYING TO SOLVE THE VOID ISSUE, SEE IN eval-stmts
    [`(iif ,bexp ,stmt1 ,stmt2)
     (define stmt1-start (create-label))
     (define stmt1-end (create-label))
     (define res (eval-bexp tmpcount bexp))
     (set! tmpcount (+ (cadr res) tmpcount))
     (define var (car res))
     (define nline (list 'branch var stmt1-label))
     (set! program (cons nline program))
     (interp stmt2 0)
     (set! nline (list 'jump stmt1-end))
     (set! program (cons nline program))
     (set! nline (list 'label stmt1-start))
     (set! program (cons nline program))
     (interp stmt1 0)
     (set! nline (list 'label stmt1-end))
     (set! program (cons nline program))
     (set! s-cur (- s-cur tmpcount))]
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
     (for/list ([stmt lostmt])
       (interp stmt 0)) ;; potential issue with tmp variables?, need to track total in while?
     (set! nline (list 'jump loop-top))
     (set! program (cons nline program))
     (set! nline (list 'label loop-end))
     (set! program (cons nline program))]
    [`(skip) (void)]))
    
(define (eval-stmts stmts)
  (cond [(empty? stmts)
         (define nline (list 'halt))
         (set! program (cons nline program))
         (reverse program)]
        [else (interp (car stmts) 0) (eval-stmts (cdr stmts))]))

;; Assume the sexp is a list
(define (compile-simpl sexp)
  (define vars (cadr sexp))
  (define stmts (cddr sexp))
  (for ([var vars])
    (define mvar (mod-sym (car var)))
    (define val (cadr var))
    (define res (cons (list 'data mvar val) program))
    ;; (hash-set! ref-table nvar (cadr var))
    (set! program res))
  (eval-stmts stmts))

(define test
  '(var ((x 10) (y 1))
	(while (> x 0)
		(set y (* 2 y))
		(set x (- x 1))
		(print y)
		(print “\n”))))

(define test1
  '(var ((x 10) (y 1))
        (print x)
        (print "\n")))
(compile-simpl test1)

;(compile-simpl test)
;(print-ht ref-table)
;(display program)





