#lang racket

(define ref-table (make-hash))
(define program empty)

(define acount 0)
(define bcount 0)

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

(define (generate aexp)
  (cond [aexp (set! acount (+ acount 1))
              (string->symbol (string-append "A" (number->string acount)))]
        [else (set! bcount (+ bcount 1))
              (string->symbol (string-append "B" (number->string bcount)))]))

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
  (and (list? exp)
      (hash-has-key? aexpop-ht (first exp))))

;; Check bexp
(define (bexp? exp)
  (cond [(boolean? exp) true]
        [(list? exp) (hash-has-key? bexpop-ht (first exp))]
        [else false]))

;; Can aexp be stmt???
(define (interp stmt)
  (match stmt
    [`(print ,s)
     (cond [(string? s)
            (define res (cons (list 'print-string s) program))
            (set! program res)]
           [(aexp? s)
            (define nvar (generate #t)) ;; set aexp flag to true
            (eval-aexp s) ;; changes program
            (define res (cons (list 'print nvar) program))
            (set! program res)]
           [(symbol? s)
            (define mvar (mod-sym s))
            (define res (cons (list 'print mvar) program))
            (set! program res)]
           [else (define res (cons (list 'print s) program))
                 (set! program res)])]
    [`(set ,id ,exp)
     (cond [(aexp? exp) (eval-aexp exp)]
           [(bexp? exp) (eval-bexp exp)]
           [(symbol? exp)
            (define mvar (mod-sym exp))
            (define res (cons (list 'move id mvar) program))
            (set! program res)]
           [else
            (define res (cons (list 'move id exp) program))
            (set! program res)])]
    [`(seq ,lostmt ...)
     (for/list ([stmt lostmt])
       (eval-stmt #f stmt))]
    
(define (eval-stmt done? stmts)
  (cond [(empty? stmts)
         (when done?
             (reverse program))]
        [else (interp (car stmts)) (eval-stmt done? (cdr stmts))]))

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
  (eval-stmt #t stmts))

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





