#lang racket

(define tmps (make-hash))
(define var-ht (make-hash))
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
         (hash-set! tmps ntmp s-cur) ntmp]
        [else (set! s-cur curtop) (string->symbol (string-append "TMP" (number->string s-cur)))]))

(define (create-label)
  (set! labels (+ labels 1))
  (string->symbol (string-append "LABEL" (number->string labels))))

;; add "_" in front of SIMPL variables
(define (mod-sym sym)
  (string->symbol (string-append "_" (symbol->string sym))))

;(define (print-ht ht)
;  (for ([(key val) (in-hash ht)])
;    (display key)
;    (display ": ")
;    (displayln val)))

;; Check aexp
(define (aexp? exp)
  (cond [(list? exp) (hash-has-key? aexpop-ht (first exp))]
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

;(define (eval-seq lostmt)
;  (cond [(empty? lostmt) (void)]
;        [else (interp #f (first lostmt) 0)
;              (eval-seq (rest lostmt))]))

;; eval-aexp: tmpcount aexp
;; - update program and tmpcount
;; - return (list type tmpcount placeholder)
(define (eval-aexp tmpcount aexp)
  (cond [(number? aexp)
         (list aexp tmpcount aexp)]
        [(symbol? aexp)
         (define nid (mod-sym aexp))
         (list aexp tmpcount nid)]
        [else
         (match aexp
           [`(,op ,aexp1 ,aexp2)
            (define nop (hash-ref aexpop-ht op))
            (define res1 (eval-aexp tmpcount aexp1))
            (define var1 (car res1))
            (set! tmpcount (+ (cadr res1) tmpcount))
            (define res2 (eval-aexp tmpcount aexp2))
            (define var2 (car res2))
            (set! tmpcount (+ (cadr res2) tmpcount))
            (cond [(and (number? var1) (hash-has-key? var-ht var2))
                   (define res (list nop (caddr res2) (caddr res1) (caddr res2)))
                   (set! program (cons res program))
                   (list #\0 tmpcount (caddr res2))]
                  [(and (number? var2) (hash-has-key? var-ht var1))
                   (define res (list nop (caddr res1) (caddr res1) (caddr res2)))
                   (set! program (cons res program))
                   (list #\0 tmpcount (caddr res1))]
                  [else
                   (define ntmp (generate))
                   (set! tmpcount (+ tmpcount 1))
                   (define res (list nop ntmp (caddr res1) (caddr res2)))
                   (set! program (cons res program))
                   (list ntmp tmpcount ntmp)])])]))

;; eval-bexp: tmpcount bexp
;; - update program and tmpcount
;; - return (list var/tmp tmpcount)
(define (eval-bexp tmpcount bexp)
  (cond [(symbol? bexp)
         (define res (tf-convert bexp))
         (list res tmpcount)]
        [else
         (match bexp
           [`(,op ,aexp1 ,aexp2)
            (define nop (hash-ref bexpop-ht op))
            (define ntmp (generate))
            (set! tmpcount (+ tmpcount 1))
            (define res1 (eval-aexp tmpcount aexp1))
            (define var1 (caddr res1))
            (set! tmpcount (+ (cadr res1) tmpcount))
            (define res2 (eval-aexp tmpcount aexp2))
            (define var2 (caddr res2))
            (set! tmpcount (+ (cadr res2) tmpcount))
            (define res (list nop ntmp var1 var2))
            (set! program (cons res program))
            (list ntmp tmpcount)])]))
           
;; interp a stmt
(define (interp loop stmt tmpcount)
  (match stmt
    [`(print ,s)
     (cond [(string? s)
            (define nline (list 'print-string s))
            (set! program (cons nline program))
            (if loop tmpcount (set! s-cur (- s-cur tmpcount)))]
           [else
            (define res (eval-aexp tmpcount s))
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
            (define mid (mod-sym id))
            (define res (eval-aexp tmpcount exp))
            (set! tmpcount (+ (cadr res) tmpcount))
            (define var (car res))
            (cond [(char? var)
                   (if loop tmpcount (set! s-cur (- s-cur tmpcount)))]
                  [else (define nline (list 'move mid var))
                        (set! program (cons nline program))
                        (if loop tmpcount (set! s-cur (- s-cur tmpcount)))])]
           [(bexp? exp)
            (define mid (mod-sym id))
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
  (for ([(key value) (in-hash tmps)])
    (define res (list 'data key value))
    (set! program (cons res program))))
    
(define (eval-stmts stmts)
  (cond [(empty? stmts)
         (define nline (list 'halt))
         (set! program (cons nline program))
         (for ([(key value) (in-hash var-ht)])
           (define mvar (mod-sym key))
           (define res (cons (list 'data mvar value) program))
           (set! program res))
         (insert-data)
         (reverse program)]
        [else (interp #f (car stmts) 0) (eval-stmts (cdr stmts))]))

;; Assume the sexp is a list
(define (compile-simpl sexp)
  (define vars (cadr sexp))
  (define stmts (cddr sexp))
  (for ([var vars])
    (define mvar (mod-sym (car var)))
    (define val (cadr var))
    (hash-set! var-ht (car var) (cadr var)))
  (eval-stmts stmts))

;(define test
;  '(var ((x 10) (y 1))
;	(while (> x 0)
;		(set y (* 2 y))
;		(set x (- x 1))
;		(print y)
;		(print "\n"))))
;;
;;(define test1
;;  '(var ((x 10) (y 1))
;;        (print x)
;;        (print "\n")))
;;
;;(define test2
;;  '(var ((x 10) (y 1))
;;        (print "\n")
;;        (print x)))
;;
;;(define test3
;;  '(var ((x 10) (y 1))
;;        (seq
;;         (set y (* 2 y))
;;         (set x (- x 1))
;;         (set y (* 2 2)))))
;;
;(define test4
;  '(vars [(i 1) (j 0) (acc 0)]
;  (while (<= i 100)
;     (set j 1)
;     (set acc 0)
;     (while (< j i)
;        (iif (= (mod i j) 0)
;             (set acc (+ acc j))
;             (skip))
;        (set j (+ j 1)))
;     (iif (= acc i)
;          (seq
;            (print i)
;            (print "\n"))
;          (skip))
;     (set i (+ i 1)))))
;;
;;
;
;(define test5
;  '(vars [(x 10)] (> x 0)))
;
;(define test6
;  '(vars [(x 10) (y 0)]
;         (set y (+ 2 y))))
;
;(define test7
;  '(vars [(i 0)] (set i (+ i 1))))
;(define test8
;  '(var [(x 10) (y 1)]
;        (seq
;         (set y 1)
;         (set y (* 2 y))
;         (set x (- x 1))
;         (set y (* 2 2)))))

;(define test9
;  '(var [(x 10) (y 1)]
;        (set x (* (+ 2 x) 4))
;        (set x (* (+ x 3) 5))
;        (set x (* (+ 2 y) 4))
;        ))
;
;(compile-simpl test4)
;(display tmps)
;(display var-ht)

;(compile-simpl test)
;(print-ht ref-table)
;(display program)





