#lang racket

;; Group work done by Junzhang Luo, Elyn Huang

(define tmps-ht (make-hash))
(define var-ht (make-hash))
(define args-ht (make-hash))
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

;;TODO: write a mod-arg
;;TODO: mod-var


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
(define (eval-aexp tmpcount aexp)
  (cond [(number? aexp)
         (list aexp tmpcount aexp)]
        [(symbol? aexp)
         (define nid (mod-sym aexp))
         (list aexp tmpcount nid)]
        [(and (list? aexp) (hash-has-key? fun-name-ht (first aexp))) 
        ;TODO: need to have the function in hash first
        ;;TODO: check there are the right number of parameters being passed in to the function
        (define params (rest aexp))
        (define tmp-count 0) ;; Asume SP points to the end of function
        (for [(param params)]
          ;; Create tmp variables at the end of current stack, relative to SP
          ;; For passing arguments to the called function
          ;; TODO: make sure parameters are in right order
          (set! program (cons '(move (tmp-count SP) param)))
          (set! tmp-count (add tmp-count 1)))
        ;; TODO: not sure if moving FP and SP is needed
        ;;(set! SP (add SP tmp-count))
        (set! program (cons '(jsr RETURN-ADDR (first aexp)) program))
        ;;(set! SP (sub SP tmp-count))
        ]
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
            (define res1 (eval-aexp tmpcount aexp1))
            (define var1 (caddr res1))
            (set! tmpcount (+ (cadr res1) tmpcount))
            (define res2 (eval-aexp tmpcount aexp2))
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
    (eval-aexp 0 x) ;; TODO: assume return is the last statement to call
    ]
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
  (for ([(key value) (in-hash tmps-ht)])
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
;; (vars [] stmt ...)
;; global variables
;; RETURN-ADDR
;; RETURN-VAL

;; local variables
;; RETURN-ADDR
;; RETURN-VAL
(define (compile-function sexp)
  (define local-fp-name (mod-arg fun-name "FP"))
  (define local-return-addr (mod-arg fun-name "RETURN-ADDR"))
    (hash-set! var-ht (make-hash))
    (hash-set! tmps-ht (make-hash)) ;; tmps is 
    (define args (rest (second sexp)))
    (define fun-name (mod-sym (first (second sexp))))
    ;; TODO: check for main existence
  (define vars (second (third sexp)))
  (define stmts (third (third sexp)))
  (define local-size (mod-sym fun-name "SIZE"))
  (cons '(label fun-name) program)
  (if (hash-has-key? fun-name-ht fun-name)
  (error "duplicate")
  (hash-set! fun-name-ht fun-name 0)) ;;TODO: return void
  (define counter -1)
  (for ([arg args])
    (define marg (mod-arg fun-name arg))
    (define arg-line '(const marg counter))
    (if 
    (hash-has-key? args-ht arg)
    (error "duplicate")
    (hash-set! args-ht arg arg-line))
    (set! program (cons arg-line program))
    (set! counter (- counter 1)))
  (set! program (cons '(const local-fp-name 0) program))
  (set! program (cons '(const local-return-addr 1) program))
  (set! counter 2)
  (for ([var vars])
    (define mvar (mod-sym fun-name (car var)))
    (define val (cadr var))
    (if 
      (hash-has-key? var-ht var) 
      (error "duplicate") ;;TODO: will return void if error
      (hash-set! var-ht var val))
    (set! program (cons '(data mvar counter)))
    (set! counter (add counter 1)))
  (set! program (cons local-size (+ 1 (length vars))))
  ;; Prologue
  (set! program (cons '(move (local-fp-name SP) FP) program))
  (set! program (cons '(move (local-return-addr SP) RETURN-ADDR) program))
  (for [(var (in-hash var-ht))]
    (set! program (cons '(move ((mod-sym fun-name var) SP) val))))
  (set! program (cons '(move FP SP) program))
  (set! program (cons '(add SP SP local-size)))
  ;; Body
  (eval-stmts stmts)
  ;; Epilogue
  (set! program (cons '(sub SP SP local-size) program))
  (set! program (cons '(move FP (local-fp-name SP)) program))
  (set! program (cons '(move RETURN-ADDR (local-return-addr FP))))
  (set! program (cons '(jump RETURN-ADDR))))

(define (compile-program losexp)
    (set! program empty)
    (for [(func losexp)]
      (compile-function func))
    ;; Global datas
    (set! program (cons '(data RETURN-VAL 0) program))
    (set! program (cons '(data RETURN-ADDR 0) program))
    (set! program (cons '(data FP 0) program))
    (set! program (cons '(data SP" 0) program)))

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
;(define test2
;  '(var ((x 10) (y 1))
;        (print "\n")
;        (print 1)))
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
;(define test10
;  '(vars [(x 10) (y 131)]
;         (iif (and (= x y) (< x y))
;          (print 1111)
;          (print 2222))))

;(define first-test '(vars [(x 0) (y 1) (z 2)]
;                          (print y)))
;
;(define first-arith-test '(vars [(a 1) (b 2)]
;                                (set a b)
;                                (print (+ a b))))
;
;(define basic-test '(vars [(x 10) (y 1)]
;                          (while (> x 0)
;                                 (set y (* 2 y))
;                                 (set x (- x 1)))
;                          (print y)))
;
;(define iff-even-odd-test '(vars [(a 17) (b 5)]
;                                 (iif (= (mod a 2) 0)
;                                      (iif (= (mod b 2) 1)
;                                           (seq (print "a even, b odd: (a + b) = ")
;                                                (print (+ a b)))
;                                           (seq (print "a even, b even: (a - b) = ")
;                                                (print (- a b))))
;                                      (iif (= (mod b 2) 0)
;                                           (seq (print "a odd, b even: (a * b) = ")
;                                                (print (* a b)))
;                                           (seq (print "a odd, b odd: (a / b) = ")
;                                                (print (div a b)))))
;                                 (print "\n")
;                                 (print a)
;                                 (print "\n")
;                                 (print b)
;                                 (print "\nProgram done!\n")))
;
;(define perfect-num-test '(vars [(i 1) (j 0) (acc 0)]
;                                (while (<= i 10000)
;                                       (set j 1)
;                                       (set acc 0)
;                                       (while (< j i)
;                                              (iif (= (mod i j) 0)
;                                                   (set acc (+ acc j))
;                                                   (skip))
;                                              (set j (+ j 1)))
;                                       (iif (= acc i)
;                                            (seq
;                                             (print i)
;                                             (print "\n"))
;                                            (skip))
;                                       (set i (+ i 1)))))
;
;(define var-name-test '(vars [(TMP0 2) (LABEL0 1) (TMP1 2) (LABEL1 1)]
;                             (iif (= (+ (+ TMP0 TMP1) LABEL0) 5)
;                                  (print (+ (* LABEL0 TMP0) (- TMP1 LABEL1)))
;                                  (skip))))
;
;(define fibonacci-test '(vars [(a 1) (b 0) (i 0) (n 100)]
;                              (while (<= i n)
;                                     (print b)
;                                     (print "\n")
;                                     (set a (+ a b))
;                                     (set b (- a b))
;                                     (set i (+ i 1)))))
;
;(define slow-C10-test '(vars [(m 1) (n 100) (num -1) (TMP 0) (rev 0) (i 2) (squarefree 1)]
;                             (set num m)
;                             (while (<= num n)
;                                    (set TMP num)
;                                    (set rev 0)
;                                    (while (> TMP 0)
;                                           (set rev (+ (* 10 rev) (mod TMP 10)))
;                                           (set TMP (div TMP 10)))
;                                    (set squarefree 1)
;                                    (set i 2)
;                                    (while (and (= squarefree 1) (<= (* i i) num))
;                                           (iif (= (mod num (* i i)) 0)
;                                                (set squarefree 0)
;                                                (skip))
;                                           (set i (+ i 1)))
;                                    (iif (and (= rev num) (= squarefree 1))
;                                         (seq (print num)
;                                              (print "\n"))
;                                         (skip))
;                                    (set num (+ num 1)))))
;
;(define simple-bool-test '(vars [(numnumbers 0) (max 5)]
;                                (while (and (not (>= numnumbers max)))
;                                       (set numnumbers (+ numnumbers 1))
;                                       (print numnumbers))))
;
;(define bool-jungle-test '(vars [(a 172) (b 9821) (c 173) (d 10920) (e 71) (f 1227) (g 912) (numnumbers 0) (max 10)]
;                                (while
;                                 (and (or (>= ( * 8 a) (mod (+ b c) e))
;                                          (and (<= 12 g) (> (mod (* (+ c d) b) f) (mod (* a g) b)))
;                                          (= numnumbers 0))
;                                      (not (>= numnumbers max)))
;                                       (iif (<= a c)
;                                            (seq
;                                             (print "a <= c case\n")
;                                             (set a (+ (mod (* a d) f) (div b c))))
;                                            (seq
;                                             (print "a > c case\n")
;                                             (set c (* (- (* d e) g) (mod b (+ a f))))))
;                                       (set d (+ d (* (mod b e) (div b e))))
;                                       (iif (>= d f)
;                                            (seq
;                                             (print "d >= f case\n")
;                                             (set f (+ (* 9 a) (* (mod f e) (div d f))))
;                                             (set d (- 1901203 (* (mod (* a (* b e)) (+ f d)) c))))
;                                            (seq
;                                             (print "d < f case\n")
;                                             (set d (* (div (* 6 (+ f g)) a) (+ (mod (* g 171) (+ b c)) (+ a 15))))))
;                                       (set numnumbers (+ numnumbers 1))
;                                       (print a) (print " ") (print b) (print " ") (print c) (print " ") (print d)
;                                       (print " ") (print e) (print " ") (print f) (print " ") (print g) (print "\n"))))
;
;(define bool-alg-test '(vars [(a 2) (b 3) (c 12) (TMP 0) (rand 0)]
;                             (while (not (and (= (mod a 5) 0) (> b 310) (= (mod (* c 8) 9) 0)))
;                                    (iif (= (mod a 5) 0)
;                                         (seq (set TMP a)
;                                              (set a b)
;                                              (set b TMP))
;                                         (skip))
;                                    (iif (or (not (> b 310)) (= (mod c 9) 0))
;                                         (seq (set rand (mod (mod (* (+ c b) 78162848712687993) 1000000007) 355))
;                                              (set b (+ b rand))
;                                              (set c (+ c rand)))
;                                         (skip))
;                                    (set a (+ a 1)) (set b (+ b 1)) (set c (+ c 1))
;                                    (print a) (print " ") (print b) (print " ") (print c) (print "\n"))
;                             (print a) (print " ") (print b) (print " ") (print c) (print "\n")))
;
;(compile-simpl fibonacci-test)
;(compile-simpl fibonacci-test)

;(display tmps)
;(display var-ht)

;(compile-simpl test)
;(print-ht ref-table)
;(display program)
