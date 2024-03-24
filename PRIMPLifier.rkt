#lang racket

(define psym-table (make-hash))

(define (update-hash-lst lst)
  (for ([sym lst])
    (unless (hash-has-key? psym-table sym)
      (hash-set! psym-table sym (list "unknown" 0)))))

(define (print-hash-table ht)
  (for ([(key value) (in-hash ht)])
    (display key)
    (display ": ")
    (displayln value)))

(define (check-dup sym)
  (and (hash-has-key? psym-table sym) (not (string=? (first (hash-ref psym-table sym)) "unknown"))))

(define (check-deop opd)
  (match opd
    [`(,x ,y)
     (when (and (symbol? x) (not (hash-has-key? psym-table x))) (hash-set! psym-table x (list "unknown" 0)))
     (when (and (symbol? y) (not (hash-has-key? psym-table y))) (hash-set! psym-table y (list "unknown" 1)))]
    [x (when (and (symbol? x) (not (hash-has-key? psym-table x))) (hash-set! psym-table x (list "unknown" 2)))]))
      
(define (interp loi revloi inst pc halt)
  (if (empty? inst) (primplify1 (rest loi) (cons inst revloi) pc halt)
      (match inst
        [`(print-string ,v) (primplify1 (rest loi) (cons inst revloi) (+ pc 1) #t)]
        [`(halt) (primplify1 (rest loi) (cons inst revloi) (+ pc 1) #t)]
        [`(const ,sym ,v)
         (if (check-dup sym)
             (error "duplicate")
             (begin (hash-set! psym-table sym (list "const" v))
                    (primplify1 (rest loi) (cons inst revloi) pc halt)))]
        [`(label ,sym)
         (if (check-dup sym)
             (error "duplicate")
             (begin (hash-set! psym-table sym (list "label" pc))
                    (primplify1 (rest loi) (cons inst revloi) pc halt)))]
        [`(data ,sym (,n ,v))
         (cond [(check-dup sym)
                (error "duplicate")]
               [(symbol? v)
                (hash-set! psym-table sym (list pc v))
                (unless (hash-has-key? psym-table v) (hash-set! psym-table v (list "unknown" 0)))
                (primplify1 (rest loi) (cons inst revloi) (+ pc n) halt)]
               [else
                (hash-set! psym-table sym (list pc v))
                (primplify1 (rest loi) (cons inst revloi) (+ pc n) halt)])]
        [`(data ,sym ,lov ...)
         (cond [(check-dup sym)
                (error "duplicate")]
               [else
                (hash-set! psym-table sym (list pc lov))
                (update-hash-lst (filter symbol? lov))
                (primplify1 (rest loi) (cons inst revloi) (+ pc (length lov)) halt)])]
        [`(,op ,dest ,opd1 ,opd2)
         (check-deop dest)
         (check-deop opd1)
         (check-deop opd2)
         (primplify1 (rest loi) (cons inst revloi) (+ pc 1) halt)]
        [`(,op ,dest ,opd)
         (check-deop dest)
         (check-deop opd)
         (primplify1 (rest loi) (cons inst revloi) (+ pc 1) halt)]
        [`(print-string ,s) (primplify1 (rest loi) (cons inst revloi) (+ pc 1) halt)]
        [`(,op ,opd)
         (check-deop opd)
         (primplify1 (rest loi) (cons inst revloi) (+ pc 1) halt)]
        [x (cond [(symbol? x)
                  (unless (hash-has-key? psym-table x) (hash-set! psym-table x (list"unknown" 0)))
                  (primplify1 (rest loi) (cons inst revloi) (+ pc 1) halt)]
                 [else (primplify1 (rest loi) (cons inst revloi) (+ pc 1) halt)])])))

(define (find-sym orisym sym)
  (cond [(hash-has-key? psym-table sym)
         (define res (hash-ref psym-table sym))
         (define type (car res))
         (define value (cadr res))
         (cond [(string? type)
                (cond [(string=? type "unknown") (error "undefined symbol")]
                      [(string=? type "label") value]
                      [(symbol? value)
                       (cond [(symbol=? orisym value) (error "circular references")]
                             [else (find-sym orisym value)])]
                      [else value])] 
               [else type])]
        [else (error "undefined symbol")]))

(define (check-lov lst result)
  (cond [(empty? lst) result]
        [(symbol? (first lst))
         (define nv (find-sym (car lst) (car lst)))
         (check-lov (rest lst) (cons nv result))]
        [else (check-lov (rest lst) (cons (car lst) result))]))

(define (find-imm sym)
  (define res (hash-ref psym-table sym))
  (define type (first res))
  (define value (cadr res))
  (cond [(number? type) type]
        [(string? type)
         (cond [(string=? type "unknown") (error "undefined symbol")]
               [(string=? type "label") (error "incorrect")]
               [(if (symbol? value)
                    (cond [(symbol=? value sym) (error "circular")]
                          [else (define nv (find-imm value))
                                (hash-set! psym-table sym nv)
                                nv])
                    value)])]
        [(symbol? value) (find-imm value)]
        [else value]))

(define (check-label sym)
  (define res (hash-ref psym-table sym))
  (cond [(not (list? res)) res]
        [else (define type (first res))
              (and (string? type) (string=? type "label"))]))

(define (check-const sym)
  (define res (hash-ref psym-table sym))
  (cond [(not (list? res)) res]
        [else (define type (first res))
              (and (string? type) (string=? type "const"))]))

(define (check-data sym)
  (define res (hash-ref psym-table sym))
  (and (list? res) (number? (first res))))

(define (find-deop dest opd)
  (match opd
    [`(,x ,y)
     (cond [(symbol? x)
            (cond [(check-label x) (error "incorrect")]
                  [dest 
                   (define nx (find-imm x))
                   (cond [(symbol? y)
                          (cond [(check-label y) (error "incorrect")]
                                [(check-const y) (error "incorrect")]
                                [else
                                 (define ny (find-sym y y))
                                 (list nx (list ny))])]
                         [else (list nx y)])]
                  [else
                   (define nx (find-sym x x))
                   (cond [(symbol? y)
                          (cond [(check-label y) (error "incorrect")]
                                [(check-const y) (error "incorrect")]
                                [else
                                 (define ny (find-sym y y))
                                 (list nx (list ny))])]
                         [else (list nx y)])])]
           [(symbol? y)
            (cond [(check-label y) (error "incorrect")]
                  [(check-const y) (error "incorrect")]
                  [else 
                   (define ny (find-sym y y))
                   (list x (list ny))])]
           [else (list x y)])]
    [x (cond [(symbol? x)
              (define nx (find-sym x x))
              (if dest
                  (cond [(check-data x) (list nx)]
                        [(or (boolean? nx) (number? nx)) (error "incorrect")]
                        [(check-label x) nx]
                        [else (list nx)])
                  (cond [(check-label x) nx]
                        [(check-const x) nx]
                        [else (list nx)]))]
             [(and dest (boolean? x) (number? x)) (error "incorrect")]
             [else x])]))

(define (find-deop2 dest opd)
  (cond [(symbol? opd)
         (define no1 (hash-ref psym-table opd))
         (if (and (list? no1) (string? (first no1)) (string=? (first no1) "label")) (error "incorrect position")
             (find-deop dest opd))]
        [else (find-deop dest opd)]))

(define (translate loi inst result)
  (if (empty? inst) (primplify2 (rest loi) (cons inst result))
      (match inst
        [`(halt) (primplify2 (rest loi) (cons 0 result))]
        [`(const ,sym ,v)
         (cond [(symbol? v)
                (find-sym v v)
                (primplify2 (rest loi) result)]
               [else (primplify2 (rest loi) result)])]
        [`(label ,sym) (primplify2 (rest loi) result)]
        [`(data ,sym (,n ,v))
         (cond [(symbol? v)
                (define nv (find-sym v v))
                (define nlst (build-list n (lambda (x) nv)))
                (primplify2 (rest loi) (append nlst result))]
               [else
                (define nlst (build-list n (lambda (x) v)))
                (primplify2 (rest loi) (append nlst result))])]
        [`(data ,sym ,lov ...)
         (primplify2 (rest loi) (check-lov (reverse lov) result))]
        [`(,op ,dest ,opd1 ,opd2)
         (define nd (find-deop2 #t dest))
         (define no1 (find-deop2 #f opd1))
         (define no2 (find-deop2 #f opd2))
         (define res (list op nd no1 no2))
         (primplify2 (rest loi) (cons res result))]
        [`(branch ,opd1 ,opd2)
         (define no1 (find-deop2 #f opd1))
         (define no2 (find-deop #f opd2))
         (define res (list 'branch no1 no2))
         (primplify2 (rest loi) (cons res result))]
        [`(,op ,dest ,opd)
         (define nd (find-deop2 #t dest))
         (define no1 (find-deop2 #f opd))
         (define res (list op nd no1))
         (primplify2 (rest loi) (cons res result))]
        [`(print-val ,opd)
         (cond [(symbol? opd)
                (define res (hash-ref psym-table opd))
                (cond [(and (string? (first res)) (string=? (first res) "label"))
                       (error "incorrect")]
                      [else
                       (define no1 (find-deop #f opd))
                       (define res (list 'print-val no1))
                       (primplify2 (rest loi) (cons res result))])]
               [else
                (define no1 (find-deop #f opd))
                (define res (list 'print-val no1))
                (primplify2 (rest loi) (cons res result))])]
        [`(print-string ,v)
         (define res (list 'print-string v))
         (primplify2 (rest loi) (cons res result))]
        [`(,op ,opd)
         (cond [(string? opd)
                (define res (list op opd))
                (primplify2 (rest loi) (cons res result))]
               [else
                (define no1 (find-deop #f opd))
                (define res (list op no1))
                (primplify2 (rest loi) (cons res result))])]
        [x (cond [(symbol? x)
                  (define res (find-sym x x))
                  (primplify2 (rest loi) (cons res result))]
                 [else (primplify2 (rest loi) (cons x result))])])))
    
(define (primplify2 loi result)
  (cond [(empty? loi) result]
        [else (translate loi (first loi) result)]))

(define (primplify1 loi revloi pc halt)
  (cond [(empty? loi) (primplify2 revloi empty)]
        [else (interp loi revloi (first loi) pc halt)]))

(define (primplify loi)
  (primplify1 loi empty 0 #f))

;(define test
;  '((const n 15)
;    (label TOP)
;    (ge TMP i n)
;    (branch TMP TERM)
;    (move TMP A)
;    (add A A B)
;    (move B TMP)
;    (add i i 1)
;    (jump TOP)
;    (label TERM)
;    (print-val B)
;    (print-string "\n")
;    (data i 0)
;    (data A 1)
;    (data B 0)
;    (data TMP 0)))

;(require "PRIMPL.rkt")
;(define assembled-code (primplify test))
;(print assembled-code)
;(load-primp assembled-code)
;(run-primp)