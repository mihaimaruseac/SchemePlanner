; Maruseac Mihai, 341C3

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; README - TODO
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; GLOBAL AUXILIARY FUNCS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(require srfi/1)
(define (oldtake l n) (take l n))
(define (olddrop l n) (drop l n))
(define (nub-aux l seen) (if (null? l) seen (if (elem? (car l) seen) (nub-aux (cdr l) seen) (nub-aux (cdr l) (cons (car l) seen)))))
(define (andList l) (foldl (lambda (x y) (and x y)) #t l))
(define (orList l) (foldl (lambda (x y) (and x y)) #f l))

(define (take n l) (oldtake l n))
(define (drop n l) (olddrop l n))
(define (head l) (if (null? l) '() (car l)))
(define (nub l) (reverse (nub-aux l '())))
(define (++ l1 l2) (append l1 l2))
(define (+++ l1 l2) (nub (++ l1 l2)))
(define (-- l1 l2) (filter (lambda (x) (not (elem? x l2))) l1))
(define (elem? x l) (if (null? l) #f (if (equal? x (car l)) #t (elem? x (cdr l)))))
(define (in? l1 l2) (andList (map (lambda (x) (elem? x l2)) l1)))

(define (variable? s) (char-upper-case? (first (string->list (symbol->string s)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  OPERATOR AUXILIARY FUNCS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (opName op) (caar op))
(define (opVars op) (cdar op))
(define (opPred op) (cadr op))
(define (opAdd op) (cadddr op))
(define (opDel op) (caddr op))

(define (opFindName name opList) (head (filter (lambda (x) (equal? (opName x) name)) opList)))

(define (opApply op state) (predList+ (predList- state (opDel op)) (opAdd op)))
(define (opApplicable? op state) (in? (opPred op) state))

(define (printOp op)
  (display (opName op))(display ": ")
  (display (opVars op))(newline)
  (display (opPred op))(newline)
  (display (opDel op))(newline)
  (display (opAdd op))(newline)
  op
  )

(define testOp '(
                 (move A B C)
                 ((disc A) (clear A) (on A B) (smaller A C) (clear C))
                 ((on A B) (clear C))
                 ((on A C) (clear B))
                 ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  PREDICATE AUXILIARY FUNCS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (predName pred) (car pred))
(define (predArgs pred) (cdr pred))

(define (predList+ l1 l2) (++ l1 l2))
(define (predList- l1 l2) (-- l1 l2))

(define (printPred pred)
  (display (predName pred))(display ": ")
  (display (predArgs pred))(newline)
  pred
  )

(define testPred '(smaller d2 p1))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  ACTION AUXILIARY FUNCS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (actName act) (car act))
(define (actArgs act) (cdr act))

(define (actApply act state opList)
  (let*
      (
       (name (actName act))
       (op (opFindName name opList))
       )
    (if (opApplicable? op state) (opApply op state)
        (begin (display "### Error on applying op: ")(newline)
               (printOp op)(display "=> (OP IGNORED)")(newline)
               state))
    )
  )

(define (printAct act)
  (display (actName act))(display ": ")
  (display (actArgs act))(newline)
  act
  )

(define testAction '(move d1 d2 p3))
(define testInitState (opPred (opFindName (actName testAction) (list testOp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  IMPLEMENTATION FUNCTIONS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; main func - call the defined funcs
; TODO
(define solve
  (lambda (operatori init scopuri)
    '()
    )
  )
