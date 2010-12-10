; Maruseac Mihai, 341C3

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; README - TODO
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; GLOBAL AUXILIARY FUNCS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; first, convert to Haskel-ish notations
(require srfi/1)
(define (oldtake l n) (take l n))
(define (olddrop l n) (drop l n))

; some auxiliary functions, used below
(define (nub-aux l seen) (if (null? l) seen (if (elem? (car l) seen) (nub-aux (cdr l) seen) (nub-aux (cdr l) (cons (car l) seen)))))
(define (andList l) (foldl (lambda (x y) (and x y)) #t l))
(define (orList l) (foldl (lambda (x y) (and x y)) #f l))
(define (stringCompare s1 s2) (string<? s1 s2))
(define (take n l) (oldtake l n))
(define (drop n l) (olddrop l n))
(define (head l) (if (null? l) '() (car l)))
(define (nub l) (reverse (nub-aux l '())))
(define ++ (lambda l (apply append l)))
(define +++ (lambda l (nub (apply ++ l))))
(define (-- l1 l2) (filter (lambda (x) (not (elem? x l2))) l1))
(define (elem? x l) (if (null? l) #f (if (equal? x (car l)) #t (elem? x (cdr l)))))
(define (in? l1 l2) (andList (map (lambda (x) (elem? x l2)) l1)))

(define (variable? s) (char-upper-case? (first (string->list (symbol->string s)))))
(define (substTerm x bindName bindValue) (if (equal? x bindName) bindValue x))

(define (canonicalStateForm state) (sort state (lambda (p1 p2) (stringCompare (symbol->string (predName p1)) (symbol->string (predName p2))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  OPERATOR AUXILIARY FUNCS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (opName op) (caar op))
(define (opVars op) (cdar op))
(define (opPred op) (cadr op))
(define (opAdd op) (cadddr op))
(define (opDel op) (caddr op))

(define (opFindName name opList) (head (filter (lambda (x) (equal? (opName x) name)) opList)))
(define (opFindNameArg name vars opList) (head (filter (lambda (x) (and (equal? (opName x) name) (equal? (opVars x) vars))) opList)))

(define (opApply op state) (predList+ (predList- state (opDel op)) (opAdd op)))
(define (opApplicable? op state) (and (opInstantiated? op) (in? (opPred op) state)))

(define (opInstantiated? op) (not (andList (map variable? (opVars op)))))
(define (opInstance op bindings) (foldl opBindVarVal op bindings))
(define (opBindVarVal bind op)
  (let*
      (
       (oldName (opName op))
       (oldVars (opVars op))
       (bindName (car bind))
       (bindValue (cdr bind))
       (oldPred (opPred op))
       (oldAdd (opAdd op))
       (oldDel (opDel op))
       (newVars (map (lambda (x) (substTerm x bindName bindValue)) oldVars))
       (newPred (map (lambda (x) (subst x bindName bindValue)) oldPred))
       (newAdd (map (lambda (x) (subst x bindName bindValue)) oldAdd))
       (newDel (map (lambda (x) (subst x bindName bindValue)) oldDel))
       )
    (list (cons oldName newVars) newPred newDel newAdd)
    )
  )

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

(define (predList+ l1 l2) (+++ l1 l2))
(define (predList- l1 l2) (-- l1 l2))

(define (subst pred bindName bindValue) (map (lambda (x) (substTerm x bindName bindValue)) pred))

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
       (arg (actArgs act))
       (op (opFindNameArg name arg opList))
       )
    (if (null? op)
        (begin (display "### Trying to apply unknown/non-instantiated op: ")(newline)
               (printAct act)(display "=> (ACT IGNORED)")(newline)
               state)
        (if (opApplicable? op state) (opApply op state)
            (begin (display "### Error on applying op: ")(newline)
                   (printOp op)(display "=> (OP IGNORED)")(newline)
                   state)))
    )
  )

(define (printAct act)
  (display (actName act))(display ": ")
  (display (actArgs act))(newline)
  act
  )

(define testAction '(move d1 d2 p3))
(define testInitState '((disc d1) (disc d2)
                                  (smaller d2 p1) (smaller d2 p2) (smaller d2 p3) (smaller d1 d2) (smaller d1 p1) (smaller d1 p2) (smaller d1 p3)
                                  (clear d1) (clear p2) (clear p3)
                                  (on d1 d2) (on d2 p1)))
(define testBindings1 '((A . a)))
(define testBindings2 '((A . a) (B . b) (C . c)))
(define testBindings3 '((A . d1) (B . d2) (C . p3)))

; test for first day of work: Test if all functions needed for plan application are succesful.
(display "Test plan apply ")
(if (equal? (canonicalStateForm (actApply testAction testInitState 
                      (list (opInstance testOp testBindings1) (opInstance testOp testBindings2) (opInstance testOp testBindings3))))
            '(
              (clear d1) (clear p2) (clear d2)
              (disc d1) (disc d2)
              (on d2 p1) (on d1 p3)
              (smaller d2 p1) (smaller d2 p2) (smaller d2 p3) (smaller d1 d2) (smaller d1 p1) (smaller d1 p2) (smaller d1 p3)
              )
            )
    (display "passed") (display "failed"))
(newline)

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
