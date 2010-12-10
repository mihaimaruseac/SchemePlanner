; Maruseac Mihai, 341C3

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; README - TODO
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; GLOBAL AUXILIARY FUNCS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (variable? s) (char-upper-case? (first (string->list (symbol->string s)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  OPERATOR AUXILIARY FUNCS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (opName op) (caar op))
(define (opVars op) (cdar op))
(define (opPred op) (cadr op))
(define (opAdd op) (cadddr op))
(define (opDel op) (caddr op))

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
                 ((on A C) (clear B))
                 ((on A B) (clear C))
                 ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  PREDICATE AUXILIARY FUNCS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (predName pred) (car pred))
(define (predArgs pred) (cdr pred))

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

(define (printAct act)
  (display (actName act))(display ": ")
  (display (actArgs act))(newline)
  act
  )

(define testAction '(move d1 d2 p3))

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
