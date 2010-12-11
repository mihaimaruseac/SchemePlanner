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
(define (stringCompare s1 s2) (string<? s1 s2))

; and and or with list arguments
(define (andList l) (foldl (lambda (x y) (and x y)) #t l))
(define (orList l) (foldl (lambda (x y) (or x y)) #f l))

; Haskell-ish take and drop
(define (take n l) (oldtake l n))
(define (drop n l) (olddrop l n))

; safe call of car -> returns '() if there's no answer
(define (head l) (if (null? l) '() (car l)))

; nubify = remove duplicates
(define (nub l) (reverse (nub-aux l '())))

; repeat
(define (repeat x n) (if (>= 0 n) '() (cons x (repeat x (- n 1)))))

; Haskell-ish append, used below to implement set addition
(define ++ (lambda l (apply append l)))
(define +++ (lambda l (nub (apply ++ l))))

; Set removal
(define (-- l1 l2) (filter (lambda (x) (not (elem? x l2))) l1))

; Cartesian products and multiple-list applications
(define (cAp2 f x l2) (map f (repeat x (length l2)) l2))
(define (cAp f l1 l2) (if (null? l1) '() (append (cAp2 f (car l1) l2) (cAp f (cdr l1) l2))))
(define (**2 l1 l2) (cAp (lambda (x y) (if (list? y) (cons x y) (cons x (list y)))) l1 l2))
(define (** l) (if (< (length l) 2) '() (if (= (length l) 2) (**2 (car l) (cadr l)) (**2 (car l) (** (cdr l))))))

; Set predicates
(define (elem? x l) (if (null? l) #f (if (equal? x (car l)) #t (elem? x (cdr l)))))
(define (in? l1 l2) (andList (map (lambda (x) (elem? x l2)) l1)))
(define (== l1 l2) (and (in? l1 l2) (in? l2 l1)))

; test if symbol is variable
(define (variable? s) (char-upper-case? (first (string->list (symbol->string s)))))

; substitution rule and unifications
(define (substTerm x bindName bindValue) (if (equal? x bindName) bindValue x))
(define (unify vals vars) (if (= (length vals) (length vars)) (unify-aux vals vars) '()))

(define (unify-aux vals vars)
  (if (null? vals) '()
      (if (variable? (car vars)) (cons (cons (car vars) (car vals)) (unify-aux (cdr vals) (cdr vars)))
          (cons (cons (car vars) (car vars)) (unify-aux (cdr vals) (cdr vars)))))
  )

; transform one list of predicates (state) to a canonicalStateForm
(define (canonicalStateForm state) (sort state (lambda (p1 p2) (stringCompare (symbol->string (predName p1)) (symbol->string (predName p2))))))

; define OO constant and undefined constant
(define OO 'OO)
(define UN '?)

; more cadddr goodies
(define (caddddr l) (car (cddddr l)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  OPERATOR AUXILIARY FUNCS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; record accesors
(define (opName op) (caar op))
(define (opVars op) (cdar op))
(define (opPred op) (cadr op))
(define (opAdd op) (cadddr op))
(define (opDel op) (caddr op))

; locators
(define (opFindName name opList) (head (filter (lambda (x) (equal? (opName x) name)) opList)))
(define (opFindNameArg name vars opList) (head (filter (lambda (x) (and (equal? (opName x) name) (equal? (opVars x) vars))) opList)))
(define (opFindResult pred opList) (if (null? opList) '() (+++ (getAllInstantiations pred (car opList)) (opFindResult pred (cdr opList)))))
(define (opFullInstance ops goal world) (opFullWorld world (opFullGoal goal ops)))

; applications
(define (opApply op state) (predList+ (predList- state (opDel op)) (opAdd op)))
(define (opApplicable? op state) (and (opInstantiated? op) (in? (opPred op) state)))

; instantiations and bindings
(define (opInstantiated? op) (not (orList (map variable? (opVars op)))))
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
       (newPred (map (lambda (x) (predSubst x bindName bindValue)) oldPred))
       (newAdd (map (lambda (x) (predSubst x bindName bindValue)) oldAdd))
       (newDel (map (lambda (x) (predSubst x bindName bindValue)) oldDel))
       )
    (list (cons oldName newVars) newPred newDel newAdd)
    )
  )

(define (getAllInstantiations pred op)
  (let*
      (
       (results (opAdd op))
       (pName (predName pred))
       (relevantResults (filter (lambda (p) (equal? pName (predName p))) results))
       (relevantBindings (map (lambda (R) (unify (predArgs pred) (predArgs R))) relevantResults))
       (obtainedOps (map (lambda (b) (opInstance op b)) relevantBindings))
       )
    obtainedOps
    )
  )

(define A
  '(
    (((move d1 p1 d2) ((disc d1) (clear d1) (on d1 p1) (smaller d1 d2) (clear d2)) ((on d1 p1) (clear d2)) ((on d1 d2) (clear p1))))
    (((move d1 d1 d2) ((disc d1) (clear d1) (on d1 d1) (smaller d1 d2) (clear d2)) ((on d1 d1) (clear d2)) ((on d1 d2) (clear d1))))
    (((move d1 p3 d2) ((disc d1) (clear d1) (on d1 p3) (smaller d1 d2) (clear d2)) ((on d1 p3) (clear d2)) ((on d1 d2) (clear p3))))
    )
  )
(define B
  '(((move d1 B d2) ((disc d1) (clear d1) (on d1 B) (smaller d1 d2) (clear d2)) ((on d1 B) (clear d2)) ((on d1 d2) (clear B))))
  )

(define (opFullGoal goal l) (apply +++ (map (lambda (x) (opFullInstancesGoal x goal)) l)))

(define (opFullInstancesGoal op goal)
  (if (opInstantiated? op) op
      (let
          (
           (firstUnInstPred (head (filter (lambda (p) (not (predInstantiated? p))) (opAdd op))))
           )
        (if (null? firstUnInstPred) op
            (let*
                (
                 (fUIPName (predName firstUnInstPred))
                 (instancesInGoal (filter (lambda (p) (equal? (predName p) fUIPName)) goal))
                 (relevantBindings (map (lambda (R) (unify (predArgs R) (predArgs firstUnInstPred))) instancesInGoal))
                 (results (map (lambda (b) (opInstance op b)) relevantBindings))
                 )
              (map (lambda (o) (opFullInstancesGoal o goal)) results)
              )))
      )
  )

(define (opFullWorld world l) (apply +++ (map (lambda (x) (opFullInstancesWorld x world)) l)))

; the following function should return quickly in a normal implementation
(define (opFullInstancesWorld op world) (if (opInstantiated? op) (list op) (map (lambda (b) (opInstance op b)) (getAllBindings (opVars op) world))))
(define (getAllBindings args world) (let ((lists (map (lambda (v) (if (variable? v) (map (lambda (x) (cons v x)) world) (list (cons v v)))) args))) (** lists)))

; printing
(define (opPrint op)
  (display (opName op))(display ": ")
  (display (opVars op))(newline)
  (display (opPred op))(newline)
  (display (opDel op))(newline)
  (display (opAdd op))(newline)
  op
  )

; test
(define opTest '(
                 (move A B C)
                 ((disc A) (clear A) (on A B) (smaller A C) (clear C))
                 ((on A B) (clear C))
                 ((on A C) (clear B))
                 ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  PREDICATE AUXILIARY FUNCS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; record accessors
(define (predName pred) (car pred))
(define (predArgs pred) (cdr pred))

; add and removal from state
(define (predList+ l1 l2) (+++ l1 l2))
(define (predList- l1 l2) (-- l1 l2))

; substitutions
(define (predInstantiated? p) (not (orList (map variable? (predArgs p)))))
(define (predSubst pred bindName bindValue) (map (lambda (x) (substTerm x bindName bindValue)) pred))

; printing
(define (predPrint pred)
  (display (predName pred))(display ": ")
  (display (predArgs pred))(newline)
  pred
  )

; test
(define predTest '(smaller d2 p1))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  ACTION AUXILIARY FUNCS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; record accessors
(define (actName act) (car act))
(define (actArgs act) (cdr act))

; applications
(define (actApply act state opList)
  (let*
      (
       (name (actName act))
       (arg (actArgs act))
       (op (opFindNameArg name arg opList))
       )
    (if (null? op)
        (begin (display "### Trying to apply unknown/non-instantiated op: ")(newline)
               (actPrint act)(display "=> (ACT IGNORED)")(newline)
               state)
        (if (opApplicable? op state) (opApply op state)
            (begin (display "### Error on applying op: ")(newline)
                   (opPrint op)(display "=> (OP IGNORED)")(newline)
                   state)))
    )
  )

; printing
(define (actPrint act)
  (display (actName act))(display ": ")
  (display (actArgs act))(newline)
  act
  )

; test
(define actTest '(move d1 d2 p3))
(define testInitState '((disc d1) (disc d2)
                                  (smaller d2 p1) (smaller d2 p2) (smaller d2 p3) (smaller d1 d2) (smaller d1 p1) (smaller d1 p2) (smaller d1 p3)
                                  (clear d1) (clear p2) (clear p3)
                                  (on d1 d2) (on d2 p1)))
(define testBindings1 '((A . a)))
(define testBindings2 '((A . a) (B . b) (C . c)))
(define testBindings3 '((A . d1) (B . d2) (C . p3)))

; test for first day of work: Test if all functions needed for plan application are succesful.
(display "Test plan apply ")
(if (== (canonicalStateForm (actApply actTest testInitState 
                                      (list (opInstance opTest testBindings1) (opInstance opTest testBindings2) (opInstance opTest testBindings3))))
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
;  AND NODE AUXILIARY FUNCS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Each AND node is a list of predicates

; expanding: create OR nodes with empty desirability slot
(define (andExpand n) (map (lambda (x) (cons desEmpty (list x))) n))

; printing
(define (andPrint n)
  (display "AND node: ")(newline)
  (map predPrint n)
  (display "END AND node")(newline)
  n
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  OR NODE AUXILIARY FUNCS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; each OR node contains one predicate and one desirability slot
(define (orPred n) (cadr n))
(define (orDes n) (car n))

; expanding: create OPR nodes with empty desirability slot
(define (orExpand n opList goal worldObjects)
  (let*
      (
       (ops (opFullInstance (opFindResult (orPred n) opList) goal worldObjects))
       )
    (map (lambda (x) (cons desEmpty (list x))) ops)
    )
  )

; printing
(define (orPrint n)
  (display "OR node: ")(display (orPred n))(display " ")(desPrint (orDes n))(newline)
  n
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  OPR NODE AUXILIARY FUNCS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; record accessors
(define (oprOp opr) (cadr opr))
(define (oprDes opr) (car opr))

; printing
(define (oprPrint opr)
  (display "OPR node: ")(desPrint (oprDes opr))(newline)(opPrint (oprOp opr))(newline)
  opr
  )

(define A
  '(
    ((?) ((move d1 p1 d2 d1) ((disc d1) (clear d1) (on d1 p1) (smaller d1 d2) (clear d2)) ((on d1 p1) (clear d2) (test d1)) ((on d1 d2) (clear p1))))
    ((?) ((move d1 p1 d2 d2) ((disc d1) (clear d1) (on d1 p1) (smaller d1 d2) (clear d2)) ((on d1 p1) (clear d2) (test d2)) ((on d1 d2) (clear p1))))
    ((?) ((move d1 p1 d2 p1) ((disc d1) (clear d1) (on d1 p1) (smaller d1 d2) (clear d2)) ((on d1 p1) (clear d2) (test p1)) ((on d1 d2) (clear p1))))
    ((?) ((move d1 p1 d2 p2) ((disc d1) (clear d1) (on d1 p1) (smaller d1 d2) (clear d2)) ((on d1 p1) (clear d2) (test p2)) ((on d1 d2) (clear p1))))
    ((?) ((move d1 p1 d2 p3) ((disc d1) (clear d1) (on d1 p1) (smaller d1 d2) (clear d2)) ((on d1 p1) (clear d2) (test p3)) ((on d1 d2) (clear p1))))
    ((?) ((move d2 p1 p2 d1) ((disc d2) (clear d2) (on d2 p1) (smaller d2 p2) (clear p2)) ((on d2 p1) (clear p2) (test d1)) ((on d2 p2) (clear p1))))
    ((?) ((move d2 p1 p2 d2) ((disc d2) (clear d2) (on d2 p1) (smaller d2 p2) (clear p2)) ((on d2 p1) (clear p2) (test d2)) ((on d2 p2) (clear p1))))
    ((?) ((move d2 p1 p2 p1) ((disc d2) (clear d2) (on d2 p1) (smaller d2 p2) (clear p2)) ((on d2 p1) (clear p2) (test p1)) ((on d2 p2) (clear p1))))
    ((?) ((move d2 p1 p2 p2) ((disc d2) (clear d2) (on d2 p1) (smaller d2 p2) (clear p2)) ((on d2 p1) (clear p2) (test p2)) ((on d2 p2) (clear p1))))
    ((?) ((move d2 p1 p2 p3) ((disc d2) (clear d2) (on d2 p1) (smaller d2 p2) (clear p2)) ((on d2 p1) (clear p2) (test p3)) ((on d2 p2) (clear p1))))
    )
  )
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  DESIRABILITY AUXILIARY FUNCS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; record accessors
(define (desOp d) (car d))
(define (desKill d) (cadr d))
(define (desGen d) (caddr d))
(define (desCz d) (cadddr d))
(define (desIFc d) (caddddr d))

; construct empty slot
(define desEmpty (list UN UN UN UN UN))

; get heuristic value
(define (desEval d) OO)

; printing
(define (desPrint d)
  (display "op = ")(display (desOp d))(display "; ")
  (display "kill = ")(display (desKill d))(display "; ")
  (display "gen = ")(display (desGen d))(display "; ")
  (display "cz = ")(display (desCz d))(display "; ")
  (display "IFc = ")(display (desIFc d))(display "; ")
  d
  )

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

(define (expandGoal g) (andExpand g))

; get world objects
(define (worldObjects init scopes) (apply +++ (+++ (map predArgs init) (map predArgs scopes))))

; testing Hanoi problem
(define HanoiOps '((
                    (move A B C)
                    ((disc A) (clear A) (on A B) (smaller A C) (clear C))
                    ((on A B) (clear C))
                    ((on A C) (clear B))
                    )))
(define HanoiState '((disc d1) (disc d2)
                               (smaller d2 p1) (smaller d2 p2) (smaller d2 p3) (smaller d1 d2) (smaller d1 p1) (smaller d1 p2) (smaller d1 p3)
                               (clear d1) (clear p2) (clear p3)
                               (on d1 d2) (on d2 p1)))
(define HanoiGoal '((clear p1) (clear d1) (on d1 d2) (on d2 p2) (clear p3)))

; tests for second day of work
(display "Test op instantiation1 ")
(define HanoiOps1  '((
                      (move A B C D)
                      ((disc A) (clear A) (on A B) (smaller A C) (clear C))
                      ((on A B) (clear C))
                      ((on A C) (clear B))
                      )))
(if (== (opFullInstance (opFindResult '(on d1 d2) HanoiOps1) HanoiGoal (worldObjects HanoiState HanoiGoal))
        '(((move d1 p1 d2 d1) ((disc d1) (clear d1) (on d1 p1) (smaller d1 d2) (clear d2)) ((on d1 p1) (clear d2)) ((on d1 d2) (clear p1)))
          ((move d1 p1 d2 d2) ((disc d1) (clear d1) (on d1 p1) (smaller d1 d2) (clear d2)) ((on d1 p1) (clear d2)) ((on d1 d2) (clear p1)))
          ((move d1 p1 d2 p1) ((disc d1) (clear d1) (on d1 p1) (smaller d1 d2) (clear d2)) ((on d1 p1) (clear d2)) ((on d1 d2) (clear p1)))
          ((move d1 p1 d2 p2) ((disc d1) (clear d1) (on d1 p1) (smaller d1 d2) (clear d2)) ((on d1 p1) (clear d2)) ((on d1 d2) (clear p1)))
          ((move d1 p1 d2 p3) ((disc d1) (clear d1) (on d1 p1) (smaller d1 d2) (clear d2)) ((on d1 p1) (clear d2)) ((on d1 d2) (clear p1)))
          ((move d1 d1 d2 d1) ((disc d1) (clear d1) (on d1 d1) (smaller d1 d2) (clear d2)) ((on d1 d1) (clear d2)) ((on d1 d2) (clear d1)))
          ((move d1 d1 d2 d2) ((disc d1) (clear d1) (on d1 d1) (smaller d1 d2) (clear d2)) ((on d1 d1) (clear d2)) ((on d1 d2) (clear d1)))
          ((move d1 d1 d2 p1) ((disc d1) (clear d1) (on d1 d1) (smaller d1 d2) (clear d2)) ((on d1 d1) (clear d2)) ((on d1 d2) (clear d1)))
          ((move d1 d1 d2 p2) ((disc d1) (clear d1) (on d1 d1) (smaller d1 d2) (clear d2)) ((on d1 d1) (clear d2)) ((on d1 d2) (clear d1)))
          ((move d1 d1 d2 p3) ((disc d1) (clear d1) (on d1 d1) (smaller d1 d2) (clear d2)) ((on d1 d1) (clear d2)) ((on d1 d2) (clear d1)))
          ((move d1 p3 d2 d1) ((disc d1) (clear d1) (on d1 p3) (smaller d1 d2) (clear d2)) ((on d1 p3) (clear d2)) ((on d1 d2) (clear p3)))
          ((move d1 p3 d2 d2) ((disc d1) (clear d1) (on d1 p3) (smaller d1 d2) (clear d2)) ((on d1 p3) (clear d2)) ((on d1 d2) (clear p3)))
          ((move d1 p3 d2 p1) ((disc d1) (clear d1) (on d1 p3) (smaller d1 d2) (clear d2)) ((on d1 p3) (clear d2)) ((on d1 d2) (clear p3)))
          ((move d1 p3 d2 p2) ((disc d1) (clear d1) (on d1 p3) (smaller d1 d2) (clear d2)) ((on d1 p3) (clear d2)) ((on d1 d2) (clear p3)))
          ((move d1 p3 d2 p3) ((disc d1) (clear d1) (on d1 p3) (smaller d1 d2) (clear d2)) ((on d1 p3) (clear d2)) ((on d1 d2) (clear p3)))))
    (display "passed") (display "failed"))
(newline)
(display "Test op instantiation2 ")
(if (== (opFullInstance (opFindResult '(on d1 d2) HanoiOps) HanoiGoal (worldObjects HanoiState HanoiGoal))
        '(((move d1 p1 d2) ((disc d1) (clear d1) (on d1 p1) (smaller d1 d2) (clear d2)) ((on d1 p1) (clear d2)) ((on d1 d2) (clear p1)))
          ((move d1 d1 d2) ((disc d1) (clear d1) (on d1 d1) (smaller d1 d2) (clear d2)) ((on d1 d1) (clear d2)) ((on d1 d2) (clear d1)))
          ((move d1 p3 d2) ((disc d1) (clear d1) (on d1 p3) (smaller d1 d2) (clear d2)) ((on d1 p3) (clear d2)) ((on d1 d2) (clear p3)))))
    (display "passed") (display "failed"))
(newline)
