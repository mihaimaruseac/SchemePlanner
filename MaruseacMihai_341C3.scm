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
(define (listCompare l1 l2) (if (null? l1) #t (if (= (car l1) (car l2)) (listCompare (cdr l1) (cdr l2)) (< (car l1) (car l2)))))

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

; Interesction
(define (^ l1 l2) (filter (lambda (x) (elem? x l2)) l1))

; Cartesian products and multiple-list applications
(define (cAp2 f x l2) (map f (repeat x (length l2)) l2))
(define (cAp f l1 l2) (if (null? l1) '() (append (cAp2 f (car l1) l2) (cAp f (cdr l1) l2))))
(define (**2 l1 l2) (cAp (lambda (x y) (if (list? y) (cons x y) (cons x (list y)))) l1 l2))
(define (** l) (if (< (length l) 2) '() (if (= (length l) 2) (**2 (car l) (cadr l)) (**2 (car l) (** (cdr l))))))

; Set predicates
(define (elem? x l) (if (null? l) #f (if (equal? x (car l)) #t (elem? x (cdr l)))))
(define (in? l1 l2) (andList (map (lambda (x) (elem? x l2)) l1)))
(define (== l1 l2) (and (in? l1 l2) (in? l2 l1)))

; Not null (stupid syntax for filter)
(define (notnull? l) (not (null? l)))

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

(define (opFindDelAdd del add opList)
  (if (null? opList) '()
      (let*
          (
           (op (car opList))
           (opDelPredNames (map predName (opDel op)))
           (opAddPredNames (map predName (opAdd op)))
           (delPredNames (map predName del))
           (addPredNames (map predName add))
           (relevant? (not (or (null? (^ delPredNames opDelPredNames)) (null? (^ addPredNames opAddPredNames)))))
           )
        (if relevant?
            (let*
                (
                 (opRelevantDelSet (filter (lambda (p) (elem? (predName p) delPredNames)) (opDel op)))
                 (relevantDelSet (filter (lambda (p) (elem? (predName p) opDelPredNames)) del))
                 (opsFromDel (getAllInstantiationsDel (car relevantDelSet) op))
                 )
              (+++ opsFromDel (opFindDelAdd del add (cdr opList)))
              )
            (opFindDelAdd del add (cdr opList))
            )
        )
      )
  )

(define (opFullInstance ops goal world) (opFullWorld world (opFullGoal goal ops)))
(define (opExists? pred opList) (if (null? (opFindResult pred opList)) #f #t))

(define (opObtainable? op init opList)
  (let*
      (
       (needSet (opPred op))
       (notGiven (-- needSet init))
       )
    (andList (map (lambda (x) (opExists? x opList)) notGiven))
    )
  )

(define (opValid? op)
  (let*
      (
       (needSet (opPred op))
       (addSet (opAdd op))
       (delSet (opDel op))
       (disjunctAddDel? (null? (^ addSet delSet)))
       (unknownDel? (null? (-- delSet needSet)))
       )
    (and disjunctAddDel? unknownDel?)
    )
  )

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

(define (getAllInstantiationsDel pred op)
  (let*
      (
       (results (opDel op))
       (pName (predName pred))
       (relevantResults (filter (lambda (p) (equal? pName (predName p))) results))
       (relevantBindings (map (lambda (R) (unify (predArgs pred) (predArgs R))) relevantResults))
       (obtainedOps (map (lambda (b) (opInstance op b)) relevantBindings))
       )
    obtainedOps
    )
  )

(define (opFullGoal goal l) (apply +++ (map (lambda (x) (opFullInstancesGoal x goal)) l)))

(define (opFullInstancesGoal op goal)
  (if (opInstantiated? op) (list op)
      (let
          (
           (firstUnInstPred (head (filter (lambda (p) (not (predInstantiated? p))) (opAdd op))))
           )
        (if (null? firstUnInstPred) (list op)
            (let*
                (
                 (fUIPName (predName firstUnInstPred))
                 (instancesInGoal (filter (lambda (p) (equal? (predName p) fUIPName)) goal))
                 (relevantBindings (map (lambda (R) (unify (predArgs R) (predArgs firstUnInstPred))) instancesInGoal))
                 (results (map (lambda (b) (opInstance op b)) relevantBindings))
                 )
              (if (null? instancesInGoal) (list op)
                  (apply ++ (map (lambda (o) (opFullInstancesGoal o goal)) results))
                  ))))
      )
  )

(define (opFullWorld world l) (filter opValid? (apply +++ (map (lambda (x) (opFullInstancesWorld x world)) l))))

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
(define (andExpand n opList init world) (apply +++ (map (lambda(x) (andExpandOPR x opList n init world)) n)))

(define (andExpandOPR n opList goal init world)
  (let*
      (
       (ornode (cons desEmpty (list n)))
       (expansion (orExpand ornode opList goal init world))
       )
    expansion
    )
  )

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
(define (orExpand n opList goal init worldObjects)
  (let*
      (
       (ops (opFullInstance (opFindResult (orPred n) opList) goal worldObjects))
       (goodOps (filter (lambda (x) (opObtainable? x init opList)) ops))
       (l (length goodOps))
       )
    (map (lambda (o) (makeOPR o goal init opList l)) goodOps)
    )
  )

(define (makeOPR op goal init opList l)
  (let*
      (
       (killSet (^ (opDel op) goal))
       (kv (length killSet))
       (genSet (^ (opAdd op) goal))
       (gv (length genSet))
       (needSet (opPred op))
       (inGoal (^ needSet goal))
       (czv (length inGoal))
       (given (^ needSet init))
       (ifcv (length given))
       )
    (cons (list l kv gv czv ifcv) (list op))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  DESIRABILITY AUXILIARY FUNCS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; record accessors
(define (desOp d) (car d))
(define (desKill d) (cadr d))
(define (desGen d) (caddr d))
(define (desCz d) (cadddr d))
(define (desIFc d) (caddddr d))

; setters
(define (desSetOp d v) (++ (take 0 d) (list v) (drop 1 d)))
(define (desSetKill d v) (++ (take 1 d) (list v) (drop 2 d)))
(define (desSetGen d v) (++ (take 2 d) (list v) (drop 3 d)))
(define (desSetCz d v) (++ (take 3 d) (list v) (drop 4 d)))
(define (desSetIFc d v) (++ (take 4 d) (list v) (drop 5 d)))
(define (desSetORLevel d opv) (desSetOp d opv))
(define (desSetOPRLevel d killv genv) (desSetKill (desSetGen d genv) killv))
(define (desSetANDLevel d czv ifcv) (desSetCz (desSetIFc d ifcv) czv))
(define (desSetOPRANDLevel d killv genv czv ifcv) (desSetANDLevel (desSetOPRLevel d killv genv) czv ifcv))

; construct empty slot
(define desEmpty (list UN UN UN UN UN))

; get heuristic value / compare
(define (desEval d) OO)
(define (desSort d1 d2)
  (let*
      (
       (dO1 (desOp d1))
       (dK1 (desKill d1))
       (dG1 (desGen d1))
       (dC1 (desCz d1))
       (dI1 (desIFc d1))
       (dO2 (desOp d2))
       (dK2 (desKill d2))
       (dG2 (desGen d2))
       (dC2 (desCz d2))
       (dI2 (desIFc d2))
       )
    (listCompare (list dO1 dC1 dI2) (list dO2 dC2 dI1))
    )
  )

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
(define (solve opList init scope) (solveTF opList init scope #t))

(define (solveTF opList init scope tryAgain?)
  (if (null? (-- scope init))
      '() ; no plan if all is given
      (let
          (
           (return (solveGoal scope opList init (worldObjects init scope)))
           )
        (if (null? return)
            '() ; no plan if goal impossible to achieve
            (let
                (
                 (oplist (car return))
                 (state (cadr return))
                 )
              (display "MAIN:\n")(display scope)(newline)
              (display oplist)(newline)
              (display state)
              (display "\nSOLUTION:")
              (if tryAgain?
                  (append oplist (solveTF opList state (-- scope state) #f))
                  oplist
                  )
              )
            )
        )
      )
  )

; return list of operators needed to solve a goal paired with the new state
(define (solveGoal g opList given world)
  (newline)(newline)
  (display "solveGoal called with ")(newline)
  (display "g:")(display g)(newline)
  (display "given:")(display given)(newline)
  (newline)(newline)
  (let*
      (
       (ng (-- g given))
       (exp (andExpand ng opList given world))
       (sortedExp (sort exp altSort))
       (result (tryExpansion sortedExp opList ng given world))
       (expansionSuccessful? (car result))
       )
    (display ">>>>>>>>>>>>>\n")(display result)(display "<<<<<<<<<<\n")
    (if expansionSuccessful?
        ; if we have a result, check if we have more subgoals
        (let*
            (
             (returnedData (cdr result))
             (oplist (car returnedData))
             (newState (cadr returnedData))
             (stillToSolve (-- g newState))
             )
          (display "sTS")(display stillToSolve)(newline)
          (if (null? stillToSolve)
              ; if completely solved, return result
              (cdr result)
              ; else, search again, new goal, other state
              (let*
                  (
                   (nextResult (solveGoal stillToSolve opList newState world))
                   (ret_oplist (car nextResult))
                   (ret_newState (cadr nextResult))
                   (now_op (car returnedData))
                   )
                (display"\n.......................\n")
                (display nextResult)(newline)
                (display ret_oplist)(newline)
                (display ret_newState)(newline)
                (display now_op)(newline)
                (display"\n.......................\n")
                (list (++ now_op ret_oplist) ret_newState)
                )
              )
          )
        '() ; return empty list if failed to solve
        )
    )
  )

; return list (#t/#f oplist new_state)
(define (tryExpansion alternatives opList g given world)
  (newline)(newline)
  (display "tryExpansion called with ")(newline)
  (display "alternatives:")(display alternatives)(newline)
  (display "given:")(display given)(newline)
  (newline)(newline)
  (if (null? alternatives)
      (list #f '() '())
      (let*
          (
           (best (car alternatives))
           (op (oprOp best))
           (preCond (opPred op))
           (Add (opAdd op))
           (stillToProve (-- preCond given))
           )
        (display stillToProve)(display "<---- stillToProve\n")
        (if (null? stillToProve)
            ; if successful, return (#t (list op) newstate)
            (list #t (list (car op)) (opApply op given))
            ; if unknown, try to expand one more level
            (let
                (
                 (nextLevel (solveGoal stillToProve opList given world))
                 )
              (if (null? nextLevel)
                  (if (null? (cdr alternatives))
                      (list #f '() '())
                      (tryExpansion (cdr alternatives) opList g given world)
                      )
                  (let
                      (
                       (okToChain? (opApplicable? op (cadr nextLevel)))
                       )
                    (display"\n@@@@@@@@@@@@@@@@@@@\n")
                    (display op)(newline)
                    (display (list #t (++ (car nextLevel) (list (car op))) (opApply op (cadr nextLevel))))
                    (display okToChain?)
                    (display"\n@@@@@@@@@@@@@@@@@@@\n")
                    (if okToChain?
                        (list #t (++ (car nextLevel) (list (car op))) (opApply op (cadr nextLevel)))
                        (let*
                            (
                             (meetup (meetBetween (opPred op) (cadr nextLevel) opList world))
                             (state (cadr meetup))
                             (meetOps (map car (car meetup)))
                             )
                          (display "><")(display meetup)(newline)
                          (display "S")(display state)(newline)
                          (display "O")(display meetOps)(newline)
                          (list #t (++ (car nextLevel) meetOps (list (car op))) (opApply op state))
                          )
                        )
                    )
                  )
              )
            )
        )
      )
  )

; returns (opListForMeet newState)
(define (meetBetween goal current opList world)
  (if (null? (-- goal current)) (list '() current)
      (let*
          (
           (stillToRemove (-- current goal))
           (needToAchieve (-- goal current))
           (ops (opFindDelAdd stillToRemove needToAchieve opList))
           (fulls (opFullWorld world ops))
           (oks (filter (lambda (o) (opApplicable? o current)) fulls))
           (values (map (lambda (o) (cons (length (^ goal (opDel o))) (list o))) oks))
           (svalues (sort values (lambda (v1 v2) (< (car v1) (car v2)))))
           (bestOp (cadr (car svalues)))
           (result (opApply bestOp current))
           (nextLevel (meetBetween goal result opList world))
           )
        (list (cons bestOp (car nextLevel)) (cadr nextLevel))
        )
      )
  )

(define (altSort a1 a2) (desSort (oprDes a1) (oprDes a2)))

; get world objects
(define (worldObjects init scopes) (apply +++ (+++ (map predArgs init) (map predArgs scopes))))

; testing Blocks world problem
(define BWOps '((
                 (pickup X)
                 ((ontable X) (clear X) (armempty))
                 ((ontable X) (clear X) (armempty))
                 ((hold X))
                 ) 
                (
                 (putdown X) 
                 ((hold X))
                 ((hold X)) 
                 ((ontable X) (clear X) (armempty))
                 ) 
                (
                 (unstack X Y) 
                 ((on X Y) (clear X) (armempty))
                 ((on X Y) (clear X) (armempty))
                 ((hold X) (clear Y))
                 ) 
                (
                 (stack X Y) 
                 ((hold X) (clear Y)) 
                 ((hold X) (clear Y)) 
                 ((on X Y) (clear X) (armempty))
                 )))

(define BWState '((ontable a) (on b a) (on c b) (clear c) (armempty)))
(define BWState1 '((ontable a) (on c a) (ontable b) (clear c) (clear b) (armempty)))
(define BWState2 '((ontable a1) (on a2 a1) (on a3 a2) (on a4 a3) (on a5 a4) (on a6 a5) (on a7 a6) (on a8 a7) (clear a8) (armempty)))

(define BWGoal '((clear c) (ontable b) (on c b) (armempty)))
(define BWGoal1 '((ontable c) (on b c) (on a b) (clear a) (armempty)))
(define BWGoal2 '((ontable a8) (on a7 a8) (on a6 a7) (on a5 a6) (on a4 a5) (on a3 a4) (on a2 a3) (on a1 a2) (clear a1) (armempty)))

(define BWWorld (worldObjects BWState BWGoal))

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
(define HanoiGoal1 '((clear d2) (on d1 p3) (on d2 p2)))
(define HanoiGoal2 '((on d1 p3) (on d1 p2)))

(define HanoiWorld (worldObjects HanoiState HanoiGoal))

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

; DBG TESTS
(display ">>>> tests for opFindResult:")
(display "\nHanoi: ")(display (== (opFindResult '(clear d1) HanoiOps) '(((move A d1 C) ((disc A) (clear A) (on A d1) (smaller A C) (clear C)) ((on A d1) (clear C)) ((on A C) (clear d1))))))
(display "\nBW: ")(display (== (opFindResult '(clear c) BWOps) '(((putdown c) ((hold c)) ((hold c)) ((ontable c) (clear c) (armempty)))
                                                                 ((unstack X c) ((on X c) (clear X) (armempty)) ((on X c) (clear X) (armempty)) ((hold X) (clear c)))
                                                                 ((stack c Y) ((hold c) (clear Y)) ((hold c) (clear Y)) ((on c Y) (clear c) (armempty))))))
(newline)

(display ">>>> tests for opFullGoal:")
(display "\nHanoi partial: ")(display (== (opFullGoal '((clear d1)) (opFindResult '(clear d1) HanoiOps)) '(((move A d1 C) ((disc A) (clear A) (on A d1) (smaller A C) (clear C)) ((on A d1) (clear C)) ((on A C) (clear d1))))))
(display "\nHanoi total: ")(display (== (opFullGoal '((on d1 p3) (clear d1)) (opFindResult '(clear d1) HanoiOps)) '(((move d1 d1 p3) ((disc d1) (clear d1) (on d1 d1) (smaller d1 p3) (clear p3)) ((on d1 d1) (clear p3)) ((on d1 p3) (clear d1))))))
(display "\nBW partial: ")(display (== (opFullGoal '((clear a)) (opFindResult '(clear a) BWOps)) '(((putdown a) ((hold a)) ((hold a)) ((ontable a) (clear a) (armempty)))
                                                                                                   ((unstack X a) ((on X a) (clear X) (armempty)) ((on X a) (clear X) (armempty)) ((hold X) (clear a)))
                                                                                                   ((stack a Y) ((hold a) (clear Y)) ((hold a) (clear Y)) ((on a Y) (clear a) (armempty))))))
(display "\nBW total: ")(display (== (opFullGoal '((clear a) (on a b)) (opFindResult '(clear a) BWOps)) '(((putdown a) ((hold a)) ((hold a)) ((ontable a) (clear a) (armempty)))
                                                                                                          ((unstack X a) ((on X a) (clear X) (armempty)) ((on X a) (clear X) (armempty)) ((hold X) (clear a)))
                                                                                                          ((stack a b) ((hold a) (clear b)) ((hold a) (clear b)) ((on a b) (clear a) (armempty))))))
(newline)

(display ">>>> tests for opFullWorld:")
(display "\nHanoi 1: ")(display (== (opFullWorld HanoiWorld (opFullGoal '((clear d1)) (opFindResult '(clear d1) HanoiOps)))
                                    '(((move d1 d1 d2) ((disc d1) (clear d1) (on d1 d1) (smaller d1 d2) (clear d2)) ((on d1 d1) (clear d2)) ((on d1 d2) (clear d1)))
                                      ((move d1 d1 p1) ((disc d1) (clear d1) (on d1 d1) (smaller d1 p1) (clear p1)) ((on d1 d1) (clear p1)) ((on d1 p1) (clear d1)))
                                      ((move d1 d1 p2) ((disc d1) (clear d1) (on d1 d1) (smaller d1 p2) (clear p2)) ((on d1 d1) (clear p2)) ((on d1 p2) (clear d1)))
                                      ((move d1 d1 p3) ((disc d1) (clear d1) (on d1 d1) (smaller d1 p3) (clear p3)) ((on d1 d1) (clear p3)) ((on d1 p3) (clear d1)))
                                      ((move d2 d1 d2) ((disc d2) (clear d2) (on d2 d1) (smaller d2 d2) (clear d2)) ((on d2 d1) (clear d2)) ((on d2 d2) (clear d1)))
                                      ((move d2 d1 p1) ((disc d2) (clear d2) (on d2 d1) (smaller d2 p1) (clear p1)) ((on d2 d1) (clear p1)) ((on d2 p1) (clear d1)))
                                      ((move d2 d1 p2) ((disc d2) (clear d2) (on d2 d1) (smaller d2 p2) (clear p2)) ((on d2 d1) (clear p2)) ((on d2 p2) (clear d1)))
                                      ((move d2 d1 p3) ((disc d2) (clear d2) (on d2 d1) (smaller d2 p3) (clear p3)) ((on d2 d1) (clear p3)) ((on d2 p3) (clear d1)))
                                      ((move p1 d1 d2) ((disc p1) (clear p1) (on p1 d1) (smaller p1 d2) (clear d2)) ((on p1 d1) (clear d2)) ((on p1 d2) (clear d1)))
                                      ((move p1 d1 p1) ((disc p1) (clear p1) (on p1 d1) (smaller p1 p1) (clear p1)) ((on p1 d1) (clear p1)) ((on p1 p1) (clear d1)))
                                      ((move p1 d1 p2) ((disc p1) (clear p1) (on p1 d1) (smaller p1 p2) (clear p2)) ((on p1 d1) (clear p2)) ((on p1 p2) (clear d1)))
                                      ((move p1 d1 p3) ((disc p1) (clear p1) (on p1 d1) (smaller p1 p3) (clear p3)) ((on p1 d1) (clear p3)) ((on p1 p3) (clear d1)))
                                      ((move p2 d1 d2) ((disc p2) (clear p2) (on p2 d1) (smaller p2 d2) (clear d2)) ((on p2 d1) (clear d2)) ((on p2 d2) (clear d1)))
                                      ((move p2 d1 p1) ((disc p2) (clear p2) (on p2 d1) (smaller p2 p1) (clear p1)) ((on p2 d1) (clear p1)) ((on p2 p1) (clear d1)))
                                      ((move p2 d1 p2) ((disc p2) (clear p2) (on p2 d1) (smaller p2 p2) (clear p2)) ((on p2 d1) (clear p2)) ((on p2 p2) (clear d1)))
                                      ((move p2 d1 p3) ((disc p2) (clear p2) (on p2 d1) (smaller p2 p3) (clear p3)) ((on p2 d1) (clear p3)) ((on p2 p3) (clear d1)))
                                      ((move p3 d1 d2) ((disc p3) (clear p3) (on p3 d1) (smaller p3 d2) (clear d2)) ((on p3 d1) (clear d2)) ((on p3 d2) (clear d1)))
                                      ((move p3 d1 p1) ((disc p3) (clear p3) (on p3 d1) (smaller p3 p1) (clear p1)) ((on p3 d1) (clear p1)) ((on p3 p1) (clear d1)))
                                      ((move p3 d1 p2) ((disc p3) (clear p3) (on p3 d1) (smaller p3 p2) (clear p2)) ((on p3 d1) (clear p2)) ((on p3 p2) (clear d1)))
                                      ((move p3 d1 p3) ((disc p3) (clear p3) (on p3 d1) (smaller p3 p3) (clear p3)) ((on p3 d1) (clear p3)) ((on p3 p3) (clear d1))))))
(display "\nHanoi 2: ")(display (== (opFullWorld HanoiWorld (opFullGoal '((on d1 p3) (clear d1)) (opFindResult '(clear d1) HanoiOps)))
                                    '(((move d1 d1 p3) ((disc d1) (clear d1) (on d1 d1) (smaller d1 p3) (clear p3)) ((on d1 d1) (clear p3)) ((on d1 p3) (clear d1))))))
(display "\nBW 1: ")(display (== (opFullWorld BWWorld (opFullGoal '((clear a)) (opFindResult '(clear a) BWOps)))
                                 '(((putdown a) ((hold a)) ((hold a)) ((ontable a) (clear a) (armempty)))
                                   ((unstack b a) ((on b a) (clear b) (armempty)) ((on b a) (clear b) (armempty)) ((hold b) (clear a)))
                                   ((unstack c a) ((on c a) (clear c) (armempty)) ((on c a) (clear c) (armempty)) ((hold c) (clear a)))
                                   ((stack a b) ((hold a) (clear b)) ((hold a) (clear b)) ((on a b) (clear a) (armempty)))
                                   ((stack a c) ((hold a) (clear c)) ((hold a) (clear c)) ((on a c) (clear a) (armempty))))))
(display "\nBW 2: ")(display (== (opFullWorld BWWorld (opFullGoal '((clear a) (on a b)) (opFindResult '(clear a) BWOps)))
                                 '(((putdown a) ((hold a)) ((hold a)) ((ontable a) (clear a) (armempty)))
                                   ((unstack b a) ((on b a) (clear b) (armempty)) ((on b a) (clear b) (armempty)) ((hold b) (clear a)))
                                   ((unstack c a) ((on c a) (clear c) (armempty)) ((on c a) (clear c) (armempty)) ((hold c) (clear a)))
                                   ((stack a b) ((hold a) (clear b)) ((hold a) (clear b)) ((on a b) (clear a) (armempty))))))
(newline)
; END
