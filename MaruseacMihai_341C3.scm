; Maruseac Mihai, 341C3

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; README
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;S-a implementat o căutare înapoi bazată pe o euristică proprie. În orice moment de timp se cunoaște un scop
;care trebuie evaluat precum și scopul inițial. Cunoașterea scopului inițial este utilă pentru alegerea
;euristică a operațiilor ce se vor executa.
;
;Scopul curent este împărțit în clauze și se încearcă expandarea fiecăreia, într-o manieră Best-First. Astfel,
;pentru fiecare clauză, se obține un set de operatori instanțiați ce o pot produce și lista acestor operatori
;va fi sortată ulterior pe baza unei euristici ce ia în calcul dimensiunea seturilor Add și Del din
;specificația operatorilor precum și numărul de predicate ce sunt adevărate în starea curentă sau care trebuie
;demonstrate. În plus, contează și numărul de operatori care pot satisface o anumită clauză din scopul curent.
;
;Sortând lista de operatori după acești cinci indicatori, se alege primul operator și se încearcă soluționarea
;scopului utilizând acest operator. În caz de eșec, se va încerca cu următorul, până ce lista de operatori va
;deveni vidă, caz în care se întoarce eșec.
;
;De fiecare dată când se încearcă soluționarea cu un operator se va genera un nou proces de search având drept
;scop curent (scopul inițial este vizibil în tot procesul de search) acele precondiții din operator care nu sunt
;încă demonstrate în starea curentă. Dacă asemenea precondiții nu există, se consideră că avem o etapă din plan și
;ne întoarcem din recursivitate, aplicând operatorii găsiți stării curente pentru a deduce starea la nivelul
;următor.
;
;Este posibil ca la un moment dat să se genereze un operator o1 pentru un subgoal necesar pentru alt operator o2
;dar care, aplicat asupra stării curente, va duce la o stare din care nu poate fi aplicat o2. În acest caz, se
;face o căutare înainte scurtă (maxim 3 noduri pe fiecare operator posibil), ghidată după scopul inițial și
;scopul curent, ignorând valorile din euristică (altfel s-ar ajunge la bucle). După restaurarea stării corecte,
;se aplică o2 și procedura continuă.
;
;Când se ajunge la nivelul inițial, se verifică dacă mai există scopuri nerezolvate și se mai încearcă, o singură
;dată, soluționarea lor. În caz de eșec, se întoarce eșec.
;
;Euristica aleasă nu este full-proof, existând încă cazuri în care se generează operatori redundanți.

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
      (let* ((op (car opList)) (opDelPredNames (map predName (opDel op))) (opAddPredNames (map predName (opAdd op)))
                               (delPredNames (map predName del)) (addPredNames (map predName add))
                               (relevant? (not (or (null? (^ delPredNames opDelPredNames)) (null? (^ addPredNames opAddPredNames))))))
        (if relevant?
            (let* ((opRelevantDelSet (filter (lambda (p) (elem? (predName p) delPredNames)) (opDel op)))
                   (relevantDelSet (filter (lambda (p) (elem? (predName p) opDelPredNames)) del))
                   (opsFromDel (getAllInstantiationsDel (car relevantDelSet) op)))
              (+++ opsFromDel (opFindDelAdd del add (cdr opList))))
            (opFindDelAdd del add (cdr opList))))))

(define (opFullInstance ops goal world) (opFullWorld world (opFullGoal goal ops)))
(define (opExists? pred opList) (if (null? (opFindResult pred opList)) #f #t))
(define (opObtainable? op init opList) (andList (map (lambda (x) (opExists? x opList)) (-- (opPred op) init))))
(define (opValid? op) (and (null? (^ (opAdd op) (opDel op))) (null? (-- (opDel op) (opPred op)))))

; applications
(define (opApply op state) (predList+ (predList- state (opDel op)) (opAdd op)))
(define (opApplicable? op state) (and (opInstantiated? op) (in? (opPred op) state)))

; instantiations and bindings
(define (opInstantiated? op) (not (orList (map variable? (opVars op)))))
(define (opInstance op bindings) (foldl opBindVarVal op bindings))

(define (opBindVarVal bind op)
  (let* ((oldName (opName op)) (oldVars (opVars op)) (bindName (car bind)) (bindValue (cdr bind)) (oldPred (opPred op)) (oldAdd (opAdd op))
                               (oldDel (opDel op)) (newVars (map (lambda (x) (substTerm x bindName bindValue)) oldVars))
                               (newPred (map (lambda (x) (predSubst x bindName bindValue)) oldPred))
                               (newAdd (map (lambda (x) (predSubst x bindName bindValue)) oldAdd))
                               (newDel (map (lambda (x) (predSubst x bindName bindValue)) oldDel)))
    (list (cons oldName newVars) newPred newDel newAdd)))

(define (getAllInstantiations pred op)
  (let* ((results (opAdd op)) (pName (predName pred))
                              (relevantResults (filter (lambda (p) (equal? pName (predName p))) results))
                              (relevantBindings (map (lambda (R) (unify (predArgs pred) (predArgs R))) relevantResults)))
    (map (lambda (b) (opInstance op b)) relevantBindings)))

(define (getAllInstantiationsDel pred op)
  (let* ((results (opDel op)) (pName (predName pred))
                              (relevantResults (filter (lambda (p) (equal? pName (predName p))) results))
                              (relevantBindings (map (lambda (R) (unify (predArgs pred) (predArgs R))) relevantResults)))
    (map (lambda (b) (opInstance op b)) relevantBindings)))

(define (opFullGoal goal l) (apply +++ (map (lambda (x) (opFullInstancesGoal x goal)) l)))

(define (opFullInstancesGoal op goal) 
  (if (opInstantiated? op) (list op)
      (let ((firstUnInstPred (head (filter (lambda (p) (not (predInstantiated? p))) (opAdd op)))))
        (if (null? firstUnInstPred) (list op) 
            (let* ((fUIPName (predName firstUnInstPred))
                   (instancesInGoal (filter (lambda (p) (equal? (predName p) fUIPName)) goal))
                   (relevantBindings (map (lambda (R) (unify (predArgs R) (predArgs firstUnInstPred))) instancesInGoal))
                   (results (map (lambda (b) (opInstance op b)) relevantBindings)))
              (if (null? instancesInGoal) (list op) (apply ++ (map (lambda (o) (opFullInstancesGoal o goal)) results))))))))

(define (opFullWorld world l) (filter opValid? (apply +++ (map (lambda (x) (opFullInstancesWorld x world)) l))))

; the following function should return quickly in a normal implementation
(define (opFullInstancesWorld op world) (if (opInstantiated? op) (list op) (map (lambda (b) (opInstance op b)) (getAllBindings (opVars op) world))))
(define (getAllBindings args world) (let ((lists (map (lambda (v) (if (variable? v) (map (lambda (x) (cons v x)) world) (list (cons v v)))) args))) (** lists)))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  ACTION AUXILIARY FUNCS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; record accessors
(define (actName act) (car act))
(define (actArgs act) (cdr act))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  AND NODE AUXILIARY FUNCS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Each AND node is a list of predicates - nothing to obtain
; expanding: create OR nodes with empty desirability slot
(define (andExpand n opList init world) (apply +++ (map (lambda(x) (andExpandOPR x opList n init world)) n)))
(define (andExpandOPR n opList goal init world) (orExpand (cons desEmpty (list n)) opList goal init world))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  OR NODE AUXILIARY FUNCS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; each OR node contains one predicate and one desirability slot
(define (orPred n) (cadr n))
(define (orDes n) (car n))

; expanding: create OPR nodes with empty desirability slot
(define (orExpand n opList goal init worldObjects)
  (let* ((ops (opFullInstance (opFindResult (orPred n) opList) goal worldObjects)) (goodOps (filter (lambda (x) (opObtainable? x init opList)) ops))
                                                                                   (l (length goodOps)))
    (map (lambda (o) (makeOPR o goal init opList l)) goodOps)))

(define (makeOPR op goal init opList l) (let* ((killSet (^ (opDel op) goal)) (kv (length killSet)) (genSet (^ (opAdd op) goal)) (gv (length genSet))
                                                                             (needSet (opPred op)) (inGoal (^ needSet goal)) (czv (length inGoal))
                                                                             (given (^ needSet init)) (ifcv (length given)))
                                          (cons (list l kv gv czv ifcv) (list op))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  OPR NODE AUXILIARY FUNCS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; record accessors
(define (oprOp opr) (cadr opr))
(define (oprDes opr) (car opr))

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
(define (desSort d1 d2) (let* ((dO1 (desOp d1)) (dK1 (desKill d1)) (dG1 (desGen d1)) (dC1 (desCz d1)) (dI1 (desIFc d1))
                                                (dO2 (desOp d2)) (dK2 (desKill d2)) (dG2 (desGen d2)) (dC2 (desCz d2)) (dI2 (desIFc d2)) )
                          (listCompare (list dO1 dC1 dI2) (list dO2 dC2 dI1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  IMPLEMENTATION FUNCTIONS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; main func - call the defined funcs
(define (solve opList init scope) (solveTF opList init scope #t))

(define (solveTF opList init scope tryAgain?)
  (if (null? (-- scope init)) '() ; no plan if all is given
      (let ((return (solveGoal scope scope opList init (worldObjects init scope))))
        (if (null? return) '() ; no plan if goal impossible to achieve
            (let ((oplist (car return)) (state (cadr return)))
              (if tryAgain? (append oplist (solveTF opList state (-- scope state) #f)) oplist))))))

; return list of operators needed to solve a goal paired with the new state
(define (solveGoal gg g opList given world)
  (let* ((ng (-- g given)) (exp (andExpand ng opList given world)) (sortedExp (sort exp altSort)) 
                           (result (tryExpansion sortedExp opList gg ng given world)) (expansionSuccessful? (car result)))
    (if expansionSuccessful?
        ; if we have a result, check if we have more subgoals
        (let* ( (returnedData (cdr result)) (oplist (car returnedData)) (newState (cadr returnedData)) (stillToSolve (-- ng newState)))
          (if (null? stillToSolve)
              ; if completely solved, return result
              (cdr result)
              ; else, search again, new goal, other state
              (let* ( (nextResult (solveGoal gg stillToSolve opList newState world)) (ret_oplist (car nextResult))
                                                                                     (ret_newState (cadr nextResult)) (now_op (car returnedData)))
                (list (++ now_op ret_oplist) ret_newState))))
        '() ; return empty list if failed to solve
        )))

; return list (#t/#f oplist new_state)
(define (tryExpansion alternatives opList gg g given world)
  (if (null? alternatives) (list #f '() '())
      (let* ((best (car alternatives)) (op (oprOp best)) (preCond (opPred op)) (Add (opAdd op)) (stillToProve (-- preCond given)))
        (if (null? stillToProve)
            ; if successful, return (#t (list op) newstate)
            (list #t (list (car op)) (opApply op given))
            ; if unknown, try to expand one more level
            (let ((nextLevel (solveGoal gg stillToProve opList given world)))
              (if (null? nextLevel) (if (null? (cdr alternatives)) (list #f '() '()) (tryExpansion (cdr alternatives) opList gg g given world))
                  (if (opApplicable? op (cadr nextLevel)) (list #t (++ (car nextLevel) (list (car op))) (opApply op (cadr nextLevel)))
                      (let* ((meetup (meetBetween gg (opPred op) (cadr nextLevel) opList world))
                             (state (cadr meetup)) (meetOps (map car (car meetup))))
                        (list #t (++ (car nextLevel) meetOps (list (car op))) (opApply op state))))))))))

; returns (opListForMeet newState)
(define (meetBetween gg goal current opList world)
  (if (null? (-- goal current)) (list '() current)
      (let*
          (
           (stillToRemove (-- current goal))
           (needToAchieve (-- goal current))
           (ops (opFindDelAdd stillToRemove needToAchieve opList))
           (fulls (opFullWorld world ops))
           (oks (filter (lambda (o) (opApplicable? o current)) fulls))
           (values (map (lambda (o) (cons (length (^ goal (opDel o))) (list o))) oks))
           (svalues (reorder (sort values (lambda (v1 v2) (< (car v1) (car v2)))) gg))
           (bestOp (cadr (car svalues)))
           (result (opApply bestOp current))
           (nextLevel (meetBetween gg goal result opList world))
           )
        (list (cons bestOp (car nextLevel)) (cadr nextLevel))
        )
      )
  )

(define (reorder l goal)
  (if (= 0 (caar l)) (sort (map (lambda (o) (cons (length (^ goal (opAdd o))) (list o)))
                                (map cadr (filter (lambda (o) (= 0 (car o))) l))) 
                           (lambda (v1 v2) (> (car v1) (car v2))))
      l))

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

(== (solve BWOps BWState2 BWGoal2) '((unstack a8 a7)
                                     (putdown a8)
                                     (unstack a7 a6)
                                     (stack a7 a8)
                                     (unstack a6 a5)
                                     (stack a6 a7)
                                     (unstack a5 a4)
                                     (stack a5 a6)
                                     (unstack a4 a3)
                                     (stack a4 a5)
                                     (unstack a3 a2)
                                     (stack a3 a4)
                                     (unstack a2 a1)
                                     (stack a2 a3)
                                     (pickup a1)
                                     (stack a1 a2)))
(== (solve BWOps BWState1 BWGoal1) '((unstack c a) (putdown c) (pickup a) (stack a b) (unstack a b) (putdown a) (pickup b) (stack b c) (pickup a) (stack a b)))
(== (solve BWOps BWState BWGoal) '((unstack c b) (putdown c) (unstack b a) (putdown b) (pickup c) (stack c b)))
(== (solve HanoiOps HanoiState HanoiGoal2) '((move d1 d2 p2) (move d1 p2 p3) (move d1 p3 p2)))
(== (solve HanoiOps HanoiState HanoiGoal1) '((move d1 d2 p3) (move d2 p1 p2)))
(== (solve HanoiOps HanoiState HanoiGoal) '((move d1 d2 p3) (move d2 p1 p2) (move d1 p3 d2)))