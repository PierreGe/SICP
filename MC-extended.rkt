#lang r6rs

;-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-
;-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-
;-*-*                                                                 *-*-
;-*-*         Extended version with transfer and new-process          *-*-
;-*-*                       Pierre Gerard  (ULB)                      *-*-
;-*-*                                                                 *-*-
;-*-*                        Original work :                          *-*-
;-*-*                      The SICP-MC-Eval (cnt)                     *-*-
;-*-*                        Wolfgang De Meuter                       *-*-
;-*-*                      Adaptation of Amb-Eval                     *-*-
;-*-*              H. Abelson, G.J. Sussman, J. Sussman               *-*-
;-*-*                           MIT-Press                             *-*-
;-*-*                                                                 *-*-
;-*-*                   2010 Software Languages Lab                   *-*-
;-*-*                    Vrije Universiteit Brussel                   *-*-
;-*-*                                                                 *-*-
;-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-
;-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-

;;; The implementation is supposed to show the same behavior as the one in class (chap4)
;;; Tested with the following example (same result as chap4)

; > (define p1 (new-process (lambda (input) (+ 1 1) (newline) (display "input : ") (display input) input )))
; > (define p2 (new-process (lambda (input) (+ 1 1) (newline) (display "input : ") (display input) input )))
; > (define p3 (new-process (lambda (input) (+ 1 1) (newline) (display "input : ") (display input) input )))
; > (transfer p1 0)
; 3
; > (transfer p2 100)
; 100 
; > (transfer p3 1000)
; 1000

;; Known drawback with following example (but quite similar at what is found in chap 4)
;> (define p1 (new-process (lambda (input) (+ 1 1) (set! input (transfer p2 (+ input 1))) (set! input (+ input 7)) input )))
;> (define p2 (new-process (lambda (input) (+ 1 1) (set! input (transfer p3 (+ input 1))) (set! input (+ input 11)) input )))
;> (define p3 (new-process (lambda (input) (+ 1 1) (set! input (transfer p1 (+ input 1))) (set! input (+ input 23)) input )))
;> (transfer p1 0)
;10
;> (transfer p2 100)
;118 
;> (transfer p3 1000)
;1041
;> (transfer p3 1000)
;1000  >>> At that point the implementation from chapter 4 returns 1041
;> (transfer p3 1000)
;1000
;> (transfer p3 1000)
;1000

;; Bonus transfer can accept multiple args
;> (define p1 (new-process (lambda (input input2) (+ 1 1) (set! input (transfer p2 (+ input 1) input2)) (set! input (+ input 7)) (+ input input2) )))
;> (define p2 (new-process (lambda (input input2) (+ 1 1) (set! input (transfer p3 (+ input 1) input2)) (set! input (+ input 11)) input )))
;> (define p3 (new-process (lambda (input input2) (+ 1 1) (set! input (transfer p1 (+ input 1) input2)) (set! input (+ input 23)) input )))
;> (transfer p1 0 5000)
; 5010

(library 
  (mc-eval)
  (export driver-loop)
  (import (rename (rnrs base) (apply apply-in-underlying-scheme))
          (rnrs lists)
          (rnrs mutable-pairs)
          (rnrs programs (6)) ;; for (exit) procedure
          (rnrs base (6)) ;; for mutable pairs
          (rnrs io simple))
  
  (define (true? x)
    (not (eq? x #f)))
  (define (false? x)
    (eq? x #f))
  
  (define (self-evaluating? exp)
    (cond ((number? exp) #t)
        ((string? exp) #t)
    (else #f)))
  
  (define (tagged-list? exp tag)
    (if (pair? exp)
        (eq? (car exp) tag)
        #f))
  
  (define (quoted? exp)
    (tagged-list? exp 'quote))
  
  (define (text-of-quotation exp) 
    (cadr exp))
  
  (define (variable? exp) 
    (symbol? exp))
  
  (define (assignment? exp)
    (tagged-list? exp 'set!))
  
  (define (assignment-variable exp) 
    (cadr exp))
  
  (define (assignment-value exp) 
    (caddr exp))
  
  (define (definition? exp)
    (tagged-list? exp 'define))
  
  (define (definition-variable exp)
    (if (symbol? (cadr exp))
        (cadr exp)
        (caadr exp)))
  
  (define (definition-value exp)
    (if (symbol? (cadr exp))
        (caddr exp)
        (make-lambda (cdadr exp)
                     (cddr exp))))
  
  (define (if? exp) 
    (tagged-list? exp 'if))
  
  (define (if-predicate exp) 
    (cadr exp))
  
  (define (if-consequent exp) 
    (caddr exp))
  
  (define (if-alternative exp)
    (if (not (null? (cdddr exp)))
        (cadddr exp)
        'false))
  
  (define (make-if predicate consequent alternative)
    (list 'if predicate consequent alternative))
  
  (define (lambda? exp) 
    (tagged-list? exp 'lambda))
  
  (define (lambda-parameters exp) 
    (cadr exp))

  (define (lambda-body exp) 
    (cddr exp))
  
  (define (make-lambda parameters body)
    (cons 'lambda (cons parameters body)))
  
  (define (cond? exp) 
    (tagged-list? exp 'cond))
  
  (define (cond-clauses exp) 
    (cdr exp))
  
  (define (cond-else-clause? clause)
    (eq? (cond-predicate clause) 'else))
  
  (define (cond-predicate clause) 
    (car clause))
  
  (define (cond-actions clause) 
    (cdr clause))
  
  (define (cond->if exp)
    (expand-clauses (cond-clauses exp)))
  
  (define (expand-clauses clauses)
    (if (null? clauses)
        'false
        (let ((first (car clauses))
              (rest (cdr clauses)))
          (if (cond-else-clause? first)
              (if (null? rest)
                  (sequence->exp (cond-actions first))
                  (error "ELSE clause isn't last -- COND->IF"
                         clauses))
              (make-if (cond-predicate first)
                       (sequence->exp (cond-actions first))
                       (expand-clauses rest))))))
  
  (define (begin? exp) 
    (tagged-list? exp 'begin))
  
  (define (begin-actions exp) 
    (cdr exp))
  
  (define (last-exp? seq) 
    (null? (cdr seq)))
  
  (define (first-exp seq) 
    (car seq))
  
  (define (rest-exps seq) 
    (cdr seq))
  
  (define (sequence->exp seq)
    (cond ((null? seq) seq)
          ((last-exp? seq) (first-exp seq))
          (else (make-begin seq))))
  
  (define (make-begin seq) 
    (cons 'begin seq))
  
  (define (application? exp) 
    (pair? exp))
  
  (define (operator exp) 
    (car exp))
  
  (define (operands exp) 
    (cdr exp))
  
  (define (no-operands? ops) 
    (null? ops))
  
  (define (first-operand ops) 
    (car ops))
  
  (define (rest-operands ops) 
    (cdr ops))
  
  ;; runtime representation of procedures
  
  (define (make-procedure parameters body env)
    (list 'procedure parameters body env))
  
  (define (compound-procedure? p)
    (tagged-list? p 'procedure))
  
  (define (procedure-parameters p) 
    (cadr p))
  
  (define (procedure-body p) 
    (caddr p))
  
  (define (procedure-environment p) 
    (cadddr p))
  
   ;; runtime representation of continuations
  
  (define (make-continuation cont)
    (list 'continuation cont))
  
  (define (continuation? c)
    (tagged-list? c 'continuation))
  
  (define (continuation-continuation p) 
    (cadr p))
 
  ;; representation of environments
 
  (define (enclosing-environment env) 
    (cdr env))
  
  (define (first-frame env) 
    (car env))
  
  (define the-empty-environment '())
  
  (define (extend-environment vars vals base-env)
    (if (= (length vars) (length vals))
        (cons (make-frame vars vals) base-env)
        (if (< (length vars) (length vals))
            (error "Too many arguments supplied" vars vals)
            (error "Too few arguments supplied" vars vals))))
  
  (define (make-frame variables values)
    (cons variables values))
  
  (define (frame-variables frame) 
    (car frame))

  (define (frame-values frame) 
    (cdr frame))
  
  (define (add-binding-to-frame! var val frame)
    (set-car! frame (cons var (car frame)))
    (set-cdr! frame (cons val (cdr frame))))
  
  (define (lookup-variable-value var env)
    (define (env-loop env)
      (define (scan vars vals)
        (cond ((null? vars)
               (env-loop (enclosing-environment env)))
              ((eq? var (car vars))
               (car vals))
              (else (scan (cdr vars) (cdr vals)))))
      (if (eq? env the-empty-environment)
          (error "Unbound variable" var)
          (let ((frame (first-frame env)))
            (scan (frame-variables frame)
                  (frame-values frame)))))
    (env-loop env))
  
  (define (set-variable-value! var val env)
    (define (env-loop env)
      (define (scan vars vals)
        (cond ((null? vars)
               (env-loop (enclosing-environment env)))
              ((eq? var (car vars))
               (set-car! vals val))
              (else (scan (cdr vars) (cdr vals)))))
      (if (eq? env the-empty-environment)
          (error "Unbound variable -- SET!" var)
          (let ((frame (first-frame env)))
            (scan (frame-variables frame)
                  (frame-values frame)))))
    (env-loop env))
  
  (define (define-variable! var val env)
    (let ((frame (first-frame env)))
      (define (scan vars vals)
        (cond ((null? vars)
               (add-binding-to-frame! var val frame))
              ((eq? var (car vars))
               (set-car! vals val))
              (else (scan (cdr vars) (cdr vals)))))
      (scan (frame-variables frame)
            (frame-values frame))))
  
  (define (setup-environment)
    (let ((initial-env
           (extend-environment (primitive-procedure-names)
                               (primitive-procedure-objects)
                               the-empty-environment)))
      (define-variable! 'true #t initial-env)
      (define-variable! 'false #f initial-env)
      initial-env))
  
  (define (primitive-procedure? proc)
    (tagged-list? proc 'primitive))
 
  (define (primitive-implementation proc) 
    (cadr proc))
  
  ;; CALL-CC => CREATE CONTINUATION OBJECT AND PASS IT TO THE 1-PARAMETER 
  
  (define (do-call-cc cont proc)
    ((procedure-body proc)
     (extend-environment (procedure-parameters proc)
                         (list (make-continuation cont)) ; a list of 1 parameter
                         (procedure-environment proc))
     cont))
  
  (define primitive-procedures
    ;; cc/ise-it remove the continutation from args
    (let ((cc/ise-it (lambda (p)    ; lift p
                       (lambda args ; to a function that ignores its first cont argument
                         (apply-in-underlying-scheme p (cdr args))))))
      (list (list 'car   (cc/ise-it car))
            (list 'cdr   (cc/ise-it cdr))
            (list 'cons  (cc/ise-it cons))
            (list 'null? (cc/ise-it null?))
            (list 'list  (cc/ise-it list))
            (list 'not   (cc/ise-it not))
            (list '+     (cc/ise-it +))
            (list '-     (cc/ise-it -))
            (list '*     (cc/ise-it *))
            (list '=     (cc/ise-it =))
            (list '>     (cc/ise-it >))
            (list '>=    (cc/ise-it >=))
            (list 'abs   (cc/ise-it abs))
            (list 'remainder (cc/ise-it mod))
            (list 'integer?  (cc/ise-it integer?))
            (list 'sqrt  (cc/ise-it sqrt))
            (list 'eq?   (cc/ise-it eq?))
            (list 'member    (cc/ise-it member))
            (list 'memq  (cc/ise-it memq))
            ;;      more primitives
            (list 'exit (cc/ise-it exit))
            (list 'display (cc/ise-it display))
            (list 'newline (cc/ise-it newline))
            ;; last but no least
            (list 'call/cc do-call-cc)

            )))
  
  (define (primitive-procedure-names)
    (map car
         primitive-procedures))
  
  (define (primitive-procedure-objects)
    (map (lambda (proc) (list 'primitive (cadr proc)))
        primitive-procedures))
  
  (define (apply-primitive-procedure proc args cont)
    (cont (apply-in-underlying-scheme
          (primitive-implementation proc) cont args)))
  
  (define input-prompt ";;; Cnt-Eval input:")
  (define output-prompt ";;; Cnt-Eval value:")
  
  (define (driver-loop)
    (prompt-for-input input-prompt)
    (let ((input (read)))
      (display input) ;; show input when cat insfile <pipe> mc
      (cnteval input the-global-environment
        (lambda (val)
          (announce-output output-prompt)
          (user-print val)
          (driver-loop)))))
  
  (define (prompt-for-input string)
    (newline) (newline) (display string) (newline))
  
  (define (announce-output string)
    (newline) (display string) (newline))
  
  (define (user-print object)
    (if (compound-procedure? object)
        (display (list 'compound-procedure
                       (procedure-parameters object)
                       (procedure-body object)
                       '<procedure-env>))
        (display object)))
  
  (define (amb? exp) 
    (tagged-list? exp 'amb))

  (define (amb-choices exp) 
    (cdr exp))
  
  (define (cnteval exp env cnt)
    ((analyze exp) env cnt))

  ;; addition ;; check for tagged list  corresponding to a new-process
  (define (new-process? exp)
    (tagged-list? exp 'new-process))

  ;; addition ;; check for tagged list  corresponding to a transfer
  (define (transfer? exp) 
    (tagged-list? exp 'transfer))


  ;; addition ;; make a tagged list associated with a process
  (define (make-process parameters get-body set-body env)
    (list 'process parameters get-body set-body env))

  ;; addition ;; get args of process from the process tagged list
  (define (process-args process)
    (cadr process)) 

  ;; addition ;; get get-body from the process tagged list
  (define (get-process-body process)
    (caddr process)) ;; get the 3rd element

  ;; addition ;; get set-bodys from the process tagged list
  (define (set-process-body process)
    (cadddr process)) ;; get the 4th element

  ;; addition ;; get the env from the process tagged list
  (define (process-env process)
    (cadr (cdddr process))) ;; get the 5th element


  ;; addition ;; get the procedure from (define p (new-process (procedure))
  (define (process-procedure exp) 
    (cadr exp))

  ;; addition ;; dispatcher call this method upon the tag new-process
  (define (analyze-new-process exp)
    (lambda (env cnt)
      ((analyze (process-procedure exp)) env ;; analyse the my-lambda in (define p (new-process my-lambda))
        (lambda (procedure) ;; the procedure from (new-process (procedure))
          (let ( (vars (procedure-parameters procedure))
              (bproc  (procedure-body procedure ))
              (envproc (procedure-environment procedure)))
              (cnt (make-process
                  vars
                  (lambda () bproc) ;; bproc 'getter'
                  (lambda (newbproc) (set! bproc newbproc)) ;; bproc 'setter'
                  envproc )))))))


  ;; addition ;; global var to store current process and continuation of the current process
  ;; storing continuation might be useless here
  (define *current-process* (cons 'undefined-process 'undefined-continuation))

  ;; addition ;; is there a process defined in list current-process
  (define (defined-process?)
    (not (eq? (car *current-process*) 'undefined-process)))

  ;; addition ;; is there a continuation defined in list current-process
  (define (defined-continuation?)
    (not (eq? (cdr *current-process*) 'undefined-continuation)))

  ;; addition ;; is there a process defined in list current-process
  (define (get-process-continuation)
    (cdr *current-process*))

  ;; addition ;; is there a continuation defined in list current-process
  (define (get-process-process)
    (car *current-process*))


  ;; addition ;; create a new body to be set to process ( a save to where we are )
  (define (new-bproc cntbis)
    (lambda (env cnt) 
      (lambda (args) ;; current value of args (eg. (3) for input in p1 p2 p3 series)
        (cntbis args)))) ;; arg is a list of operands to transfer

  ;;addition ;; execute the actual transfer
  (define (execute-transfer process args cnt)
    (let   ((bproc (get-process-body process)) ;; body of the process to be transfered to
        (env (extend-environment (process-args process) args (process-env process))) ;; env of the process to be transfered to
        (newbproc (new-bproc cnt ))) ;; update of body of old process (if necessary)
    (if (defined-process?) ;; if a co routine were running
      ((set-process-body (get-process-process) ) newbproc ))  ;; we update its state to newbproc aka the actual continuation
    (set-cdr! *current-process* cnt)  ;; we set the current coroutine ;; not used
    (set-car! *current-process* process)  ;; we set the current process
    (execute-application (make-continuation ((bproc) env cnt)) args cnt))) ;; we make a continuation from body and call the procedure new-bproc with args

  ;; addition ;; get p1 of exp (transfer p1 0)
  (define (transfer-operator exp)
    (cadr exp))
  
  ;; addition ;; get 0 of exp (transfer p1 0)
  (define (transfer-operands exp)
    (cddr exp))

  (define (printvar v)
    (newline)
    (display "var ::")
    (display v)
    (newline))

  ;; addition ;; dispatcher call this method upon the tag transfer
  (define (analyze-transfer exp)
    (let ((fproc (analyze (transfer-operator exp))) ;; lambda 
        (aprocs (map analyze (transfer-operands exp)))) ;; still a list of lambda at this point (or one lambda here)
    (lambda (env cnt)
      (printvar (transfer-operator exp))
      (fproc env
        (lambda (process) ;; the process to be transfered to
          (printvar process)
          (get-args aprocs
              env
              (lambda (args) ;; args of transfer
                (execute-transfer process args cnt) )))))))
  
  
  (define (analyze exp)
    (cond ((self-evaluating? exp) 
          (analyze-self-evaluating exp))
          ((quoted? exp) (analyze-quoted exp))
          ((variable? exp) (analyze-variable exp))
          ((assignment? exp) (analyze-assignment exp))
          ((definition? exp) (analyze-definition exp))
          ((if? exp) (analyze-if exp))
          ((lambda? exp) (analyze-lambda exp))
          ((begin? exp) (analyze-sequence (begin-actions exp)))
          ((cond? exp) (analyze (cond->if exp)))
          ((let? exp) (analyze (let->combination exp)))
          ;; addition ;; : transfer and new process
          ((new-process? exp) (analyze-new-process exp))
          ((transfer? exp) (analyze-transfer exp))
          ;; application
          ((application? exp) (analyze-application exp))
          (else
            (error "Unknown expression type -- ANALYZE" exp))))
  
  (define (analyze-self-evaluating exp)
    (lambda (env cnt)
      (cnt exp)))
  
  (define (analyze-quoted exp)
    (let ((qval (text-of-quotation exp)))
      (lambda (env cnt)
        (cnt qval))))
  
  (define (analyze-variable exp)
    (lambda (env cnt)
      (cnt (lookup-variable-value exp env))))
  
  (define (analyze-lambda exp)
    (let ((vars (lambda-parameters exp))
        (bproc (analyze-sequence (lambda-body exp))))
      (lambda (env cnt)
        (cnt (make-procedure vars bproc env)))))
 
  (define (analyze-if exp)
    (let ((pproc (analyze (if-predicate exp)))
          (cproc (analyze (if-consequent exp)))
          (aproc (analyze (if-alternative exp))))
      (lambda (env cnt)
        (pproc env
               (lambda (pred-value)
                 (if (true? pred-value)
                     (cproc env cnt)
                     (aproc env cnt)))))))
  
  (define (analyze-sequence exps)
    (define (sequentially a b)
      (lambda (env cnt)
        (a env
           (lambda (a-value)
             (b env cnt)))))
    (define (loop first-proc rest-procs)
      (if (null? rest-procs)
          first-proc
          (loop (sequentially first-proc (car rest-procs))
                (cdr rest-procs))))
    (let ((procs (map analyze exps)))
      (if (null? procs)
          (error "Empty sequence -- ANALYZE"))
      (loop (car procs) (cdr procs))))
  
  (define (analyze-definition exp)
    (let ((var (definition-variable exp))
          (vproc (analyze (definition-value exp))))
      (lambda (env cnt)
        (vproc env                        
               (lambda (val)
                 (define-variable! var val env)
                 (cnt 'ok))))))
  
  (define (analyze-assignment exp)
    (let ((var (assignment-variable exp))
          (vproc (analyze (assignment-value exp))))
      (lambda (env cnt)
        (vproc env
               (lambda (val)
                 (set-variable-value! var val env)
                 (cnt 'ok))))))
  
  (define (analyze-application exp)
    (let ((fproc (analyze (operator exp)))
          (aprocs (map analyze (operands exp))))
      (lambda (env cnt)
        (fproc env
          (lambda (proc)
            (get-args aprocs
              env
              (lambda (args)
                (execute-application
                proc args cnt))))))))
  
  (define (get-args aprocs env cnt)
    (if (null? aprocs) ;; if empty
        (cnt '())
        ((car aprocs) env 
            (lambda (arg)
              (get-args (cdr aprocs) ;; recursivly looks at args
                env
                (lambda (args)
                  (cnt (cons arg args))))))))
  
  ;; CALL-CC => CALL A PREVIOUSLY GRABBED CONTINUATION
  
  (define (execute-application proc args cnt)
    (cond ((primitive-procedure? proc)
           (apply-primitive-procedure proc args cnt))
          ((compound-procedure? proc)
           ((procedure-body proc)
            (extend-environment (procedure-parameters proc)
                                args
                                (procedure-environment proc))
            cnt))
          ((continuation? proc) ; ignore cnt => use the grabbed continuation
           ((continuation-continuation proc) (car args)))
          (else
           (error
            "Unknown procedure type -- EXECUTE-APPLICATION"
            proc))))
  
  (define (let? exp) (tagged-list? exp 'let))
  (define (let-bindings exp) (cadr exp))
  (define (let-body exp) (cddr exp))
  
  (define (let-var binding) (car binding))
  (define (let-val binding) (cadr binding))
  
  (define (make-combination operator operands)
    (cons operator operands))
  
  (define (let->combination exp)
    (let ((bindings (let-bindings exp)))
      (make-combination (make-lambda (map let-var bindings)
                                     (let-body exp))
                        (map let-val bindings))))
  
  (define the-global-environment (setup-environment))

  (driver-loop)) 




