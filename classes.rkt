#lang racket

#| IREF: Uma Linguagem com Referências Implícitas

; Expressed values e Denoted values
ExpVal = Int + Bool + Proc
DenVal = Ref(ExpVal)
 
; Operações para locations e referências
  newref :: ExpVal -> Ref
  deref :: Ref -> ExpVal
  setref :: Ref x ExpVal -> ???

; Sintaxe

Prog -> (ClassDecl* Expr)

Prog -> (prog Expr)
Expr -> (lit Val) | (var Var) | (zero? Expr) | (dif Expr Expr)
     |  (if Expr Expr Expr) | (let Var Expr Expr)
     | (proc Var Expr) | (call Expr Expr)
     | (letrec Name Var Expr Expr)
     | (set Var Expr)
     | (begin Expr Expr*)
     |  

; Exemplo
1)
let g = let count = 0
        in proc(dummy)
            begin
             set count = -(count, -1));
             count
            end
in let a = (g 11)
   in let b = (g 11)
      in -(a,b)
_____________________________________________________
(let g (let count (lit 0)
        (proc dummy (begin (set count (dif (var count) (lit -1)))
                           (var count))))
 (let a (call (var g) (lit 11))
  (let b (call (var g) (lit 11))
   (dif (var a) (var b)))))


2)
let x = newref(newref(0))
in begin
    setref(deref(x), 11);
    deref(deref(x))
   end
______________________________________________________
Não tem equivalente em IREF


; Notação do Estado

σ => denota um estado (memória, ou store)
[l = v]σ => um estado que é igual a σ, exceto que no location l tem o valor v
σ(l) => valor no estado σ referenciado pelo location l

|#
; Representando um estado como um par: próximo endereço e um vetor
(define TAM 100) ; tamanho da memória
(define σ (cons 0 (make-vector TAM)))

;empty-store
(define (empty-store) (set! σ (cons 0 (cdr σ))))

;newref :: ExpVal -> Ref
(define (newref v)
  (define addr (car σ))
  (define mem (cdr σ))
  (vector-set! mem addr v)
  (set! σ (cons (add1 addr) mem))
  addr)

; deref :: Ref -> ExpVal
(define (deref addr)
  (if (< addr (car σ))
         (vector-ref (cdr σ) addr)
         (error "invalid location")))
; setref! :: Ref x ExpVal -> ?
(define (setref! addr v)
  (if (< addr (car σ))
      (vector-set! (cdr σ) addr v)
      (error "invalid location")))

#|
; Environment
Env = Var -> Value

empty-env :: Env
extend-env :: Var x Value x Env -> Env
apply-env :: Env x Var -> Value
    
; Notação
  Δ => Environment
  [] => empty-env
  [var=val]Δ => (extend-env var val Δ)
  [var1=val1, var2=val2]Δ => abreviação para [var1=val1]([var2=val2]Δ)
  [var1=val1, var2=val2, ..., varn=valn] => abreviação para [var1=val1,...,varn=valn][]
  Δ⟦var⟧  => (apply-env Δ var)

  |[name = var / body]Δ| = (extend-env-rec name var body Δ) 
|#
(define empty-env
  (lambda (var)
    (error "No bind")))

(define (extend-env var value env)
  (lambda (svar)
    (if (equal? svar var) value
        (apply-env env svar))))

(define (extend-env-rec name var body env)
  (lambda (svar)
    (if (equal? svar name)
        (newref (proc-val var body (extend-env-rec name var body env)))
        (apply-env env svar))))

(define (apply-env env var)
  (env var))

(define init-env empty-env)




#|



(define initialize-class-env!
(lambda (c-decls)
(set! the-class-env
(list
(list ’object (a-class #f ’() ’()))))
(for-each initialize-class-decl! c-decls)))


(define initialize-class-decl!
(lambda (c-decl)
(cases class-decl c-decl
(a-class-decl (c-name s-name f-names m-decls)
(let ((f-names
(append-field-names
(class->field-names (lookup-class s-name))
f-names)))
(add-to-class-env!
c-name
(a-class s-name f-names
(merge-method-envs
(class->method-env (lookup-class s-name))
(method-decls->method-env
m-decls s-name f-names)))))))))

|#

#|
; Definição dos Valores

(apply-proc (procedure var body Δ) val) = (value-of body [var=l]Δ [l=val]σ)


|#
; call-by-value
; proc-val :: Var x Expr x Env -> Proc
#;(define (proc-val var exp Δ)
  (lambda (val)
    (value-of exp (extend-env var (newref val) Δ))))

; apply-proc :: Proc x ExpVal -> ExpVal  
#;(define (apply-proc proc val)
  (proc val))


; call-by-reference
(define (proc-val var exp Δ)
  (lambda (val flag)
    (if flag (value-of exp (extend-env var (newref val) Δ))
        (value-of exp (extend-env var val Δ)))))

(define (apply-proc proc val)
  (proc val #t))

(define (apply-proc-ref proc val)
  (proc val #f))



(struct thunk (env exp))




(define (value-of exp Δ)
  (define type (car exp))

  (cond [(equal? type 'lit) (cadr exp)]
        ; call-by-value e call-by-reference
        ;[(equal? type 'var) (deref (apply-env Δ (cadr exp)))]
        ; call-by-name
        [(equal? type 'var) (define v (cadr exp))
                            (if (thunk? v) (value-of (thunk-exp v) (thunk-env v))
                                (deref (apply-env Δ v)))]
        [(equal? type 'dif) (- (value-of (cadr exp) Δ) (value-of (caddr exp) Δ))]
        [(equal? type 'zero?) (= (value-of (cadr exp) Δ) 0)]
        [(equal? type 'let) (value-of (cadddr exp) (extend-env (cadr exp) (newref (value-of (caddr exp) Δ)) Δ))]
        [(equal? type 'if) (if (value-of (cadr exp) Δ)
                               (value-of (caddr exp) Δ) (value-of (cadddr exp) Δ))]
        [(equal? type 'proc) (proc-val (cadr exp) (caddr exp) Δ)]
        ; call-by-value
        ;[(equal? type 'call) (apply-proc (value-of (cadr exp) Δ) (value-of (caddr exp) Δ))]
        ; call-by-reference
        #;[(equal? type 'call) (if (equal? (car (caddr exp)) 'var)
                                 (apply-proc-ref (value-of (cadr exp) Δ) (apply-env Δ (cadr (caddr exp))))
                                 (apply-proc (value-of (cadr exp) Δ) (value-of (caddr exp) Δ)))] ; -- 
        ;call-by-name
        [(equal? type 'call) (if (equal? (car (caddr exp)) 'var)
                                 (apply-proc-ref (value-of (cadr exp) Δ) (apply-env Δ (cadr (caddr exp))))
                                 (apply-proc (value-of (cadr exp) Δ) (thunk Δ (caddr exp))))] ; -- vai sair
        
        [(equal? type 'letrec) (value-of (car (cddddr exp)) (extend-env-rec (cadr exp) (caddr exp) (cadddr exp) Δ))] ; -- Ok
        

        [(equal? type 'set) (let ([v (value-of (caddr exp) Δ)])
                              (setref! (apply-env Δ (cadr exp)) v)
                              v)] ; -- Ok
        
        [(equal? type 'begin) (foldr (lambda (e acumulador) (value-of e Δ)) (value-of (cadr exp) Δ) (cddr exp))] ; -- OK

       ; [(equal? type 'self) (()(apply-env env ’%self)) ]

      ;  [(equal? type 'send) (define v (cadr exp)) (foldr (lambda (e acumulador) (value-of e Δ)) (value-of (cadr exp) Δ) (cddr exp))] ;

        [else (error "operação não implementada")])

  )

; ---------------------------- ENV CLASSES -------------------
(require racket/trace)

(struct class (classname super fields methods) ) ; Estrutura para representar os objetos de uma classe

(define class-env '()) ; ou // (define class-env '(empty-class-env))
(define init-env-classes class-env)


(define extend-class-env
  (lambda (name env)
    (set! class-env (append (list (cons name env))
           class-env) )
    )
 )

(define (get-class-env name assoc-name-class)
     (if (equal? name (caar assoc-name-class)) (cdar assoc-name-class)   ; Procurar na lista de classe o env dado o nome
         (get-class-env name (cdr assoc-name-class))
 ))

(define struct-class-list '()) 

(define add-struct-class
  (lambda (name obj_class)
    (set! struct-class-list (append (list (cons name obj_class))
           struct-class-list) )
    )
 )

(define (get-class-struct name struct-list)
     (if (equal? name (caar struct-list)) (cdar struct-list)   ; Procurar na lista de classe o env dado o nome
         (get-class-struct name (cdr struct-list))
 ))

 
(define (apply-class-env env var)
  (env var))


; (extend-class-env 'name init-env)
; (get-class-env 'name class-env)

#|
(define all-classes)
(lambda (classes)
  for(classes)
   init-class(classes[i])
 )
|#

(define init-class
(lambda (class-name super-name fields methods)
  (define aux (class class-name super-name fields methods))
  (add-struct-class class-name aux)
 ))

;(define initialize-class-env!
;  (lambda (c-decls)
;    (set! class-env
;          (list
;           (list ’object (a-class #f ’() ’()))))
;    (for-each initialize-class-decl! c-decls)))

#|


Sobre a avaliação de uma declaração de método, quando você encontrar um, você deverá criar algo semelhante a um procedimento e associar,
posteriormente, a definição da classe.Uma possibilidade é tratar métodos como se fosse procedimento,
porém adicionar sempre um parâmetro a mais referente ao objeto atual



(define init-all ;; Para cada classe colocar os atributos
( lambda(classes)
   (set! class-env
(list
(list 'object (class 'nome #f '() '()))))
(for-each init-classes classes))) ; Pegar as declarações de classe e criar objeto vazio
|#

(define init-all ;; Para cada classe colocar os atributos
( lambda(classes)
   (set! class-env 
(list 'object (class 'nome #f '() '()))))) ; Pegar as declarações de classe e criar objeto vazio


(define init-classes
  (lambda (classes)
    
    display(3)
    )
  ) ; pegar cada atributo e associar a classe


(define (value-of-classes-program class-decls bodyExpr )
  (empty-store)
  (init-all class-decls)
  ;(value-of bodyExpr init-env-classes)
)
(define class-example
'(class-name super-name
field-names method-decls))

(define new-object-exp '(class-name obj_name))

(define a-program '(class-example body))

(value-of-classes-program a-program init-env-classes)

(trace value-of-classes-program)


; Especificação do comportamento de programas
(define (value-of-program prog)
  (empty-store)
  (value-of (cadr prog) init-env))




#|
; Exemplo
let p = proc (x) set x = 4
in let a = 3
   in begin (p a); a end

(define prog '(let p (proc x (set x (lit 4)))
                (let a (lit 3)
                  (begin (call (var p) (var a)) (var a)))))
|#


;(value-of p1 init-env)
;(value-of p2 init-env)
;(value-of p3 init-env)
;(value-of p4 init-env)
