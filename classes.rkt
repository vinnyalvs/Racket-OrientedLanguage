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
        [(equal? type 'var) (define v (cadr exp))
                            ;(if (thunk? v) (value-of (thunk-exp v) (thunk-env v))
                                (deref (apply-env Δ (cadr exp)))]
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


        [(equal? type 'self ) (apply-env Δ '%self)]
        [(equal? type 'send) (error "operação ainda não implementada") ] ;
       ; [(equal? type 'new) (error "operação ainda não implementada") ]
        [(equal? type 'new) (let* ([args (caddr exp) ]

                                    [obj (new-object (cadr exp))])
                                    
                                    (display 'comencando) )]


        [(equal? type 'super) (error "operação ainda não implementada") ]
        
        [else (error "operação não implementada")])

  )
;[mth (find-method obj 'init)]
;(apply-method mth obj args ))]
; ---------------------------- ENV CLASSES -------------------
(require racket/trace)

(struct class (classname super fields methods env) ) ; Estrutura para representar os objetos de uma classe



;(define class-env '()) ; ou // (define class-env '(empty-class-env))
(define init-env-classes class-env)

(define classes-struct-list (cons 'object (class 'object 'object null null empty-env)) ) ; Lista que vai cada elemento associa um nome de classe a seus atributos (incluindo o env)

(struct object (classname fields-refs))

(struct method (vars body super-name field-names))



(define add-class ; add um struct class a lista classes-struct-list 
  (lambda (name obj_class)
    (set! classes-struct-list (append (list (cons name obj_class))
           classes-struct-list) )
    )
 )

(define (get-class name struct-list)
     (if (empty? struct-list) (void)
     (if (equal? name (caar struct-list)) (cdar struct-list)   ; Procurar na lista de classes o struct dado o nome
         (get-class name (cdr struct-list)))
     )
 )


(define get-field-names
 (lambda(class-name)
  (class-fields (get-class class-name classes-struct-list))
   )
 )



;(map
;(lambda (field-name)
;(newref (list ’uninitialized-field field-name)))
;(class->field-names (lookup-class class-name))))))

;(define get-field-refs
;  (lambda(class-name)
;    (let ([fields-names (get-field-names class-name)])
;      (map 
;      newref (cons 'undefined field-name)
;     )
;    )
;))



(define new-object
(lambda (class-name)
  (object
   class-name
   (map
    (lambda (field-name)
      (newref (list 'uninitialized-field field-name)))
    (get-field-names class-name)))))



; (init-all-classes t)
; (new-object-2 'c1)
(define init-class
(lambda (decl)
  ;(display (cadr decl))
  ;(display (caddr decl))
  ;(display (cdr (cadddr decl)))
  ;(display  (cdar (cadddr (cdr decl))))
  (add-class (cadr decl) ( class (cadr decl) (caddr decl) (cdr (cadddr decl)) (cdar (cadddr (cdr decl))) init-env) ))
  )

;(define add-object-class
;(add-class 'object (class 'object 'object 'fields 'methods empty-env))) ;
 
 
(define init-all-classes
  (lambda (classes-decls)
    (map init-class classes-decls))
 )


(define t '(
            (class c1 object (fields x y)  ((method init () (lit 1 ))))
             (class c2 c1 (fields z w)  ((method init () (lit 5 ))))
            ))

(init-all-classes t)

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



(define (apply-class-env env var)
  (env var))


(define (value-of-classes-program prog )
  (empty-store)
  (init-all-classes (cadr prog)) ; ClassDecl
  ;(value-of (cadr prog init-env)) ; Body Expr
)

; Especificação do comportamento de programas
(define (value-of-program prog)
  (empty-store)
  (value-of (cadr prog) init-env))


(define class-example
'(class-name super-name
field-names method-decls))

(define new-object-exp '(class-name obj_name))

(define a-program '(class-example body))

;(value-of-classes-program a-program init-env-classes)

(trace value-of-classes-program)








;(value-of p1 init-env)
;(value-of p2 init-env)
;(value-of p3 init-env)
;(value-of p4 init-env)
