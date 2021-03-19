#lang racket

#| CLASSES: Uma Linguagem Orientada a Objetos


; ------------------- Estado IREF --------------------

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


; -------------------- ENV IREF ---------------
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


; --------------------- PROC IREF ----------------------

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


; ----------- value-of exp . Base IREF + operacoes: New, Super, Send, Self e Begin
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

; ---------------------------- ENV CLASSES ------------------- Estruturas criadas para o trabalho
(require racket/trace)

(struct class (classname super fields method-env) ) ; Estrutura para representar as informações de uma CLASSE

 ; Lista que vai cada elemento associa um nome de classe a seus atributos (incluindo o env)
(define classes-struct-list '() ) ;; Inicia lista com classe object

(struct object (classname fields-refs)) ; Estrutura para representar as informações de um OBJETO

; (struct method (vars body super-name field-names)) ; Estrutura para representar as informações de um METODO
(struct method (vars-body super-name field-names))

 ; add um struct class a lista classes-struct-list 
(define add-class
  (lambda (name obj_class)
    (set! classes-struct-list (append (list (cons name obj_class))
           classes-struct-list) )
    )
 )

; Recupera um struct class da lista classes-struct-list a partir do nome
(define (get-class name struct-list)
     (if (empty? struct-list) (void)
     (if (equal? name (caar struct-list)) (cdar struct-list)   ; Procurar na lista de classes o struct dado o nome
         (get-class name (cdr struct-list)))
     )
 )

;Remove duplicatas da lista: https://stackoverflow.com/questions/33716736/removing-duplicates-from-a-list-as-well-as-the-elements-themselves-racket-sche
(define (remove-duplicates list)
  (cond ((empty? list)
         '())
        ((member (first list) (rest list))
         (remove-duplicates (rest list)))
        (else
         (cons (first list) (remove-duplicates (rest list))))))


; Recebe campos do super e campos da classe e retorna nova lista de campos
(define append-fields
  (lambda (fields-super fields-child)
    (cond
      ((null? fields-super) fields-child)
      (else
       (remove-duplicates (append fields-super fields-child)))
   )
  ))


; Pega os nomes dos campos de uma classe dado o nome da classe

(define get-field-names
 (lambda(class-name)
  (class-fields (get-class class-name classes-struct-list))
   )
 )

; A partir das declarações dos metodos cria o env do metodo
(define create-method
  (lambda (method-decl super-name fields)
    (let ([method-name  (car method-decl)])
      (cons method-name (method (cddr method-decl) super-name fields))
      ) )
 )

; Recebe todas as declarações de metodos e 'recursivamente' anda em cada recursão 
(define create-methods-env
  (lambda(methods-decls super-name fields method-env)
    (if (empty? methods-decls) method-env
    (aux-create-methods-env methods-decls super-name fields method-env))
    ))

;Recebe uma declaração de método e chama a função create-methods-env, para cada env criado coloca numa lista 

(define aux-create-methods-env
 (lambda(method-decl super-name fields method-env)
   (set! method-env (append (list (create-method (cdar method-decl) super-name fields) )
           method-env) )
   (create-methods-env (cdr method-decl) super-name fields method-env)
   )
  )

             
; Para uma classe pega as informações da declaração (decl) e cria um novo struct. Esse struct é add na lista com add-class
(define init-class
(lambda (decl)
  ;(display (cadr decl)) -- class-name
 ; (display (caddr decl)) ;-- super-clas-name
  ;(display (cdr (cadddr decl))) -- fields names
 ; (display  (cadddr (cdr decl))) ;-- methods namses
  
  (let ([correct-fields (append-fields (get-field-names (caddr decl)) (cdr (cadddr decl)))] ; Fields do Super e novos fields da classe
        [method-env (append (class-method-env (get-class (caddr decl) classes-struct-list)) (create-methods-env (cadddr (cdr decl)) (caddr decl) (cdr (cadddr decl)) '())  ) ])
    (add-class (cadr decl) ( class (cadr decl) (caddr decl) correct-fields method-env )) ))
  )

;Pega todas as declarações de classes, para cada uma chama init-class
(define init-all-classes
  (lambda (classes-decls)
    (add-class 'object (class 'object 'object null null))
    (map init-class classes-decls))
 )


; Exemplo de código (apenas declarações de classe) que funciona
(define exemplo '(
            (class classe1 object (fields a b)  (( method initialize()(v1 lit 1)) (method teste() (lit 2 )) ))
             (class classe2 classe1 (fields c d)  ((method initialize(5) (lit 5 ))))
             (class classe3 classe2 (fields d e f g)  ((method initialize() (lit 5 ))))
            ))

(define metodos '(( method initialize()(v1 lit 1)) (method teste() (lit 2 )) ))

(init-all-classes exemplo)
; -- Fim exemplo de código



; Criar um novo objeto com nome da classe e referências para os campos

(define new-object
(lambda (class-name)
  (object
   class-name
   (map
    (lambda (field-name)
      (newref (list 'uninitialized-field field-name)))
    (get-field-names class-name)))))


; -- Avalia o programa

(define (value-of-classes-program prog )
  (empty-store)
  (init-all-classes (cadr prog)) ; ClassDecl
  ;(value-of (cadr prog init-env)) ; Body Expr
)

; Especificação do comportamento de programas (IREF)
(define (value-of-program prog)
  (empty-store)
  (value-of (cadr prog) init-env))







