#lang typed/racket/base

(require typed/racket/stream
         "common-combinators.rkt"
         "grammar.rkt")

(require/typed racket/list
  [filter-map (All (A B) (-> (-> A (U B False)) (Listof A) (Listof B)))])

(provide decode-body)

(define-type GumbelScore Flonum)
(define-type SeenTexts (Immutable-HashTable String True))

(: rendered-value-text (-> value String))
(define (rendered-value-text v)
  (cond
    [(lit? v) (lit-value v)]
    [(generated? v) (generated-text v)]
    [(selected? v) (rendered-body-text (selected-choice v))]
    [(repeated? v) (repeated-text v)]
    [else (error 'decode-body "unsupported evaluated value: ~e" v)]))

(: rendered-body-text (-> EvaluatedBody String))
(define (rendered-body-text body)
  (apply string-append (map rendered-value-text body)))

;; Repetition is unbounded in the AST, so decoding still needs an operational cap.
(define repeating-search-budget : TokenBudget 256)

(struct frontier-node
  ([depth : TokenBudget]
   [logp : LogProb]
   [g : GumbelScore]
   [state : MatcherState])
  #:transparent)
(define-type FrontierNode frontier-node)
(define-type FrontierAgenda (agenda FrontierNode))

(struct: (A) agenda
  ([better? : (-> A A Boolean)]
   [items : (Listof A)])
  #:transparent)

(struct: (A) agenda-view
  ([item : A]
   [rest : (agenda A)])
  #:transparent)

(: decode-body (-> TokenOracle EvaluatedProgram Grammar EvaluatedBodyStream))
(define (decode-body oracle transcript target)
  (define matcher (compile-matcher target))
  (gumbel-stream
   (frontier-expander oracle transcript (search-budget target))
   (frontier-root matcher)))

(: gumbel-stream (-> (-> FrontierNode (Listof FrontierNode)) FrontierNode EvaluatedBodyStream))
(define (gumbel-stream expand root)
  (define debug-search? : Boolean
    (and (getenv "RACK_LLM_DEBUG_SEARCH") #t))
  (define debug-phases? : Boolean
    (and (getenv "RACK_LLM_DEBUG_PHASES") #t))
  (define debug-every : Positive-Integer
    (let ([value (getenv "RACK_LLM_DEBUG_EVERY")])
      (if value
          (assert (or (string->number value) 100) exact-positive-integer?)
          100)))
  (define popped : Natural 0)
  (define expanded : Natural 0)
  (define children : Natural 0)
  (define last-yield-popped : Natural 0)
  (define last-yield-expanded : Natural 0)
  (define started-at : Flonum (current-inexact-milliseconds))

  (: log-phase (-> String Natural Flonum Flonum Natural Void))
  (define (log-phase phase node-number start finish count)
    (when debug-phases?
      (eprintf
       "sampler phase: node=~a phase=~a start=~a finish=~a duration-ms=~a count=~a\n"
       node-number
       phase
       (real->decimal-string (/ (- start started-at) 1000.0) 1)
       (real->decimal-string (/ (- finish started-at) 1000.0) 1)
       (real->decimal-string (- finish start) 1)
       count)
      (flush-output (current-error-port))))

  (: emit-unique
     (-> (Listof EvaluatedBody)
         SeenTexts
         (-> SeenTexts EvaluatedBodyStream)
         EvaluatedBodyStream))
  (define (emit-unique bodies seen continue)
    (cond
      [(null? bodies) (continue seen)]
      [else
       (define body (car bodies))
       (define text (rendered-body-text body))
       (cond
         [(hash-has-key? seen text)
          (emit-unique (cdr bodies) seen continue)]
         [else
          (define next-seen (hash-set seen text #t))
          (stream-cons body
                       (emit-unique (cdr bodies) next-seen continue))])]))

  (: step (-> FrontierAgenda SeenTexts EvaluatedBodyStream))
  (define (step queue seen)
    (define next (agenda-pop queue))
    (cond
      [(not next) empty-stream]
      [else
       (set! popped (add1 popped))
       (define current (agenda-view-item next))
       (define rest (agenda-view-rest next))
       (when (and debug-search? (zero? (remainder popped debug-every)))
         (define current-prefix (frontier-text current))
         (eprintf
          "sampler progress: elapsed=~a popped=~a expanded=~a queue=~a children=~a depth=~a\n"
          (real->decimal-string
           (/ (- (current-inexact-milliseconds) started-at) 1000.0)
           1)
          popped
          expanded
          (length (agenda-items queue))
          children
          (frontier-node-depth current))
         (when (getenv "RACK_LLM_DEBUG_PREFIX")
           (eprintf "sampler prefix: ~s\n" current-prefix))
         (flush-output (current-error-port)))
       (define yield-start (current-inexact-milliseconds))
       (when debug-phases?
         (eprintf "sampler phase-start: node=~a phase=matcher-yields depth=~a\n"
                  popped
                  (frontier-node-depth current))
         (flush-output (current-error-port)))
       (define yields (frontier-yields current))
       (define yield-finish (current-inexact-milliseconds))
       (log-phase "matcher-yields"
                  popped
                  yield-start
                  yield-finish
                  (length yields))
       (when (and debug-search? (not (null? yields)))
         (eprintf
          "sampler yield: bodies=~a depth=~a queue=~a popped=~a (+~a) expanded=~a (+~a) children=~a\n"
          (length yields)
          (frontier-node-depth current)
          (length (agenda-items queue))
          popped
          (- popped last-yield-popped)
          expanded
          (- expanded last-yield-expanded)
          children)
         (flush-output (current-error-port))
         (set! last-yield-popped popped)
         (set! last-yield-expanded expanded))
       (emit-unique
        yields
        seen
        (lambda (next-seen)
          (set! expanded (add1 expanded))
          (define expand-start (current-inexact-milliseconds))
          (when debug-phases?
            (eprintf "sampler phase-start: node=~a phase=expand queue=~a depth=~a\n"
                     popped
                     (length (agenda-items rest))
                     (frontier-node-depth current))
            (flush-output (current-error-port)))
          (define raw-successors (expand current))
          (define expand-finish (current-inexact-milliseconds))
          (log-phase "expand"
                     popped
                     expand-start
                     expand-finish
                     (length raw-successors))
          (define filter-start (current-inexact-milliseconds))
          (when debug-phases?
            (eprintf "sampler phase-start: node=~a phase=filter-viable children=~a\n"
                     popped
                     (length raw-successors))
            (flush-output (current-error-port)))
          (define successors (filter frontier-viable? raw-successors))
          (define filter-finish (current-inexact-milliseconds))
          (log-phase "filter-viable"
                     popped
                     filter-start
                     filter-finish
                     (length successors))
          (set! children (+ children (length successors)))
          (define insert-start (current-inexact-milliseconds))
          (when debug-phases?
            (eprintf "sampler phase-start: node=~a phase=agenda-push queue=~a children=~a\n"
                     popped
                     (length (agenda-items rest))
                     (length successors))
            (flush-output (current-error-port)))
          (define next-queue (agenda-push* rest successors))
          (define insert-finish (current-inexact-milliseconds))
          (log-phase "agenda-push"
                     popped
                     insert-start
                     insert-finish
                     (length (agenda-items next-queue)))
          (step next-queue next-seen)))]))
  (step (agenda-singleton frontier-better? root)
        (ann (hash) SeenTexts)))

(: frontier-expander (-> TokenOracle EvaluatedProgram TokenBudget (-> FrontierNode (Listof FrontierNode))))
(define (frontier-expander oracle transcript max-depth)
  (lambda ([parent : FrontierNode])
    (if (>= (frontier-node-depth parent) max-depth)
        '()
        (let ()
          (define debug-phases? : Boolean
            (and (getenv "RACK_LLM_DEBUG_PHASES") #t))
          (define oracle-start (current-inexact-milliseconds))
          (when debug-phases?
            (eprintf "sampler phase-start: depth=~a phase=oracle prefix-length=~a\n"
                     (frontier-node-depth parent)
                     (string-length (frontier-text parent)))
            (flush-output (current-error-port)))
          (define candidates (oracle transcript (frontier-text parent)))
          (define oracle-finish (current-inexact-milliseconds))
          (when debug-phases?
            (eprintf "sampler phase: depth=~a phase=oracle duration-ms=~a count=~a\n"
                     (frontier-node-depth parent)
                     (real->decimal-string (- oracle-finish oracle-start) 1)
                     (length candidates))
            (flush-output (current-error-port)))
          (define build-start (current-inexact-milliseconds))
          (when debug-phases?
            (eprintf "sampler phase-start: depth=~a phase=build-children candidates=~a\n"
                     (frontier-node-depth parent)
                     (length candidates))
            (flush-output (current-error-port)))
          (define result
            (condition-subtrees
             parent
             (filter-map (lambda ([c : token-candidate])
                           (define child (frontier-child parent c))
                           (when (and child
                                      (getenv "RACK_LLM_DEBUG_CLOSERS")
                                      (regexp-match?
                                       #rx"\\]"
                                       (token-candidate-text c)))
                             (eprintf
                              "sampler closer-child: token=~s viable=~a yields=~a depth=~a\n"
                              (token-candidate-text c)
                              (frontier-viable? child)
                              (length (frontier-yields child))
                              (frontier-node-depth child))
                             (flush-output (current-error-port)))
                           child)
                         candidates)))
          (define build-finish (current-inexact-milliseconds))
          (when debug-phases?
            (eprintf "sampler phase: depth=~a phase=build-children duration-ms=~a count=~a\n"
                     (frontier-node-depth parent)
                     (real->decimal-string (- build-finish build-start) 1)
                     (length result))
            (flush-output (current-error-port)))
          result))))

;; Frontier algebra

(: frontier-root (-> Matcher FrontierNode))
(define (frontier-root matcher)
  (frontier-node 0 0.0 (gumbel) (matcher-start matcher)))

(: frontier-child (-> FrontierNode token-candidate (U FrontierNode False)))
(define (frontier-child parent candidate)
  (and (valid-candidate? candidate)
       (let ([logp (+ (frontier-node-logp parent)
                      (token-candidate-logp candidate))])
         (frontier-node (add1 (frontier-node-depth parent))
                        logp
                        (+ logp (gumbel))
                        (matcher-advance (frontier-node-state parent)
                                         (token-candidate-text candidate))))))

(: condition-subtrees (-> FrontierNode (Listof FrontierNode) (Listof FrontierNode)))
(define (condition-subtrees parent children)
  (cond
    [(null? children) '()]
    [else
     (define raw-max (apply max (map frontier-node-g children)))
     (map (lambda ([child : FrontierNode])
            (condition-subtree parent raw-max child))
          children)]))

(: condition-subtree (-> FrontierNode GumbelScore FrontierNode FrontierNode))
(define (condition-subtree parent raw-max child)
  (struct-copy frontier-node child
               [g (cond-gumbel (frontier-node-g parent)
                               (frontier-node-g child)
                               raw-max)]))

(: frontier-yields (-> FrontierNode (Listof EvaluatedBody)))
(define (frontier-yields n)
  (matcher-yields (frontier-node-state n)))

(: frontier-successors (-> (-> FrontierNode (Listof FrontierNode)) FrontierNode (Listof FrontierNode)))
(define (frontier-successors expand n)
  (filter frontier-viable? (expand n)))

(: frontier-text (-> FrontierNode String))
(define (frontier-text n)
  (matcher-text (frontier-node-state n)))

(: frontier-viable? (-> FrontierNode Boolean))
(define (frontier-viable? n)
  (matcher-viable? (frontier-node-state n)))

(: frontier-better? (-> FrontierNode FrontierNode Boolean))
(define (frontier-better? left right)
  (> (frontier-node-g left) (frontier-node-g right)))

(: valid-candidate? (-> token-candidate Boolean))
(define (valid-candidate? candidate)
  (> (token-candidate-logp candidate) -1e300))

(: search-budget (-> Grammar TokenBudget))
(define (search-budget target)
  (max 8
       (+ 16 (target-token-budget target))
       (if (grammar-repeats? target)
           repeating-search-budget
           0)))

(: grammar-repeats? (-> Grammar Boolean))
(define (grammar-repeats? grammar)
  (ormap expr-repeats? grammar))

(: expr-repeats? (-> expr Boolean))
(define (expr-repeats? e)
  (cond
    [(at-least-once? e) #t]
    [(select? e)
     (ormap grammar-repeats?
            (cons (select-first e) (select-rest e)))]
    [(selected? e)
     (grammar-repeats? (selected-choice e))]
    [else #f]))

;; Agenda

(: agenda-singleton (All (A) (-> (-> A A Boolean) A (agenda A))))
(define (agenda-singleton better? item)
  (agenda better? (list item)))

(: agenda-pop (All (A) (-> (agenda A) (U False (agenda-view A)))))
(define (agenda-pop q)
  (define items (agenda-items q))
  (if (null? items)
      #f
      (agenda-view (car items)
                   (agenda (agenda-better? q) (cdr items)))))

(: agenda-push* (All (A) (-> (agenda A) (Listof A) (agenda A))))
(define (agenda-push* q items)
  (agenda (agenda-better? q)
          (foldl (lambda ([item : A] [queue : (Listof A)])
                   (agenda-insert (agenda-better? q) item queue))
                 (agenda-items q)
                 items)))

(: agenda-insert (All (A) (-> (-> A A Boolean) A (Listof A) (Listof A))))
(define (agenda-insert better? item queue)
  (cond
    [(null? queue) (list item)]
    [(better? item (car queue)) (cons item queue)]
    [else (cons (car queue) (agenda-insert better? item (cdr queue)))]))

;; Gumbel noise

(: ->fl (-> Number Flonum))
(define (->fl x)
  (real->double-flonum (real-part x)))

(: gumbel (-> GumbelScore))
(define (gumbel)
  (define u (max 1e-12 (min (- 1.0 1e-12) (random))))
  (->fl (- (log (- (log u))))))

(: cond-gumbel (-> GumbelScore GumbelScore GumbelScore GumbelScore))
(define (cond-gumbel parent-g raw-child-g raw-max)
  (define mass
    (+ (- (exp (- parent-g))
          (exp (- raw-max)))
       (exp (- raw-child-g))))
  (->fl (- (log (max 1e-300 (real-part mass))))))
