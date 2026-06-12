#lang typed/racket/base

(require racket/promise
         "common-combinators.rkt")

(require/typed racket/list
  [range (-> Natural Natural (Listof Natural))]
  [remove-duplicates (All (A) (-> (Listof A) (Listof A)))]
  [split-at (All (A) (-> (Listof A) Natural (Values (Listof A) (Listof A))))])

(provide Role
         Grammar
         Choice
         Program
         EvaluatedProgram
         EvaluatedBody
         EvaluatedBodyStream
         EvaluatedProgramStream
         TokenBudget
         LogProb
         TokenOracle
         (struct-out expr)
         (struct-out value)
         (struct-out message)
         (struct-out lit)
         (struct-out gen)
         (struct-out select)
         (struct-out at-least-once)
         (struct-out generated)
         (struct-out selected)
         (struct-out repeated)
         (struct-out token-candidate)
         system
         user
         assistant
         evaluated-body?
         Matcher
         MatcherState
         compile-matcher
         matcher-start
         matcher-advance
         matcher-yields
         matcher-text
         matcher-viable?
         target-token-budget)

(define-type Role (U 'system 'user 'assistant))
(define-type Grammar (Listof expr))
(define-type Choice Grammar)
(define-type Program (Listof (message expr)))
(define-type EvaluatedProgram (Listof (message value)))
(define-type EvaluatedBody (Listof value))
(define-type EvaluatedBodyStream (Sequenceof EvaluatedBody))
(define-type EvaluatedProgramStream (Sequenceof EvaluatedProgram))
(define-type TokenPieces (Listof String))
(define-type TokenBoundaries (Listof Natural))
(define-type ParsePosition Natural)
(define-type TokenBudget Natural)
(define-type LogProb Flonum)

;; Public grammar DSL

;; A backend is only a token oracle. It sees the already fixed transcript and
;; the current generated prefix, and returns a finite top-K approximation of
;; q(token | transcript, prefix).
(struct token-candidate
  ([text : String]
   [logp : LogProb])
  #:transparent)

(define-type TokenOracle (-> EvaluatedProgram String (Listof token-candidate)))

(struct expr () #:transparent)
(struct value expr () #:transparent)

(struct: (A) message
  ([role : Role]
   [body : (Listof A)])
  #:transparent)

(struct lit value
  ([value : String])
  #:transparent)

(struct gen expr
  ([max-tokens : TokenBudget])
  #:transparent)

(struct select expr
  ([first : Choice]
   [rest : (Listof Choice)])
  #:transparent)

(struct at-least-once expr
  ([grammar : Grammar])
  #:transparent)

(struct generated value
  ([source : gen]
   [text : String])
  #:transparent)

(struct selected value
  ([source : select]
   [choice : EvaluatedBody])
  #:transparent)

(struct repeated value
  ([source : at-least-once]
   [text : String])
  #:transparent)

(: system (expr * -> (message expr)))
(define (system . exprs)
  (message 'system exprs))

(: user (expr * -> (message expr)))
(define (user . exprs)
  (message 'user exprs))

(: assistant (expr * -> (message expr)))
(define (assistant . exprs)
  (message 'assistant exprs))

(define-predicate evaluated-body? EvaluatedBody)

;; Matcher

(struct parse-result
  ([live? : Boolean]
   [bodies : (Listof EvaluatedBody)])
  #:transparent)
(define-type ParseResult parse-result)

(struct parse-input
  ([text : String]
   [boundaries : TokenBoundaries]
   [end : ParsePosition])
  #:transparent)
(define-type ParseInput parse-input)

(define-type Parser (-> ParseInput ParsePosition ParseResult))

(struct matcher
  ([parser : Parser])
  #:transparent)
(define-type Matcher matcher)

(struct replay-matcher-state
  ([matcher : Matcher]
   [pieces : TokenPieces]
   [text : String]
   [result : ParseResult])
  #:transparent)
(define-type MatcherState replay-matcher-state)

(: compile-matcher (-> Grammar Matcher))
(define (compile-matcher target)
  (matcher (parse-seq target final-parser #f)))

(: matcher-start (-> Matcher MatcherState))
(define (matcher-start m)
  (replay-matcher-state m '() "" (replay-matcher-run m '())))

(: matcher-advance (-> MatcherState String MatcherState))
(define (matcher-advance state piece)
  (define pieces (append (replay-matcher-state-pieces state) (list piece)))
  (replay-matcher-state (replay-matcher-state-matcher state)
                        pieces
                        (string-append (replay-matcher-state-text state) piece)
                        (replay-matcher-run (replay-matcher-state-matcher state) pieces)))

(: matcher-yields (-> MatcherState (Listof EvaluatedBody)))
(define (matcher-yields state)
  (parse-result-bodies (replay-matcher-state-result state)))

(: matcher-text (-> MatcherState String))
(define (matcher-text state)
  (replay-matcher-state-text state))

(: matcher-viable? (-> MatcherState Boolean))
(define (matcher-viable? state)
  (result-viable? (replay-matcher-state-result state)))

(: replay-matcher-run (-> Matcher TokenPieces ParseResult))
(define (replay-matcher-run m pieces)
  (define text (apply string-append pieces))
  (define boundaries (token-boundaries pieces))
  (result-dedupe ((matcher-parser m) (parse-input text boundaries (string-length text)) 0)))

;; Parser combinators

(: final-parser Parser)
(define (final-parser source pos)
  (if (= pos (parse-input-end source)) (result-done '()) result-empty))

(: parse-seq (-> Grammar Parser Boolean Parser))
(define (parse-seq exprs k k-follows?)
  (cond
    [(null? exprs) k]
    [else
     (define rest (cdr exprs))
     (define next (parse-seq rest k k-follows?))
     (define follows? (or (not (null? rest)) k-follows?))
     (lambda ([source : ParseInput] [pos : ParsePosition])
       (if (> pos (parse-input-end source))
           result-empty
           (parse-expr (car exprs) next follows? source pos)))]))

(: parse-expr (-> expr Parser Boolean ParseInput ParsePosition ParseResult))
(define (parse-expr e k follows? source pos)
  (cond
    [(lit? e)
     (parse-literal (lit-value e) e k source pos)]
    [(generated? e)
     (parse-literal (generated-text e) e k source pos)]
    [(selected? e)
     (parse-choice (selected-source e) (selected-choice e) k follows? source pos)]
    [(repeated? e)
     (parse-literal (repeated-text e) e k source pos)]
    [(select? e)
     (result-choose
      (select-choices e)
      (lambda ([choice : Choice])
        (parse-choice e choice k follows? source pos)))]
    [(at-least-once? e)
     (parse-at-least-once e k source pos)]
    [(gen? e)
     (parse-gen e k follows? source pos)]
    [else result-empty]))

(: parse-choice (-> select Choice Parser Boolean ParseInput ParsePosition ParseResult))
(define (parse-choice source choice k follows? input pos)
  (wrap-choice source
               (length choice)
               ((parse-seq choice k follows?) input pos)))

(: parse-at-least-once
   (-> at-least-once Parser ParseInput ParsePosition ParseResult))
(define (parse-at-least-once expr k source start-pos)
  (define grammar (at-least-once-grammar expr))
  (define grammar-size (length grammar))
  ;; Different repetition splits can reach the same continuation position.
  (define cache : (Vectorof (Promise ParseResult))
    (build-vector
     (add1 (parse-input-end source))
     (lambda ([pos : Index])
       (delay (parse-next-uncached source pos)))))

  (: finish Parser)
  (define (finish input end-pos)
    (prepend-value
     (repeated expr (substring (parse-input-text input) start-pos end-pos))
     (k input end-pos)))

  (: repeat Parser)
  (define (repeat input pos)
    (result-union (finish input pos)
                  (parse-next input pos)))

  (: parse-next-uncached Parser)
  (define (parse-next-uncached input pos)
    (: after-item Parser)
    (define (after-item next-input next-pos)
      (if (> next-pos pos)
          (repeat next-input next-pos)
          result-empty))
    (result-dedupe
     (drop-leading-values
      grammar-size
      ((parse-seq grammar after-item #t) input pos))))

  (: parse-next Parser)
  (define (parse-next input pos)
    (if (eq? input source)
        (force (vector-ref cache pos))
        (parse-next-uncached input pos)))

  (parse-next source start-pos))

(: parse-literal (-> String value Parser ParseInput ParsePosition ParseResult))
(define (parse-literal literal value k source pos)
  (define available (substring (parse-input-text source) pos))
  (cond
    [(and (< (string-length available) (string-length literal))
          (prefix? literal available))
     result-live]
    [(prefix? available literal)
     (prepend-value value
                    (k source (+ pos (string-length literal))))]
    [else result-empty]))

(: prefix? (-> String String Boolean))
(define (prefix? s prefix)
  (and (<= (string-length prefix) (string-length s))
       (string=? (substring s 0 (string-length prefix)) prefix)))

(: parse-gen (-> gen Parser Boolean ParseInput ParsePosition ParseResult))
(define (parse-gen expr k follows? source pos)
  (define boundaries (parse-input-boundaries source))
  (define token-index (position->token-index boundaries pos))
  (define max-take : Natural
    (min (gen-max-tokens expr)
         (remaining-token-count boundaries token-index)))
  (define closed
    (result-choose
     (filter (lambda ([n : Natural])
               (or (positive? n) follows?))
             (range 0 (add1 max-take)))
     (lambda ([n : Natural])
       (define end-pos (token-end-position boundaries pos token-index n))
       (define generated-text (substring (parse-input-text source) pos end-pos))
       (prepend-value (generated expr generated-text)
                      (k source end-pos)))))
  (if (< max-take (gen-max-tokens expr))
      (result-union result-live closed)
      closed))

;; Parse result algebra

(define result-empty (parse-result #f '()))
(define result-live (parse-result #t '()))

(: result-done (-> EvaluatedBody ParseResult))
(define (result-done body)
  (parse-result #f (list body)))

(: result-dedupe (-> ParseResult ParseResult))
(define (result-dedupe m)
  (parse-result (parse-result-live? m)
                (remove-duplicates (parse-result-bodies m))))

(: result-union (-> ParseResult ParseResult ParseResult))
(define (result-union left right)
  (parse-result (or (parse-result-live? left) (parse-result-live? right))
                (append (parse-result-bodies left) (parse-result-bodies right))))

(: result-choose (All (A) (-> (Listof A) (-> A ParseResult) ParseResult)))
(define (result-choose xs f)
  (foldr (lambda ([x : A] [acc : ParseResult])
           (result-union (f x) acc))
         result-empty
         xs))

(: result-map (-> (-> EvaluatedBody EvaluatedBody) ParseResult ParseResult))
(define (result-map f m)
  (parse-result (parse-result-live? m)
                (map f (parse-result-bodies m))))

(: result-viable? (-> ParseResult Boolean))
(define (result-viable? result)
  (or (parse-result-live? result)
      (not (null? (parse-result-bodies result)))))

(: prepend-value (-> value ParseResult ParseResult))
(define (prepend-value value results)
  (result-map (lambda ([values : EvaluatedBody])
                (cons value values))
              results))

(: drop-leading-values (-> Natural ParseResult ParseResult))
(define (drop-leading-values count results)
  (result-map
   (lambda ([values : EvaluatedBody])
     (let-values ([(_prefix tail) (split-at values count)])
       tail))
   results))

(: wrap-choice (-> select Natural ParseResult ParseResult))
(define (wrap-choice source choice-size results)
  (result-map
   (lambda ([values : EvaluatedBody])
     (let-values ([(choice tail) (split-at values choice-size)])
       (cons (selected source choice) tail)))
   results))

;; Token geometry

(: token-boundaries (-> TokenPieces TokenBoundaries))
(define (token-boundaries pieces)
  (let loop ([remaining : (Listof String) pieces]
             [pos : Natural 0]
             [acc : (Listof Natural) '(0)])
    (cond
      [(null? remaining) (reverse acc)]
      [else
       (define next-pos (+ pos (string-length (car remaining))))
       (loop (cdr remaining) next-pos (cons next-pos acc))])))

(: position->token-index (-> TokenBoundaries ParsePosition Natural))
(define (position->token-index boundaries pos)
  (let loop ([xs : (Listof Natural) boundaries]
             [i : Natural 0])
    (cond
      [(or (null? (cdr xs)) (= (car xs) pos)) i]
      [(< pos (cadr xs)) i]
      [else (loop (cdr xs) (add1 i))])))

(: token-count (-> TokenBoundaries Natural))
(define (token-count boundaries)
  (assert (sub1 (length boundaries)) exact-nonnegative-integer?))

(: remaining-token-count (-> TokenBoundaries Natural Natural))
(define (remaining-token-count boundaries token-index)
  (assert (- (token-count boundaries) token-index) exact-nonnegative-integer?))

(: token-end-position (-> TokenBoundaries ParsePosition Natural Natural ParsePosition))
(define (token-end-position boundaries pos token-index n)
  (if (zero? n)
      pos
      (list-ref boundaries (+ token-index n))))

;; Grammar metadata

(: target-token-budget (-> Grammar Natural))
(define (target-token-budget exprs)
  (sum-map expr-token-budget exprs))

(: expr-token-budget (-> expr Natural))
(define (expr-token-budget e)
  (cond
    [(gen? e) (gen-max-tokens e)]
    [(select? e) (apply max (map target-token-budget (select-choices e)))]
    [(at-least-once? e)
     (target-token-budget (at-least-once-grammar e))]
    [(selected? e) (target-token-budget (selected-choice e))]
    [else 1]))

(: select-choices (-> select (Listof Choice)))
(define (select-choices e)
  (cons (select-first e) (select-rest e)))
