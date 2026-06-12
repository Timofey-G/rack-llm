#lang racket/base

(require racket/list
         racket/stream
         rackunit
         rack-llm)

(define (make-recording-model outputs requests)
  (define remaining (box outputs))
  (lambda (transcript prefix)
    (set-box! requests (cons (cons transcript prefix) (unbox requests)))
    (cond
      [(not (string=? prefix "")) '()]
      [else
       (define xs (unbox remaining))
       (cond
         [(null? xs) (error 'recording "no output left")]
         [else
          (set-box! remaining (cdr xs))
          (list (token-candidate (car xs) 0.0))])])))

(define core-examples
  (test-suite
   "core chat grammar examples"

   (test-case "static chats render without calling the model"
     (define requests (box '()))
     (define program
       (list
        (system (lit "You are concise."))
        (user (lit "Hello"))))

     (check-equal?
      (stream-first (eval (make-recording-model '() requests) program))
      (list
       (message 'system (list (lit "You are concise.")))
       (message 'user (list (lit "Hello")))))
     (check-equal? (unbox requests) '()))

   (test-case "select and gen nodes become readable transcript text"
     (define requests (box '()))
     (define choice (select (list (lit "a")) (list (list (lit "ab")))))
     (define answer (gen 4))
     (define program
       (list
        (system (lit "You are concise."))
        (user
         (lit "Choose: ")
         choice
         (lit "c"))
        (assistant answer)))

     (define result
       (stream-first
        (eval
         (make-recording-model
          (list "Choose: abc" "ok")
          requests)
         program)))

     (check-equal?
      result
      (list
       (message 'system (list (lit "You are concise.")))
       (message 'user
                (list (lit "Choose: ")
                      (selected choice (list (lit "ab")))
                      (lit "c")))
       (message 'assistant (list (generated answer "ok")))))
     (define user-selection (second (message-body (second result))))
     (define assistant-generation (first (message-body (third result))))
     (check-equal? (selected-choice user-selection) (list (lit "ab")))
     (check-equal? (generated-text assistant-generation) "ok"))

   (test-case "evaluated AST preserves result nodes"
     (define choice (select (list (lit "x")) (list (list (lit "y")))))
     (define answer (gen 5))
     (define result
       (stream-first
        (eval (make-recording-model
               (list "y" "hello")
               (box '()))
              (list
               (user choice)
               (assistant answer)))))

     (check-true (selected? (first (message-body (first result)))))
     (check-true (generated? (first (message-body (second result)))))
     (check-equal?
      result
      (list (message 'user (list (selected choice (list (lit "y")))))
            (message 'assistant (list (generated answer "hello"))))))

   (test-case "evaluated values render to strings"
     (define choice (select (list (lit "a")) (list (list (lit "b")))))
     (define answer (gen 5))
     (define msg
       (message 'assistant
                (list (lit "prefix ")
                      (selected choice (list (lit "b")))
                      (lit " ")
                      (generated answer "done"))))
     (check-equal? (message->string msg) "prefix b done")
     (check-equal? (body->string (message-body msg)) "prefix b done")
     (check-equal? (value->string (first (message-body msg))) "prefix "))

   (test-case "nested dynamic nodes record values from the selected branch"
     (define nested-answer (gen 3))
     (define nested-choice
       (select (list (lit "a") nested-answer)
               (list (list (lit "b")))))

     (define result
       (stream-first
        (eval (make-recording-model
               (list "axx")
               (box '()))
              (list (assistant nested-choice)))))

     (define selected-body
       (selected-choice (first (message-body (first result)))))
     (check-equal? selected-body
                   (list (lit "a") (generated nested-answer "xx")))
     (check-equal? (generated-text (second selected-body)) "xx"))

   (test-case "at-least-once records one or more repetitions as text"
     (define repeated-as
       (at-least-once (list (lit "a"))))

     (define one
       (stream-first
        (eval (make-recording-model (list "a") (box '()))
              (list (assistant repeated-as)))))
     (define many
       (stream-first
        (eval (make-recording-model (list "aaa") (box '()))
              (list (assistant repeated-as)))))

     (check-equal?
      one
      (list (message 'assistant (list (repeated repeated-as "a")))))
     (check-equal?
      many
      (list (message 'assistant (list (repeated repeated-as "aaa"))))))

   (test-case "at-least-once repeats a compound grammar"
     (define choice
       (select (list (lit "a")) (list (list (lit "b")))))
     (define repeated-items
       (at-least-once
        (list (lit "<") choice (lit ">"))))

     (define result
       (stream-first
        (eval (make-recording-model (list "<a><b>") (box '()))
              (list (assistant repeated-items)))))

     (check-equal?
      result
      (list
       (message 'assistant
                (list (repeated repeated-items "<a><b>"))))))

   (test-case "at-least-once handles ambiguous gen boundaries"
     (define repeated-items
       (at-least-once (list (gen 2))))
     (define (model _transcript prefix)
       (list
        (token-candidate
         (cond
           [(string=? prefix "") "a"]
           [(string=? prefix "a") "b"]
           [(string=? prefix "ab") "c"]
           [(string=? prefix "abc") "!"]
           [else "x"])
         0.0)))

     (define result
       (stream-first
        (eval model
              (list (assistant repeated-items (lit "!"))))))

     (check-equal?
      result
      (list
       (message 'assistant
                (list (repeated repeated-items "abc")
                      (lit "!"))))))

   (test-case "sampler emits each rendered body once"
     (define answer (gen 2))
     (define (model _transcript prefix)
       (cond
         [(string=? prefix "")
          (list (token-candidate "a" 0.0)
                (token-candidate "ab" -0.1))]
         [(string=? prefix "a")
          (list (token-candidate "b" 0.0))]
         [(string=? prefix "ab")
          (list (token-candidate "!" 0.0))]
         [else '()]))

     (define results
       (for/list ([result (eval model
                               (list (assistant answer (lit "!"))))])
         result))

     (check-equal?
      results
      (list
       (list
        (message 'assistant
                 (list (generated answer "ab")
                       (lit "!")))))))

   (test-case "at-least-once can exceed the ordinary grammar budget"
     (define repeated-as
       (at-least-once (list (lit "a"))))
     (define count 40)
     (define (model _transcript prefix)
       (list
        (token-candidate
         (if (< (string-length prefix) count) "a" "z")
         0.0)))

     (define result
       (stream-first
        (eval model
              (list (assistant repeated-as (lit "z"))))))

     (check-equal?
      (repeated-text (first (message-body (first result))))
      (make-string count #\a)))

   (test-case "at-least-once rejects zero and empty repetitions"
     (define required-a
       (at-least-once (list (lit "a"))))
     (define empty-repeat
       (at-least-once '()))

     (check-true
      (stream-empty?
       (eval (make-recording-model (list "z") (box '()))
             (list (assistant required-a (lit "z"))))))
     (check-true
      (stream-empty?
       (eval (make-recording-model (list "x") (box '()))
             (list (assistant empty-repeat))))))

   (test-case "JSON list tail uses select plus at-least-once"
     (define item
       (select (list (lit "\"a\""))
               (list (list (lit "\"b\"")))))
     (define tail
       (select
        '()
        (list
         (list
          (at-least-once
           (list (lit ", ") item))))))

     (define one
       (stream-first
        (eval (make-recording-model (list "[\"a\"]") (box '()))
              (list (assistant (lit "[") item tail (lit "]"))))))
     (define many
       (stream-first
        (eval (make-recording-model
               (list "[\"a\", \"b\", \"a\"]")
               (box '()))
              (list (assistant (lit "[") item tail (lit "]"))))))

     (check-equal?
      (selected-choice (third (message-body (first one))))
      '())
     (define many-tail
       (selected-choice (third (message-body (first many)))))
     (check-equal? (repeated-text (first many-tail))
                   ", \"b\", \"a\""))

   (test-case "model requests receive only previous evaluated messages"
     (define requests (box '()))
     (define choice (select (list (lit "a")) (list (list (lit "ab")))))
     (define answer (gen 4))

     (stream-first
      (eval
       (make-recording-model
        (list "Choose: abc" "ok")
        requests)
       (list
        (system (lit "You are concise."))
        (user (lit "Choose: ") choice (lit "c"))
        (assistant answer))))

     (define ordered-requests
       (filter (lambda (request) (string=? (cdr request) ""))
               (reverse (unbox requests))))
     (check-equal? (length ordered-requests) 2)
     (check-equal?
      (car (first ordered-requests))
      (list (message 'system (list (lit "You are concise.")))))
     (check-equal?
      (cdr (first ordered-requests))
      "")
     (check-equal? (cdr (second ordered-requests)) ""))))

(module+ test
  (require rackunit/text-ui)
  (run-tests core-examples))
