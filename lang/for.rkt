;; using continuation to implement for-loop with break and continue

#lang r5rs

(define (for_block i break continue)
  (if (= 3 i) (continue '()) '())
  (display i) (newline)
  (if (= 5 i) (break '()) '()))

#|
(define (for n f) (lambda (break)
  (if (< 0 n)
      (begin
        ((for (- n 1) f) break)
        (call-with-current-continuation (lambda (continue)
          (for_block (- n 1) break continue))))
      '())))

(call-with-current-continuation (for 10 for_block))
|#

(define (for_t n f)
  (define (for_i m n f) (lambda (break) (
    if (< m n)
       (begin
         (call-with-current-continuation (lambda (continue)
          (for_block m break continue)))
         ((for_i (+ m 1) n f) break))
       '())))
  (call-with-current-continuation (for_i 0 n f)))


(for_t 10 for_block)
