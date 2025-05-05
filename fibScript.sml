open HolKernel boolLib bossLib Parse
     arithmeticTheory intLib;
val _ = new_theory "fib";

Definition fib_int_def:
  fib_int (n: num): int = if n = 0 then 0 else if n = 1 then 1 else fib_int (n - 1) + fib_int (n - 2)
End

Theorem fib_int_positive:
  ∀n. fib_int (n + 1) > 0
Proof
  recInduct fib_int_ind>>
  rw[]>>
  rw[Once fib_int_def]>> (*‘n ≠ 0’ introduced as assm*)
  Cases_on ‘n = 1’ (*split into two subgoals ‘n = 1’ and ‘n ≠ 1’*)
  >-(rw[]>>
     EVAL_TAC (*EVAL_TAC is as though telling HOL to EVAL the term*)
    )
  >-(fs[]>>
     ARITH_TAC (*I found no reference for this*)
    )
QED

Definition fib_def:
  fib (n:num) = if n ≤ 1 then n else fib (n - 2) + fib (n - 1)
End

Theorem fib_positive:
  ∀n. fib (n + 1) > 0
Proof
  Induct >> simp[Once fib_def, ADD1]
QED

Theorem fib_add:
  ∀n k. fib (n + k + 1) = fib (k + 1) * fib (n + 1) + fib k * fib n
Proof
  ho_match_mp_tac fib_ind >> (*simp[arithmeticTheory.SUC_ONE_ADD]*)
  conj_tac >- (
   simp[fib_def]) >>
  conj_tac >-
   gs[fib_def]

  rw[fib_def] >-
   (‘fib (SUC (SUC k)) = fib k + fib (SUC k)’ suffices_by rw[arithmeticTheory.SUC_ONE_ADD] >>
    simp[fib_def]
   ) >>
  a
QED

Definition coprime_def:
  coprime m n ⇔ ∀d. (d > 0 ∧ m MOD d = 0 ∧ n MOD d = 0) ⇒ d = 1
End

Theorem lem_1:
  coprime (fib 0) (fib (SUC 0))
Proof
  simp[Once fib_def]>>
  simp[Once fib_def]
QED

Theorem coprime_fib_suc:
  ∀n. coprime (fib n) (fib (SUC n))
Proof
  ho_match_mp_tac fib_ind>>
  Cases
  >- (
   strip_tac>>
   simp[]>>
   simp[Once fib_def]>>
   simp[Once fib_def]>>
   simp[coprime_def]>>
   rw[]>>
   Cases_on ‘d’
   >- simp[]
   >- (Cases_on ‘n’
       >- simp[]
       >- (
        simp[]>>
        rw[]
       )
   )
  )
QED
     
val _ = export_theory();
