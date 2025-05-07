open HolKernel boolLib bossLib Parse
     arithmeticTheory intLib gcdTheory;

val _ = new_theory "fib";

Definition fib_int_def:
  fib_int (n: num): int = if n = 0 then 0 else if n = 1 then 1 else fib_int (n - 1) + fib_int (n - 2)
End

Theorem fib_int_nonnegative:
  ∀n. fib_int n ≥ 0
Proof
  recInduct fib_int_ind>>
  rw[]>>
  rw[Once fib_int_def]>>
  fs[]>>
  ARITH_TAC
QED

Theorem fib_int_positive:
  ∀n. fib_int (n + 1) > 0
Proof
  Induct>>
  simp[Once fib_int_def, ADD1]>>
  qspec_then ‘n’ assume_tac fib_int_nonnegative>>
  ARITH_TAC
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
  ∀k. fib (n + k + 1) = fib (k + 1) * fib (n + 1) + fib k * fib n
Proof
  Induct_on ‘k’ using fib_ind>>
  Cases_on ‘k ≤ 1’
  >-(rw[]>>
     Cases_on ‘k = 0’
     >-(rw[]>>
        qabbrev_tac ‘a = fib (n + 1)’>>
        qabbrev_tac ‘b = fib n’>>
        EVAL_TAC>>
        decide_tac
       )
     >-(‘k = 1’ by simp[]>>
        simp[]>>
        rw[Once fib_def]>>
        qabbrev_tac ‘a = fib (n + 1)’>>
        qabbrev_tac ‘b = fib n’>>
        EVAL_TAC>>
        decide_tac
       )
    )
  >-(
     gvs[]>>
     simp[Once fib_def]>>
     qabbrev_tac ‘a = fib (n + 1)’>>
     qabbrev_tac ‘b = fib n’>>
     simp[Once $ GSYM fib_def]>>
     simp[boolTheory.EQ_SYM_EQ]>>
     simp[Once fib_def]>>
     ‘b * fib k = b * (fib (k - 1) + fib (k - 2))’ by simp[Once fib_def]>>
     simp[]
     (**)
     (*I found nothing by doing: print_match ["arithmetic"] “p * (m + n) = p * m + p * n”
       but found the intended match by doing: print_find "DISTRIB"*)
    )
QED

Theorem coprime_fib_suc:
  ∀n. coprime (fib n) (fib (n + 1))
Proof
  simp[Once gcdTheory.coprime_sym]>>
  Induct
  >-(EVAL_TAC)
  >-(simp[ADD1, Once fib_def])
  (*
  Induct
  >-(EVAL_TAC)
  >-(‘fib (n + 2) = fib n + fib (n + 1)’ by simp[Once fib_def]>>
     simp[ADD1]>>
     metis_tac[gcdTheory.coprime_sym]
    )
  *)
QED

Theorem gcd_fib_add:
  ∀m n. gcd (fib m) (fib (n + m)) = gcd (fib m) (fib n)
Proof
  cheat
  (*Cases
  >-(simp[gcd_def])
  >-()*)
QED

val _ = export_theory();
