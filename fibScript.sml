open HolKernel boolLib bossLib Parse
     arithmeticTheory intLib gcdTheory

val _ = new_theory "fib";

Definition fib_int_def:
  fib_int (n: num): int =
  if n = 0 then 0
  else if n = 1 then 1
  else fib_int (n - 1) + fib_int (n - 2)
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

(*CHECKED UP TO HERE*)

Definition fib_def:
  fib (n:num) =
  if n ≤ 1 then n else fib (n - 2) + fib (n - 1)
End

Theorem fib_positive:
  ∀n. fib (n + 1) > 0
Proof
  Induct >> simp[Once fib_def, ADD1]
QED

Theorem fib_leq_1:
  n ≤ 1 ⇒ fib n = n
Proof
  rw[Once fib_def]
QED

Theorem fib_add:
  ∀k. fib (n + k + 1) =
      fib (k + 1) * fib (n + 1) + fib k * fib n
Proof
  recInduct fib_ind>>
  rw[]>>
  rename1 ‘k ≤ 1’>>
  Cases_on ‘k ≤ 1’
  >-(
    Cases_on ‘k = 0’
    >- simp[fib_leq_1]
    >- (
      ‘k = 1’ by simp[]>>
      ‘fib 2 = 1’ by EVAL_TAC>>
      simp[fib_leq_1, Once fib_def]
       ))
  >-(
    gvs[]>>
    simp[Once fib_def]>>
    ‘fib k = fib (k - 1) + fib (k - 2)’ by simp[Once fib_def]>>      ‘fib (k + 1) = fib k + fib (k - 1)’ by simp[Once fib_def]>>
    simp[]
    )
QED

Theorem coprime_fib_suc:
  ∀n. coprime (fib n) (fib (n + 1))
Proof
  simp[Once gcdTheory.coprime_sym]>>
  Induct
  >- EVAL_TAC
  >- simp[ADD1, Once fib_def]
QED

Theorem gcd_fib_add:
  ∀m. gcd (fib m) (fib (n + m)) = gcd (fib m) (fib n)
Proof
  Induct
  >- simp[]
  >-(
    simp[ADD1, Once gcdTheory.GCD_COMM]>>
    pure_rewrite_tac[fib_add, Once ADD_ASSOC]>>
    simp[gcdTheory.GCD_REDUCE]>>
    irule gcdTheory.GCD_REDUCE_BY_COPRIME>>
    metis_tac[coprime_fib_suc, gcdTheory.coprime_sym]
  )
QED

Theorem gcd_fib_diff:
  m ≤ n ⇒ gcd (fib m) (fib (n - m)) = gcd (fib m) (fib n)
Proof
  rw[]>>
  ‘n - m + m = n’ by decide_tac>>
  metis_tac[gcd_fib_add]
QED

Theorem gcd_fib_mod:
  ∀n. 0 < m ⇒
    gcd (fib m) (fib (n MOD m)) = gcd (fib m) (fib n)
Proof
  completeInduct_on ‘n’>>
  Cases_on ‘n < m’
  >-simp[]
  >-((*Case n ≥ m. Prove RHS = LHS:
         gcd (fib m) (fib n)
       = gcd (fib m) (fib (n - m))  [by sym. of gcd_fib_diff]
       = gcd (fib m) (fib ((n - m) MOD m))  [by sym. of IH and n - m < n]
       = gcd (fib m) (fib (n MOD m))  [since n ≥ m]
      *)
     last_x_assum (fn thm => qspec_then ‘n - m’ assume_tac thm)>>
     strip_tac>>
     gvs[NOT_LESS, SUB_MOD, gcd_fib_diff]
    )
QED

Theorem gcd_fib_mod_gen:
  ∀m n. 0 < m ⇒
    gcd (fib m) (fib (n MOD m)) = gcd (fib m) (fib n)
Proof
  metis_tac[gcd_fib_mod]
QED

Theorem fib_gcd:
  ∀m n. fib (gcd m n) = gcd (fib m) (fib n)
Proof
  completeInduct_on ‘n’>>
  Cases_on ‘n = 0’
  >-(‘fib 0 = 0’ by EVAL_TAC>>
     simp[]
  )
  >-(rw[]>>
     last_x_assum (fn thm => qspec_then ‘m MOD n’ assume_tac thm)>>
     rfs[]>>
     pop_assum (qspec_then ‘n’ assume_tac)>>
     qspecl_then [‘n’, ‘m’] assume_tac gcd_fib_mod_gen>>
     qspecl_then [‘n’, ‘m’] assume_tac gcdTheory.GCD_MOD>>
     last_x_assum (fn thm => fs[thm])>>
     metis_tac[gcdTheory.GCD_SYM]
  )
QED

val _ = export_theory();
