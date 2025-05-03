open HolKernel boolLib bossLib Parse
val _ = new_theory "fib";

Definition fib_def:
  fib 0 = 0 ∧ fib (SUC 0) = 1 ∧ fib (SUC (SUC n)) = fib n + fib (SUC n)
End

Theorem fib_positive:
  ∀n. fib (SUC n) > 0
Proof
  ho_match_mp_tac fib_ind >>
  rw[] >-
   (‘fib (SUC 0) > 0’ suffices_by rw[] >>
    simp[fib_def]
   ) >-
   (‘fib (SUC (SUC 0)) > 0’ suffices_by rw[] >>
    simp[fib_def]
   ) >-
   rw[fib_def]
QED

Theorem fib_add:
  ∀n k. fib (SUC (n + k)) = fib (SUC k) * fib (SUC n) + fib k * fib n
Proof
  ho_match_mp_tac fib_ind >> (*simp[arithmeticTheory.SUC_ONE_ADD]*)
  conj_tac >-
   simp[fib_def] >>
  conj_tac >-
   gs[fib_def]
       
  rw[fib_def] >-
   (‘fib (SUC (SUC k)) = fib k + fib (SUC k)’ suffices_by rw[arithmeticTheory.SUC_ONE_ADD] >>
    simp[fib_def]
   ) >>
  a
QED

val _ = export_theory();
