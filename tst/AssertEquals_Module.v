Require Import TestModule_patch.

Print Test.patch.

Theorem assertEquals:
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= p ->
    n <= p + 1.
Proof.
  exact Test.patch.
Qed.
