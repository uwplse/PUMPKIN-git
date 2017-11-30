Require Import Test_patch.

Print patch.

Theorem assertEquals:
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= p ->
    n <= p + 1.
Proof.
  exact patch.
Qed.

