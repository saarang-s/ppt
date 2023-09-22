Theorem n_plus_n : forall (n : nat),
  n + n = n * 2.
Proof.
intros n.
induction n.
- trivial.
- simpl. rewrite <- IHn. auto.
Qed.

 