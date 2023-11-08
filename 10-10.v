(* Test 1 answer *)
Variant Person := Guard | Prisoner.

Inductive Seating : Person -> Type :=
| nil : Seating Guard
| G : forall p, Seating p -> Seating Guard
| P : Seating Guard -> Seating Prisoner.

Fixpoint lec (n m : nat) : Prop :=
  match n,n with 
  | O, _ => True
  | S n, S m => lec n m
  | _ , O => False
  end.

Inductive le : nat -> nat -> Prop := 
| le_n : forall n, le n n
| le_s : forall n m, le n m -> le n (S m) .

Inductive lea : nat -> nat -> Prop :=
| le_o : forall n, lea 0 n
| le_S : forall n m, lea n m -> lea (S n) (S m).

Check le_s 4 4 (le_n 4 ).

(* Theorem le_imp_lea : forall (n m : nat), le1 n m -> lea n m .
Proof.
intros.
induction H.
-  *)

Lemma l1 : forall m, le O m.
intros.
induction m.
- exact (le_n 0).
- exact (le_s 0 m IHm).
Qed.

(* Lemma l2 : forall n m, le n m -> le (S n) (S m).
intro n .
induction n. (* Do induction on H*)
- induction m as [ | k IHm]. 
  + intros. exact(le_n 1).
  + intros. constructor. *)

Lemma l2 : forall n m, le n m -> le (S n) (S m).
intros n m H .
induction H.
- exact ( le_n (S n) ).
- exact ( le_s (S n) (S m) (IHle) ).
Qed.


(* Try to prove reflexive trasitive and anti-symetry
aka prove partial order property


Learn : destruct , rewrite and backward rewrite, autorewrite.
*)