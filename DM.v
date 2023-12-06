(* 
not A  \/ not B -> not (A /\ B)
not A /\ not B -> not (A \/ B)
not (A \/ B) -> not A /\ not B
not (A /\ B) -> not A \/ not B 
*)

Check not.

Definition dm1 : forall A B : Prop,  ((not A) \/ (not B)) -> (not ( A /\ B)) := 
fun (A B : Prop)(nAonB : ((not A) \/ (not B))) =>
match nAonB with
| or_introl ( nA ) => fun (AaB : A /\ B) => match AaB with
                                            | conj pA pB => nA pA end
| or_intror ( nB ) => fun (AaB : A /\ B) => match AaB with
                                            | conj pA pB => nB pB end
end.

Theorem DM1 : forall A B : Prop, ((not A) \/ (not B)) -> (not ( A /\ B)).
unfold not.
intros.
destruct H0.
destruct H.
- exact (H H0).
- exact (H H1).
Qed.

Definition dm2 : forall A B : Prop,  not A /\ not B -> not (A \/ B) := 
fun (A B : Prop) (nAanB : not A /\ not B ) => match nAanB with
                                              | conj nA nB => fun (AoB : (A \/ B)) => match AoB with
                                                                                      | or_introl pA => nA pA
                                                                                      | or_intror pB => nB pB end
end.

Theorem DM2 : forall A B : Prop,  not A /\ not B -> not (A \/ B).
unfold not.
intros.
destruct H.
destruct H0.
- exact (H H0).
- exact (H1 H0).
Qed.

Definition dm3  : forall A B : Prop, not (A \/ B) -> not A /\ not B :=
fun (A B : Prop ) (nAoB : not (A \/ B)) => conj (fun (pA : A) => nAoB (or_introl pA))
                                                (fun (pB : B) => nAoB (or_intror pB))
.

Theorem DM3  :forall A B : Prop, not (A \/ B) -> not A /\ not B.
unfold not.
intros.
split.
- intro pi; exact (H (or_introl pi)).
- intro pi; exact (H (or_intror pi)).
Qed.

(* Theorem DM4  :forall A B : Prop, not (A /\ B) -> not A \/ not B .
unfold not.
- intros.
left.
intro. *)

(* Inductive ex  (A : Type) (P : A -> Prop) : Prop := 
ex_intro : forall x : A, P x -> ex A P. *)

(* Another definition *)
Inductive eq2 (A:Type) (x : A) : A -> Prop :=
                                  | eq_refl2 : eq2 A x x.

Check eq2.
Check eq_refl2.

Inductive eq1 (A:Type) : A -> A -> Prop :=
                                  | eq_refl1 : forall x: A, eq1 A x x.

Check eq1.
Check eq_refl1.

Goal eq1 nat 2 2.
exact (eq_refl1 nat 2 ).
Qed. 


Inductive vector (A : Type) : nat -> Type :=
| nill : vector A 0
| cons1 : forall x:A , forall n : nat, vector A n -> vector A (S n).

Check vector.
Check cons1.

Arguments nill {A}.
Arguments cons1 {A} _ {n}. 


(* Definition hd' {A : Type} n (v : vector A n) : match n with 
                                    | O => IDProp
                                    | S _ => A
                                    end
                                    :=
                                              match v in vector _ n0 return 
                                                                            match n0 with 
                                                                            | O => IDProp
                                                                            | S _ => A
                                                                            end with 
                                              | cons1 _ x _ _ => x end. *)
                                              
Ltac intro_custom := let C := fresh "C" in 
match goal with
  | [ |- forall (_ : ?T), _ ] => refine (fun (_ : T) => _)
  | [ |- ?H -> _ ] => refine (fun c : H => _)
  end.

Ltac Known := match goal with 
| [H:?G |- ?G] => exact H
end.

Goal forall A B: Prop, A -> B -> A.
intro.
intro.

refine ( fun (a: A) (b : B) => _ ).
trivial.
Qed.

Inductive even_nat : nat -> Type :=
| EvenO : even_nat 0
| EvenS : forall n, even_nat n -> even_nat (S (S n)).

Definition even_pair : sigT  even_nat :=
  existT _ 4 (EvenS _ (EvenS _ (EvenO ))).

(* Goal forall n : nat, n + 0 = n.
Proof.
  intro n.
  simpl.
  refine (eq_refl _ ).
Qed.
 *)
 
 

Definition exTosig (A : Type) (P : A -> Prop) (e : sig P) : ex P :=
match  e with
| exist _ x Px => ex_intro _  x Px 
end.

Definition exTosig (A : Type) (P : A -> Prop) (e : ex P) : sig  P :=
match  e with
| ex_intro _ x Px => exist _ x Px 
end.


