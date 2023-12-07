Require Import List.
Import ListNotations.
Print bool.

Inductive sensId : Type :=
| no 
| yes.

Check sensId.

Lemma not_false : not False.
unfold not.
intros.
exact H.
Qed.

Lemma not_not_A : forall (A: Prop),A-> not (not A).
intros.
unfold not.
intros.
exact (H0 H).
Qed.

Goal forall A B, not (A) /\ not (B) -> not ( or A  B).
intros a b.
unfold not.
intros.
destruct H.
destruct H0.
- exact (H H0).
- apply H1. assumption .
Qed.

Print ex.

Inductive eq2 (A:Type) (x : A) : A -> Prop :=
                                  | eq_refl2 : eq2 A x x.
                                  
Check (eq2 nat 2 2).


Inductive vector {A : Type} : nat -> Type :=
| nil : vector  0
| cons : A -> forall (n: nat), vector  n -> vector  (S(n)).

Inductive Color := 
            | R : Color
            | B : Color.

Inductive tree  {A : Type} : Color -> nat -> Type :=
| nill : tree B 0
| black : A -> forall (c1 c2:Color) (n:nat), tree c1 n -> tree c2 n -> tree B (S n)
| red : A -> forall (n : nat), tree B n -> tree B n -> tree R n.

Print eq.

Theorem trans : forall A (x y : A), eq x y -> forall z, eq y z -> eq x z .
intros.
destruct H.
destruct H0.
exact (eq_refl x).
Qed.


Inductive ex A (P: A-> Prop) : Type := ex_intro : forall a: A, P a -> ex A P. 
Check ex. 

Print tree.

Definition Pointed := sigT (fun A:Type => A).
Check Pointed.

Definition cases {A B A' B': Prop} (f: A -> A') (g: B -> B') (x : {A} + {B}) : {A'}+{B'} :=
match x with 
| left pfA => left (f (pfA))
| right pfB => right (g (pfB))
end.

Fixpoint eqdec ( x y : nat) : {x = y} + {x <> y}.
refine ( match x,y with
| O , O => left _
| (S m), (S n) => cases _ _ (eqdec m n)
| _ , _ => right _ 
end ).
- trivial.
- apply O_S.
- apply not_eq_sym. apply O_S.
- apply eq_S.
- apply not_eq_S.
Qed.

Print sumor.


Inductive Even : nat -> Prop :=
| Even0 : Even 0
| EvenSSn : forall {n}, Even n -> Even (S(S n )).

Lemma even200 : Even 200 .
repeat constructor.
Qed.

Definition aa (A B : Prop) :A -> B -> A \/ B .
intros.
constructor 2.
- exact H0.
Qed.

Inductive taut := | TautTrue : taut
                  | And : taut -> taut -> taut
                  | Or : taut -> taut -> taut .

Fixpoint denote (t:taut) : Prop := 
                          match t with 
                          | TautTrue => True
                          | And t1 t2 => (denote t1) /\ (denote t2)
                          | Or t1 t2 => (denote t1) \/ (denote t2)
end.

Lemma taut_proof : forall t : taut, denote t.
intro t.
induction t.
- simpl. trivial.
- simpl. exact (conj IHt1 IHt2).
- simpl. constructor. exact IHt1.
Qed.

Ltac reify phi := match phi with 
| True => constr : ( TautTrue)
| ?A /\ ?B => let pa := reify (A) in
              let pb := reify (B) in
              constr : (And pa pb )
| ?A \/ ?B => let pa := reify (A) in
              let pb := reify (B) in
              constr : (Or pa pb )
              end.
              
Ltac tautCrush := match goal with 
| [ |- ?G ] => let phir := reify G in
exact ( taut_proof (phir))
end.

Lemma l1 : True /\ True \/ True \/ True .
tautCrush.
Qed.

Inductive hlist {sort : Type} (A : sort -> Type) : list sort -> Type :=
| hnil : hlist A []
| hcons {s} : A s -> forall l : list sort, hlist A (s::l).



(* Q1 *)
Inductive inhabited (A : Set) : Prop :=
| inhabited_intro : A -> inhabited A.

(* Q2 *)
Inductive  exp := 
| Const : nat -> exp 
| Plus : exp -> exp -> exp
| Mul : exp -> exp -> exp.

(*a*)
Fixpoint denote1 (e : exp ) : nat := 
match e with
| Const n => n
| Plus a b => (denote1 a) + (denote1 b)
| Mul a b => (denote1 a) * (denote1 b)
end.

(*b*)

Ltac reify1 n := match n with 
| ?A + ?B => let rA := reify A in 
             let rB := reify B in 
             constr : (Plus rA rB)
| ?A * ?B => let rA := reify A in 
             let rB := reify B in 
             constr : (Mul rA rB)
| 0 => constr : (Const 0)
| S n => constr : (Const (S n))
end.

(* Q3 *)
Inductive In {A} : A -> list A -> Prop :=
| Here : forall x xs, In x (x::xs)
| There : forall x y xs, In x xs -> In x (y::xs).


Arguments Here {A x xs}.
Arguments There {A x y xs}.

(*a*)
Lemma twoinList : In 2 [1;2;3] .
exact (There Here).
Qed.

(*b*)

Fixpoint FIn {A} (y : A) (l : list A) : Prop :=
match l with 
| [] => False
| x :: xs => y = x \/ FIn y xs
end.
