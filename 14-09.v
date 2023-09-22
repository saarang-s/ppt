(* This definition is computational in nature
 *)
Fixpoint eqnat (x y : nat): Prop :=
  match x, y with
  | O, O => True
  | (S n), (S m) => eqnat n m
  | _, _ => False
  end.

Lemma plus_n_o : forall n: nat, eqnat n (plus n O).

intros.
induction n.
- simpl. exact I.
- simpl. exact IHn.
Qed.

Check eqnat.

(* 
For an ideal equality checker "eq"

eq: forall (A: Type), A->A->Prop 
*)


(* For inductive difinitions
             (Parameter)(index)(index)
                 \/       \/     \/              *)
Inductive eq (A : Type) : A ->   A -> Prop := 
                                         | eq_refl : forall x:A, eq A x x.


Check eq_refl.

(* 
Goal eq nat 2 2.
exact eq_refl  nat 2. *)


(* Another definition *)
Inductive eq2 (A:Type) (x : A) : A -> Prop :=
                                  | eq_refl2 : eq2 A x x.

(* The idea of parameter is that, all the constructurs of that type can use those parameters,
Parameter cannot be changed throughout the proof *)


(* Inductive eq {A : Type} : A ->   A -> Prop
  adding {} around A will make it implicit, so you don't have to mention it.

to give the value of implicit argument we specify a @eq, which tells that we are going to give the value of implicit argument.
*)

(* Defining List *)


Inductive list (A: Type) : Type :=
| nil : list A
| cons : A -> list A -> list A.

Check nil.

(* Arguments nil {A}. *)

Check nil.

(* Definition hd {A : Type} (xs: list A ) : A :=
match xs with 
| cons _ y y0 => y
| nil _ => _
end.  *)


Check list.

(* vector : Type -> nat -> Type. *)

Inductive vector (A : Type) : nat -> Type :=
| nill : vector A 0
| cons1 : A -> forall n : nat, vector A n -> vector A (S n).


(* nil : forall A : Type, Vector A O 

cons; forall A:Type, A -> forall n : nat, Vector A n -> Vector A (S n)
 *)


Arguments nil {A}.
Arguments cons1 {A} _ {n}.

Check cons1.
Check nil.

(* Definition head {A} {n} (v : vector A (S n)) : A :=
match v with 
| cons1 _ vector _ S(n')  => n'
end
. *)
(* Argument nil {A}
Argument cons {A} _ {n} *)

Definition hd {A n} (v : vector A (S n)) : A :=
          match v with 
          | cons1 x _ => x
          end. 

