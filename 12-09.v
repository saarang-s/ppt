(* Inductive nat := 
      | O :nat
      | S :nat->nat. *)

(* Fixpoint plus (m n : nat) : nat := 
        match m with 
        | O => n
        | S (mp) => S ((plus n) mp)
end. *)

Fixpoint plus (m n :nat):nat :=
    match m with 
    | O => n
    | S mp => S ( plus mp n)
    end.



(* Predicate *)

(* 
A predicate on nat is just a function from nat -> Prop 

P : nat -> Prop

*)
Locate "exists".


Print and.
Check and.

Print all.

Inductive ex (A:Type) (P: A-> Prop) : Prop :=
                | ex_intro : forall (a:A), P a -> ex A P .


Check ex.

(* Print forall . *)


(* eqnat : nat -> nat -> Prop
 *)

(*  Fixpoint eqnat (x y : nat): Prop :=
                                match x,y with
                                 | O, O => True
                                 | (S n) , (S m) => eqnat n m
                                 | _ , _ => False
end.
  *)

Fixpoint eqnat (x y : nat): Prop :=
  match x, y with
  | O, O => True
  | (S n), (S m) => eqnat n m
  | _, _ => False
  end.


(*  match b : bool with 
  | true => _
  | false => _
  end.

(* This makes sense because bool is an inductively defined
 *)

match b : Prop with 
  | True => _
  | False => _
  end.


(* This doesn't make sense because Prop is not inductively defined.
 *)

*)

Lemma refl_eqnat: forall x:nat, eqnat x x.
intros x.
induction x as [| n IHn].
- simpl. exact I.
- simpl.
exact IHn.
Qed.


Lemma plus_o_n : forall n: nat, eqnat n (plus O n).
intros.
simpl.
apply refl_eqnat.
Qed.

(* Lemma plus_n_o : forall x: nat, eqnat n (plus n O) *)

Print nat.

Lemma plus_n_o : forall n: nat, eqnat n (plus n O).
intros.
induction n as [| n' IHn].
- simpl. exact I.
- simpl.
exact IHn.
Qed.


