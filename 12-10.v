
Search (_ <= _).

(* and prove all the lemmas identities *)

(* There exists x Px -> Proof of thereExists x:A Px is a pair w:A pw : Pw. *)

Print ex.

Inductive ex A (P: A-> Prop) := ex_intro : forall a: A, P a -> ex A P.

(* Set the defines the a set {x:A | P x}
 *)
(* Inductive sig (A : Type) (P : A -> Prop) : Type := 
| exist : forall a:A , P a -> sig A P. *)

(* Definting predecessor of nat
 *)

(* Definition pred (x:nat) : n option nat *)


(*The below {n:nat | n > 0} is same as sig nat (fun n => n > 0) *)


Check ({n:nat | n > 0}).
(* Check (sig nat (fun n => n > 0)). *)

Print sig.

Definition pred (x : {n:nat | n > 0} ): nat := 
match x with 
| exist _ x' _ => match x' with 
                               | 0 => 42
                               | S m => m
                               end
end.

Inductive sigT (A:Type) (P:A->Type) :=
| existT : forall a:A, P a -> sigT A P.

Print sigT.

Definition Pointed := sigT Type (fun A:Type => A).

Check nil.

(* There is dynamic type in haskell
todyn : forall A, A -> Dyn
fromdyn : forall B, Dyn -> option B
 *)

(* Definition F A B : A->B.
intros.
exact Set. *)

(* Definition n := 1 :: 3 :: nil.
Check (1 :: 3 :: nil).

Check (1::2::nil).

Check ( [existT _ nat 2 , existT _ bool true] ).
 *)


(*
Logic                     | Type theory
--------------------------+-----------------------------
Proposition : 2=3         | Prop/ Type
Predicate on A:Type       | P: A->Type/Prop
foralla.A (P a)           | forall a Pa should be a type
*)