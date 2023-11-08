(* Require Import Coq.Lists.List. *)
(* Require Import List. *)
Require Import List.
Import ListNotations.
Require Import String.



(* Vector 
Inductive Vector (A:Type) : nat -> Type
  | nil : Vector A O
  | cons : A -> forall n, Vector A n -> Vector A (S n)

 *)

(* H List Hetrogeneous List
Section 
Context {Sort : Type}
 
*)
Set universe polymorphism.
(* Check sort. *)
Section hlist.
Context {sort : Type}.

Inductive hlist (A : sort -> Type) : list sort -> Type :=
| hnil : hlist A nil
| hcons {s} : A s -> forall l : list sort, hlist A l -> hlist A (s::l).

Arguments hnil {A}.
Arguments hcons {A s} _ {l}.
End hlist.

(* Write the head and tail function *)

Section Foo.
Context (n : nat).
Definition foo : nat := S n.
Check foo.
End Foo.

Check foo.
Check "jo"%string.
(* Check (hcons 2 ( hcons "hello"%string ( hcons true nil)) : (hlist (fun t=>t ) [nat; string; bool]) ). *)

(* hd : forall n, Vector A (S n) -> A
 *)

(* Type of 
hd : forall sort, forall A : sort -> type, forall s : sort, hlist A (s::l) -> A s 
tail : forall sort, forall A : sort -> type, forall s : sort, hlist A (s::l) -> A l
*)

Definition hd {sort: Type} {A : sort} (l : list sort) (lst : hlist A l) : A s := match lst with
                                                      | hcons x => x
                                                      | hnil => nil end.
