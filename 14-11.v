Require Import List.
Import ListNotations.
Section Hlist .

Context {sort : Type}.

Inductive hlist {A:sort -> Type } : list sort -> Type :=
| hnil : hlist []
| hcons {s:sort} : A s -> forall {l}, hlist l -> hlist (s::l).

End Hlist.
Arguments hlist {sort} A.
Arguments hcons {sort A s} _ {l}.


Check (hnil).
(* Definition hd : forall sort ( A : sort -> Type ) ( s : sort) (l : list sort) , 
hlist (s :: l) -> A s.
 *)
(* Definition tails : forall sort (A : sort -> Type ) (s : sort) (l :list sort),
hlist (s ::l ) -> hlist A l. *)

Definition hd  {sort} { A : sort->Type } { s : sort } { l : list sort } ( hl: hlist A (s::l) ) : A s := 
match hl with
| hcons x _ => x
end. 


Definition tail {sort} {A : sort -> Type} {s : sort} {l : list sort} (hl : hlist _ (s :: l) ): hlist A l :=
match hl with
| hcons _ x => x
end.


(* Type of 0th element is A (S0) or A (0th element)
 *)
 
(* Indexing Hlist *)

Section Hlist .
Context {sort : Type }.
Inductive member : sort -> list sort -> Type := (* A membership proof of a set *)
| here {s : sort} {l : list sort} : member s ( s :: l)
| there { s : sort } { l : list sort } : member s l -> forall {s'}, member s (s' ::l ).
End Hlist.

(* Arguments hlist {sort} A. *)

Goal member 2 [3;4;2;5].
(* exact (there (there (here) ) ). *)

repeat constructor.
Show Proof.
Qed.

Fixpoint get  {sort} {s:sort} {l : list sort} (mp: member s l) {A} : ( hlist A l) -> A s:= 
(* match mp in member s0 l0 return hlist A l0 -> A s0 *)

match mp with
| here => fun hl =>  hd hl
| there mpp => fun hl => get mpp (tail hl)
end.

Fixpoint put {sort: Type } {s : sort} {l} { A } (mp : member s l) :  A s ->  hlist A l -> hlist A l :=
match mp with
| here => fun a hl => hcons a (tail hl)
| there mpp => fun a hl => hcons (hd hl) (put mpp a (tail hl))
end.

(* Functional representation of hlist
 *)
(* fhlist A h = forll s, member s l -> A s. *)

(* Fixpoint all {sort : Type } (l : list sort) : (hlist (fun s => member s l) l) := 
match l with
| [] => hnil
| x::[] => hcons here hnil
| x::ls => let c := all ls in
            hcons there (hd c) hd
            end. *)
            
Fixpoint map  s A B l :  (A s -> B s) -> hlist A l -> hlist B l :=
fun m hl => 
match hl with
| hnil => hnil 
| hcons a hls => hcons (m a) (map m hls)
end.

            
Fixpoint all l :=
match l with
| [] => hnil 
| (s :: lp ) => hcons here ()