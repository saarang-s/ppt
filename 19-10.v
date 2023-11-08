Require Import List.
Import ListNotations.
Print sumbool. (*left , right*)
Print or. (* or_introl, or_intor *)
Print sum. (* inl, inr *)

(*Sumor*)
Print sumor.  (*inleft, inright *)

(* Variant sumor (A : Type) (B:Type): Type :=
| inleft : A -> sumor A B
| inright : B -> sumor A B. *)

(* eqdec gives the proof that x and y are same, but eqb doesn't
Similarly
`hd : forall {A}, list A -> option A.`
also isn't guaranteed to give the head or an element of the list

hd : forall {A} (l:list A), A + {l=[]}

hd_nat : forall (l: list nat), nat+{l=[]}
*)

Definition hd  {A} ( l : list A): A + {l = nil} .
refine ( match l with 
        | y::ys => inleft y
        | nil => inright _ 
        end ).
trivial.
Defined.

(* lia *)

Definition map {A B E} (f : A -> B) (OA : A + {E}) : B + {E} := 
match OA with
| inleft a => inleft (f a)
| inright e => inright e
end.

About map.
About app.
Print app.

Definition app : forall A B E, A -> B + {E} -> A + {E} -> B+ {E} := 

