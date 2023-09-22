(* Last class you had to learn the idea of indexes and parameters
 *)
(* vector : Type -> nat -> Type. *)

Inductive vector (A : Type) : nat -> Type :=
| nill : vector A 0
| cons : A -> forall n : nat, vector A n -> vector A (S n).


(* nil : forall A : Type, Vector A O 

cons; forall A:Type, A -> forall n : nat, Vector A n -> Vector A (S n)
 *)


Arguments nil {A}.
Arguments cons {A} _ {n}.

Check cons.
Check nil.

(* 
Check cons.
Check nil. *)

(* Definition head {A} {n} (v : vector A (S n)) : A :=
match v with 
| cons1 _ vector _ S(n')  => n'
end
. *)
(* Argument nil {A}
Argument cons {A} _ {n}
 *)


Definition hd {A n} (v : vector A (S n)) : A :=
          match v with 
          | cons x _ => x
          end. 


Check hd.
(* Arbitrary fix point calculation is not allowed, because it can give the proof of  False
Eg: The fix point of True gives False or somehitng. Verify it .
*)

(* match v in vector _ n0  retrun match n0 with 
                                | O => IDProp
                                | S _ => A
                                end. *)

(* 
Complete / Correct it

Definition hd' {A} n (v : vector A n) : match n with 
                                    | O => IDProp
                                    | S _ => A
                                    end
                                    :=
                                              match v in vector _ n0 return 
                                                                            match n0 with 
                                                                            | O => IDProp
                                                                            | S _ => A
                                                                            end.
 *)

(* 
ALso deal with it
Definition hd'' {A n} (v: vector A (S n)) = hd (S n) v *)


(*Red Black Tree


(1) Binary tree iwth nodes of two colors red and black.
(2) ALl the childre of a red node should be black.
(3) The black height of any node should be same.
    # Black node encountered an
      a path from n to any leaf node is fixed } the black height of n
*)

Inductive Color := 
            | R : Color
            | B : Color.

Inductive tree (A : Type) : Color -> nat -> Type :=
| nil : tree A B 0
| red : forall n:nat, tree A B n -> tree A B n -> tree A R n 
| black : forall n c1 c2, tree A c1 n -> tree A c2 n -> tree A B (S n).


(*This black and red constructor can be written differently
*)
(* 
Inductive tree2 (A : Type) : Color -> nat -> Type :=
| nil2 : tree2 A B 0
| red2 : forall n:nat, tree2 A B n -> tree2 A B n -> tree2 A R n 
| black2 n c1 c2 :  tree2 A c1 n -> tree2 A c2 n -> tree2 A B (S n).


You can also make n c1 c2, as implicit arguments

Inductive tree2 (A : Type) : Color -> nat -> Type :=
| nil2 : tree2 A B 0
| red2 : forall n:nat, tree2 A B n -> tree2 A B n -> tree2 A R n 
| black2 {n c1 c2} :  tree2 A c1 n -> tree2 A c2 n -> tree2 A B (S n).
*)

Argument tree : clear implicits.

