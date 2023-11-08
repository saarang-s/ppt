Variant bool: Set := 
| true :bool
| false : bool.

Fixpoint eqb ( x y : nat) :bool :=
match x,y with
| O,O => true
| S m, S n => eqb m n
| _ , _ => false
end . (* There is only verbal confirmation that this function is correct*)

Print sumbool.

Variant prod (A B : Type) : Type :=
| pair : A -> B -> prod A B.


Variant and (A B: Prop) : Prop :=
| conj : A -> B -> and A B.

(* Variant sumbool { A B : Prop} : Set :=
| left : A -> @sumbool A B
| right : B -> @sumbool A B. *)

(* When we extract ocaml or haskell code out of coq 
all objects of type Prop are removed. So in a function that computationaly 
find a value using a prop cannot be extracted.
Eg: match x
| or_introl pfA = 0
| or_intror pfB = 1
*)

Definition abort {A} (pf : False ) : A :=
  match pf with 
  end.

Definition foo {A B} (x : @sumbool A B ): nat:=
match x with 
| left pfA => 0
| right pfB => 1
end.

(*Definition eq_dec (x y: nat) : { x=y } + { x<>y }.*) (* If such a function exist, 
then it is correct. Such a function exists show the decidability of equality of
natural numbers
dec = decidability *)

Definition Dec ( P: Prop ) := {P} + {not P}.

Lemma zNESn : forall n, O <> S n. 
intro n.
intro Hzesn.
inversion Hzesn.
Qed.

(* You can use inversion when we have to prove false but we don't know what to use
 *)

(* 
Destruct 
Induct 
Inversion
*)

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