(*Proof by reflection *)

Inductive Even : nat -> Prop :=
| Even0 : Even 0
| EvenSSn : forall {n}, Even n -> Even (S(S n )).

Goal Even 2.
exact (EvenSSn Even0).
Qed.

Lemma even200 : Even 200 .
repeat constructor.
Qed.

Require Arith.

(* Goal forall (x y : nat), (x+y)*(x+y) = x*x + 2*x*y + y*y.

intros; ring. *)

Fixpoint evenb (n:nat) : bool :=
match n with
| O => true
| S m => negb(evenb m)
end.

Fixpoint evenB (n : nat) : {Even n} + {True} :=
match n with
| O => left Even0
| S (S m) => match evenB m with
             | left pf => left (EvenSSn pf)
             | _ => right I end
| _ => right I
end.

Definition recover {P Q: Prop} (x : {P}+{Q} ) : match x with
                                                 | left _ => P
                                                 | right _ => Q
                                                 end 
                                              := match x with 
                                                 | left p => p
                                                 | right q => q
                                                 end.

Goal Even 200.
apply (recover (evenB 200)).
Qed.

Goal Even 2000.
exact (recover (evenB 2000)).
Show Proof.
Qed.

(* Lemma evenbCorrect : forall n, evenb n = true -> Even n.
intro.
induction n.
- intro. exact Even0.
- intro. apply IHn. *)


(* Write a tactic to handle True /\ (True \/ True)
 *)
(* 
Ltac taut := match goal with
          | [ |- True ] => exact I.
          | [ |- A /\ B] => constructor.
          | [ |- A \/ B ] 

also we can use repeat
*)


(* Reify *)

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
- simpl. exact (or_introl IHt1 ).
Qed.

(* Definition my_prop  = True  *)

