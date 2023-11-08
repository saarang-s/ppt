Require Import Coq.Lists.List.

Hypothesis A: Type.
Hypothesis op : A -> A -> A.
Hypothesis assoc : forall x y z : A, op x (op y z) = op (op x y ) z.

Hypothesis e : A.

Hypothesis right_id : forall x:A, op x e  = x.
Hypothesis left_id : forall x:A, op e x  = x.

Inductive MExp := 
      | MID : MExp 
      | MMul : MExp -> MExp -> MExp 
      | MVar : A -> MExp.

Fixpoint denoteMExp (me : MExp ) : A := 
match me with
| MID => e
| MMul me1 me2 => op (denoteMExp me1) (denoteMExp me2)
| MVar a => a
end.

Fixpoint flatten (me : MExp) : list A :=
match me with 
| MID => nil (* couldn't write [] *)
| MMul me1 me2 => (flatten me1) ++ (flatten me2)
| MVar a => cons a nil (* couldn't write [ a ] *)
end.

Print nil .

Fixpoint listDenote (l:list A) : A := 
match l with
| nil => e
| cons a xs => op a (listDenote xs)
end.

Axiom x : A.
Axiom y : A.
Axiom z : A.


Ltac reify M := 
              match M with 
              | e => constr : (MID)
              | op ?M1 ?M2 => let m1 := reify M1 in
                            let m2 := reify M2 in 
                            constr : (MMul m1 m2)
              | ?X => constr : (MVar X)
              end.


Ltac reifyH M := let m := reify M in exact m.

Definition foo : MExp := ltac : (  reifyH (op x (op y z)) ).

Print foo.

(* Lemma listc : forall l1 l2, listDenote (l1 ++ l2) = op (listDenote l1) (listDenote l2).
intros.
induction l1.
- simpl. *)


Lemma flatten_lemma : forall me : MExp, denoteMExp me = listDenote (flatten me).
intros.
simpl.
induction me.
- simpl. trivial. 
- simpl. 

Ltac crush_eq m1 m2 :=
                      let ml := reify m1 in 
                      let mr := reify m2 in
                      let H := fresh "H" in
                      assert  (denoteMExp ml = denoteMExp mr)
                      by (repeat rewrite flatten_lemma, simpl, trivial)
                      assumption.


Ltac crush := match goal with 
              | [ |- ?L = ?R]
                 => crush_eq L R
              end.


(* If we want to prove m1 = m2
                       |     |
                      \/     \/
                      ml1   ml2
then prove if 
 *)



(* listDenote (l:list A) :A
complete this (this can be done with foldl or foldr)
and the reify part
*)