(* Proof by reflection example *)
(* phi = True 
| phi1 /\ phi2
| phi1 \/ phi2
 *)

(*Reify is the opposite of abstraction*)

(* Stage I capture the Ast w a type  ...
*)

Inductive taut := 
              | TautTrue : taut
              | TautAnd :  taut -> taut -> taut
              | TautOr : taut -> taut -> taut.

(*Stage II give semantics *)

Fixpoint tautDenote (t : taut) : Prop := 
match t with 
| TautTrue => True
| TautAnd t1 t2 => (tautDenote t1) /\ (tautDenote t2) 
| TautOr t1 t2 => (tautDenote t1) \/ (tautDenote t2) end.

Lemma tautTruth : forall t, tautDenote t.
intros.
induction t.
- simpl. trivial.
- simpl. exact (conj (IHt1) (IHt2)) .
- simpl. exact (or_introl (IHt1) ) .
Qed.

Ltac reify phi := match phi with 
| ?P /\ ?Q => let pr := reify P in 
              let qr := reify Q in 
              constr : (TautAnd pr qr) 
| ?P \/ ?Q => let pr := reify P in 
              let qr := reify Q in
              constr : (TautOr pr qr)
| True => TautTrue
end.
Ltac tautCrush  := match goal with 
               | [ |- ?phi ] => let phir := reify phi in 
                                exact (tautTruth phir ) end.

Goal True/\(True \/ True) .
tautCrush.
Qed.


(*Monoid is a Set A together with a binary operation '.' : A->A->A*)

(*
(1) Associativity => x.(y.z) = (x.y) .z   
(2) Existence of identity => x.e = x

*)


(*We first need to normalize MExp to some suitable format. The one suitable way
is to represent it in a left bracketed form or convert it to a simple list
normalization : MExp -> list A*)

(*  

*)

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

(* listDenote (l:list A) :A
complete this (this can be done with foldl or foldr)
and the reify part
*)