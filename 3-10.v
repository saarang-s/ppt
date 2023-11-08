Require Import List.
Import ListNotations.


Inductive exp : Type := 
  | Const : nat -> exp
  | binOp : op->exp->exp->exp
with op :=
  | PLUS : op
  | TIMES : op .

Definition opDenote (o: op) : nat -> nat -> nat :=
  match o with 
  | PLUS => Nat.add
  | TIMES => Nat.mul
  end.

(* 
Fixpoint expDenote (x: exp) : nat := 
  match x with 
  | Const n => n
  | binOp PLUS a b => (expDenote (a)) + (expDenote (b))
  | binOp TIMES a b => (expDenote (a)) * (expDenote (b))
end.
 *)

Fixpoint expDenote (x: exp) : nat := 
  match x with 
  | Const n => n
  | binOp o n1 n2 => let v1 := expDenote (n1) in
                     let v2 := expDenote (n2) in
                          (opDenote o) v1 v2
end.

Compute expDenote (binOp PLUS (Const(45)) (Const(60)) ).

Variant inst : Type :=
| Push : nat -> inst
| Exec : op -> inst
.

Definition stack := list nat.

(* instDenote : inst -> stack -> option stack. *)

Definition instDenote (i : inst) (s : stack) : option stack := 
  match i with 
  | Push n => Some (n::s)
  | Exec PLUS => match s with 
                 | x1::x2::x => Some ((x1+x2)::x)
                 | _ => None end
  | Exec TIMES => match s with 
                  | x1::x2::x => Some ((x1*x2)::x)
                  | _ => None end
end.


(* Definition instDenote (i : inst) (s : stack ) : option stack :=
  match i,s with 
  | Push n, st => Some (n::st)
  | *)

Definition instDenoteP (s : option stack) (i : inst) : option stack :=
  match s with 
  | Some (a) => instDenote i a
  | _ => None
end.


Definition program := list inst.
Definition programDenote (p: program) (st : stack) : option stack :=
  List.fold_left instDenoteP p (Some st).


Fixpoint compile  (e: exp) : program := 
  match e with 
  | Const n => [Push n]
  | binOp op n1 n2 => (compile n2) ++ ((compile n1) ++ [Exec op])
end.


Lemma correctness : forall e, programDenote (compile e) [] = Some [expDenote e].
  intro e.
  induction e.
  - simpl. trivial.
  - destruct o; simpl.
Abort.

Lemma correctnessP : forall e st, programDenote (compile e) st = Some (expDenote e :: st).
intros e.
induction e.
- intro st; compute; trivial.
- intro st. destruct o. simpl.
Abort.


Lemma correctnessPP : forall e p st, programDenote (compile e ++ p) st = programDenote p (expDenote e ::st).
  intro e.
  induction e.
  - intros. simpl. trivial.
  - intros P st; simpl; destruct o; simpl;
(*     Search (_ ++ _ = _)%list.
(* *)
app_assoc: forall [A : Type] (l m n : list A), l ++ m ++ n = (l ++ m) ++ n
app_inv_head: forall [A : Type] (l l1 l2 : list A), l ++ l1 = l ++ l2 -> l1 = l2
app_inv_tail: forall [A : Type] (l l1 l2 : list A), l1 ++ l = l2 ++ l -> l1 = l2
app_assoc_reverse: forall [A : Type] (l m n : list A), (l ++ m) ++ n = l ++ m ++ n
*)
  repeat rewrite app_assoc_reverse; rewrite IHe2; rewrite IHe1;
  simpl; trivial.
Qed.



