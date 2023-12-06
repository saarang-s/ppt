(* 
* Galina is the programing language we used 
* Tactic language is powerful tool 
* Tactic is a way to generate code 
* 
*)

(*
The below may not work when you try to use intro_induct then,
if any variable named H is already present it may be overwritten
*)

(* Ltac intro_induct H:= intro H; induction H. *)

(* 
|- : This sign is called turnstile
*)


Ltac intro_induct := let H := fresh "H" in 
                     intro H; induction H.

Ltac Known := match goal with 
| [H:?G |-?G ] => exact H
end.


Locate "exact".

Goal forall A: Prop, A -> A .
intros.
Known.
Qed.

Goal forall A B: Prop, A -> B -> A.
intros.
Known.
Qed.



Ltac induct_nat := match goal with 
                  | [  |- nat-> _] => let n := fresh "n" in 
                                       intro n; induction n
                  end.

(* The match in Ltac is back tracking match.  *)
(*---------------adding-compiler-code-for-demonstration-----*)
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

#[local] Hint Rewrite app_assoc_reverse : compiler.

Ltac crush :=  repeat (simpl; trivial; 
              match goal with
              | [ |- exp -> _ ] => let e := fresh "e" in 
                                    intro e; induction e
              | [ |- program -> _ ] => let p:= fresh "p" in 
                                       intro p
              | [ |- list inst -> _ ] => let p:= fresh "p" in 
                                       intro p
              | [ |- stack -> _ ] => let s := fresh "s" in
                                        intro s
              | [H : _ |- _ ] => try rewrite H
              | _ => autorewrite with compile
              end).

Lemma correctnessPP : forall e p st, programDenote (compile e ++ p) st = programDenote p (expDenote e ::st).
(*crush.*)
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

(* Lemma correctnessPP1 : forall e p st, programDenote (compile e ++ p) st = programDenote p (expDenote e ::st).
crush. *)

