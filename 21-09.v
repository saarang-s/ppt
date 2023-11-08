(* Red Black Tree 
Mad "bad" values unrepresentable
*)

Require Import Arith.

(* Inductive exp : Type -> Type :=
| const {T}: T -> exp T
| PLUS : exp nat -> exp nat -> exp nat
| GT : exp nat -> exp nat -> exp bool
| IF {T} : exp bool -> exp T -> exp T -> exp T. *)


(* Search (nat -> nat -> bool) 
you can search like this to get all the functions of this type
. *)

(* 
Variant bool := true 
                | false. *)


(* Fixpoint denote : forall T, exp T -> T := fun (T : Type) (e : exp T) =>
                                                                      match e with 
                                                                     | const a => a
                                                                     | PLUS (const n1) (const n2) => plus n1 n2
                                                                     | GT (const n1) (const n2) => (n2  <? n1)
                                                                     | IF (const true) (x) (_) => x 
                                                                     | IF (const false) (_) (y) => y
                                                                     end . *)
(* Complete this

Fixpoint denote : (T :Type) (e : exp T) :=  match e with 
                                           | const a => a
                                           | PLUS (const n1) (const n2) => plus n1 n2
                                           | GT (const n1) (const n2) => (n2  <? n1)
                                           | IF (const true) (x) (_) => denote T x
                                           | IF (const false) (_) (y) => denote T y
                                           end . *)


(* A small compiler *)

Inductive exp : Type := 
  | Const : nat -> exp
  | binOp : op->exp->exp->exp
with op :=
  | PLUS : op
  | MINUS : op .


Variant inst : Type :=
| Push : nat -> inst
| Exec : op -> inst
.

Definition program := list inst.

Require Import List.
Import ListNotations.

(*
Variant option {A : Type} : Type := 
| Some : A -> option
| None : option.
*)

Fixpoint expDenote (x: exp) : nat := match x with 
                                                    | Const n => n
                                                    | binOp PLUS a b => (expDenote (a)) + (expDenote (b))
                                                    | binOp MINUS a b => (expDenote (a)) - (expDenote (b))
                                                    end.


Definition stack := list nat.  (*Can be wrong*) (*Nah, never wrong*)

(* instDenote : inst -> stack -> option stack. *)

Definition instDenote (i : inst) (s : stack) : option stack := match i with 
                                                               | Push n => Some (n::s)
                                                               | Exec PLUS => match s with 
                                                                           | x1::x2::x => Some ((x1+x2)::x)
                                                                           | _ => None end
                                                               | Exec MINUS => match s with 
                                                                           | x1::x2::x => Some ((x1-x2)::x)
                                                                           | _ => None end
                                                               end.




Fixpoint foldl (f : inst -> stack -> option stack) (acc : option stack) (lst : list inst) : option stack :=
  match lst with
  | [] => acc
  | x :: xs => match acc with 
               | Some a => foldl f (f x a) xs
               | None => None
               end
  end.

Definition programDenote (p : program ) : option stack := foldl instDenote (Some nil) p .


(* programDenote : program -> stack -> option stack  *)

(* Theorem correctness : forall e:exp, programDenote (compile e) [] = Some [denote e]. *)

(* compile : exp -> program*)

(* once you have instruction denote, we can use fold for programDenote (foldleft) *)

(* Definition compileHelp (e: exp) (p : program): program := match e with 
                                                         | Const n => (Push n) :: p
                                                         | binOp op n1 n2 => (compileHelp ) *)

Fixpoint compile  (e: exp) : program := match e with 
                                        | Const n => [Push n]
                                        | binOp op n1 n2 => (compile n1) ++ (compile n2) ++ ((Exec op)::nil)
                                        end.

Definition e := binOp (PLUS) (Const 2) (Const 3).

Definition a := compile ( e).
Compute a.


