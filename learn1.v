Theorem syllogism : forall P Q: Prop, (P -> Q) -> P -> Q.
intros P Q PempQ evP.
apply PempQ.
assumption.
Qed.


Theorem imp_trans : forall P Q R: Prop, (P->Q) -> (Q->R) -> (P -> R).
intros P Q R PempQ QempR evP.
apply QempR.
apply PempQ.
assumption.
Qed.

Theorem and_fst : forall P Q, P /\ Q -> P.
intros P Q PandQ.
destruct PandQ as [evP evQ].
assumption.
Qed.


Definition and_last : forall P Q, P /\ Q -> Q := fun (P Q: Prop) (PandQ : P /\ Q) => match PandQ with 
                                                                                  | conj _ evQ => evQ
                                                                                  end.


Theorem and_comm: forall P Q, P /\ Q -> Q /\ P.
Proof.
intros P Q PandQ.
destruct PandQ as [p_holds q_holds].
split.
all: assumption.
Qed.

Definition and_flip : forall P Q, (P /\ Q) -> (Q /\ P) := fun (P Q : Prop) (PandQ : P /\ Q) => match PandQ with
                                                                                       | conj evP evQ => (conj evQ evP)
                                                                                        end.


Theorem and_to_imp : forall P Q R : Prop, (P /\ Q -> R) -> (P -> (Q -> R)).
Proof.
intros P Q R PandQimpR.
intros evP evQ.
apply PandQimpR.
split.
all: assumption.
Qed.

Definition and_to_imp1 : forall P Q R : Prop, (P /\ Q -> R) -> (P -> (Q -> R)) :=
                                                            fun (P Q R : Prop) (PandQempR : P /\ Q -> R) => 
                                                                              fun (evP : P) (evQ : Q) => PandQempR (conj evP evQ).


(*
Disjunction
*)

Theorem or_left : forall (P Q : Prop), P -> P \/ Q.
Proof.
intros P Q evP.
left.
assumption.
Qed.

Print or_left.


Definition or_left1: forall (P Q : Prop), P -> P \/ Q := fun (P Q: Prop) (evP : P) => or_introl evP.

Print or_introl.


Theorem or_thm : 3110 = 3110 \/ 2110 = 3110.
Proof.
left.
trivial.
Qed.


Theorem or_comm : forall P Q, P \/ Q -> Q \/ P.

Proof.
intros P Q evPandQ.
destruct evPandQ as [P_holds|Q_holds].
- right. assumption.
- left. assumption.
Qed.

Definition or_comm_def :  forall P Q, P \/ Q -> Q \/ P := fun (P Q: Prop) (evPandQ: P \/ Q) =>
                                                                            match evPandQ with 
                                                                            | or_introl evP => or_intror evP
                                                                            | or_intror evQ => or_introl evQ
end.

Check or_comm_def.


Theorem or_distr_and : forall P Q R,
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
    intros P Q R PorQandR.
    destruct PorQandR as [evP | QandR].
    - split.
    + left. assumption.
    + left. assumption.
    - destruct QandR as [evQ evR].
      split.
      + right. assumption.
      + right. assumption.
Qed.

(* False
 *)

Theorem explosion : forall P:Prop, False -> P.
Proof.
intros P false_holds.
contradiction.
Qed.


Theorem p_imp_p_or_false : forall P:Prop, P -> P \/ False.
Proof.
intros P evP.
left.
assumption.
Qed.


(* True
 *)

Theorem p_imp_p_and_true : forall P:Prop, P -> P /\ True.
Proof.
intros P evP.
split.
assumption.
exact I.
Qed.

Theorem p_imp_p_or_true : forall P:Prop, P -> P \/ True.
Proof.
intros P evP.
right. trivial.
Qed.

Theorem notFalse : ~False -> True.
unfold not.
intros.
exact I .
Qed.

Print notFalse.

Theorem falseImpTrue : False->True.
Proof.
intros.
exact I.
Qed.

Theorem notTrue: ~True -> False.
Proof.

unfold not.
intros TrueImpFalse.
apply TrueImpFalse.
exact I.
Qed.

Theorem contra_implies_anything : forall P Q, P /\ ~P -> Q.
unfold not.
intros P Q PandnotP.
destruct PandnotP as [evP evNotP].
contradiction.
Qed.


Theorem deMorgan : forall P Q : Prop,
  ~(P \/ Q) -> ~P /\ ~Q.
unfold not.
intros P Q notPorQ.
split.
- intros P_holds. apply notPorQ. left. assumption.
- intros Q_holds. apply notPorQ. right. assumption.
Qed.

Print deMorgan.

Definition deMorgan1 : forall P Q: Prop,   ~(P \/ Q) -> ~P /\ ~Q := fun (P Q: Prop) (notPorQ : P \/ Q -> False ) =>
                                                                                     conj (fun (P_holds : P) => (notPorQ (or_introl P_holds))) 
                                                                                          (fun (Q_holds : Q) => (notPorQ (or_intror Q_holds))).


