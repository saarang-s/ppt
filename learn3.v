Lemma not_false : not False.
unfold not.
intros.
assumption.
 Qed.

Lemma not_not_A : forall (A: Prop),A-> not (not A).
intros A.
intros p_A.
unfold not.
intros.
apply H.
assumption.
Qed.


(* Demorgans Law 
- not (A) \/ not (B) -> not (A /\ B)
- not (A) /\ not (B) -> not (A \/ B)
- not (A \/ B) -> not (A) /\ not (B)
- not (A /\ B) -> not (A) \/ not (B)
*)


Theorem dm1 : forall (A B: Prop), not (A) \/ not (B) -> not (A /\ B).
Proof.
intros.
unfold not.
intros.
destruct H0 as [pA pB].
destruct H as [nA | nB].
- unfold not. contradiction.
- contradiction.
Qed.


Theorem dm2 : forall (A B : Prop), not (A) /\ not (B) -> not (A \/ B).
unfold not.
intros.
destruct H as [h1 h2].
destruct H0 as [h01 | h02].
- apply h1. exact h01.
- apply h2. exact h02.
Qed.


Theorem dm3 : forall (A B: Prop), not (A \/ B) -> not (A) /\ not (B).
Proof.
unfold not.
intros.
split.
intros.
apply H.
exact (or_introl H0).
intros.
apply H.
exact (or_intror H0).
Qed.

Definition dd1 :  forall (A B: Prop), not (A) \/ not (B) -> not (A /\ B) := 
                                                    fun (A B: Prop) (nAornB:  (not (A) \/ not (B)) ) => 
                                                                     match nAornB with 
                                                                     | or_introl nA => fun (AaB : A /\ B) => 
                                                                                      match AaB with 
                                                                                      | conj pA pB => nA pA
                                                                                      end
                                                                     | or_intror nB => fun (AaB : A /\ B) => 
                                                                                      match AaB with 
                                                                                      | conj pA pB => nB pB end
end.


Definition dd2 :  forall (A B: Prop), not (A) /\ not (B) -> not (A \/ B) :=
                                      fun (A B: Prop) (nAanB :  not (A) /\ not (B)) => 
                                                    match nAanB with 
                                                    | conj nA nB => fun (AoB : A \/ B) => 
                                                                    match AoB with 
                                                                    | or_introl pA => nA pA 
                                                                    | or_intror pB => nB pB end
end.

Definition dd3 : forall (A B : Prop), not (A \/ B) -> not (A) /\ not (B) := fun (A B: Prop ) (nAoB: not (A \/ B)) =>
                                                                            conj (fun (pA : A) => nAoB (or_introl pA) )
                                                                                 (fun (pB : B) => nAoB (or_intror pB) ).

(* Definition dd4 : forall (A B : Prop), not (A /\ B) -> not (A) \/ not (B) := 
*)


Inductive and (A B: Prop): Prop := conj.


