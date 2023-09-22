(*

Definition dM1 A B (nAonB: (not (A) \/ not (B)) ) : not (A) /\ not (B)
                              := fun (aAb : A /\ B) => match nAonB with 
                                                       | or_introl nA => _
                                                       | or_introl nB => _
                                                        end. *)
(*
not A  \/ not B -> not (A /\ B)
not A /\ not B -> not (A \/ B)
not (A \/ B) -> not A /\ not B
not (A /\ B) -> not A \/ not B
*)


(*
Definition dM1 A B (nAonB: ( or (not A)  (not B))) : (and (not A) (not B)) :=
  fun (aAb : A /\ B) => match nAonB with
                        | or_introl nA => match aAb with
                                          | conj a b => conj nA b
                                          end
                        | or_intror nB => match aAb with
                                          | conj a b => conj a nB
                                          end
                        end.

*)

Definition dM1 : forall A B: Prop,  ((not A) \/ (not B)) -> (not (A /\ B)) := 
                                            fun (A B: Prop) (nAoNB: ((not A) \/ (not B))) 
                                                          => match nAoNB with 
                                                             | or_introl nA => fun (AaB: (A /\ B)) => match AaB with 
                                                                                                     | conj pA pB => nA pA
                                                                                                      end
                                                             | or_intror nB => fun (AaB: (A /\ B)) => match AaB with 
                                                                                                     | conj pA pB => nB pB
                                                                                                      end
end.

Theorem dM1T : forall A B: Prop,  ((not A) \/ (not B)) -> (not (A /\ B)).
unfold not.
intros A B nAornB.
intros AoB.
destruct AoB as [pA pB].
destruct nAornB as [nA | nB].
- apply nA. assumption.
- apply nB. assumption.
Qed.



Definition dM2 : forall A B: Prop, (not(A)  /\ not(B)) -> not ( A \/ B) := fun (A B: Prop) (nAandnB: (not(A)  /\ not(B))) => 
                                                                            match nAandnB with 
                                                                            | conj nA nB => fun ( AorB: A \/ B ) => 
                                                                                                    match AorB with
                                                                                                    | or_introl pA => (nA pA)
                                                                                                    | or_intror pB => (nB pB)
                                                                                                     end
end.

Theorem dM2T : forall A B: Prop, (not(A)  /\ not(B)) -> not ( A \/ B).
unfold not.
intros A B nAanB.
destruct nAanB as [nA nB].
intros AorB.
destruct AorB as [pA | pB].
- apply nA. assumption.
- apply nB. assumption.
Qed.


Definition dM3 : forall A B: Prop, (not (A \/ B)) -> ((not A) /\ (not B)) := fun (A B: Prop) (notAoB: not (A \/ B)) =>
                                                                              conj (fun (pA : A) => (notAoB (or_introl pA)) )
                                                                                     (fun (pB : B) => (notAoB (or_intror pB)) ).


Theorem dM3T : forall A B: Prop, (not (A \/ B)) -> ((not A) /\ (not B)).
unfold not.
intros A B nAoB.
split.
intros pA.
apply nAoB.
left. assumption.
intros pB.
apply nAoB. right. assumption.
Qed.



Definition dM2_class A B (nAanB: (not  A) /\ (not B)) : not ( or A B )
                                            := fun (aob : A \/ B) 
                                            => match aob with 
                                               | or_introl a => match nAanB with 
                                                                | conj nA nB => nA a end
                                               | or_intror b => match nAanB with 
                                                                | conj nA nB => nB b end
                                                end.

(*
Definition dM1 A B (nAonB: (or (not A)  (not B)) ) :  (not A) /\ (not B) :=
  fun (aAb : A /\ B) => match nAonB with
                        | or_introl nA => match aAb with
                                          | conj a b => conj nA b
                                          end
                        | or_intror nB => match aAb with
                                          | conj a b => conj a nB
                                          end
                        end. *)

(*Natural numbers inductive definition*)

Inductive nat : Set :=
        | O : nat
        | S : nat -> nat.


Definition isZero (n: nat ): bool :=
      match n with 
      | O => true
      | _ => false
end.


Compute (isZero O).


(*Fix point is used when defining the recursive functions (as of now think like that)*)

Fixpoint plus (m n :nat):nat :=
    match m with 
    | O => n
    | S mp => S ( plus mp n)
    end.

(*What essentially happens is we create a function whose fix point is plus, 
then we find its fix point *)

Definition F (f : nat->nat->nat) : nat -> nat -> nat :=
    fun (m n :nat) => match m with 
                       | O => n
                       | S mp => S (f  mp n )
                      end.

Definition F_t : (nat->nat->nat) -> nat -> nat -> nat := fun (f : nat -> nat -> nat) m n => match m with 
                                                                                            | O => n 
                                                                                            | S mp => S ((f mp) n) 
 end.

Check F.
(*
Predicates on type are functions from that type to prop
*)

